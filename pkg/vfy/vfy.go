// +gobra
package vfy

import (
	"context"
	"errors"
	"fmt"
	"log"
	"strings"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/ident"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/adem-wg/adem-proto/pkg/util"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

type VerificationResults struct {
	results    []consts.VerificationResult
	protected  []*ident.AI
	issuer     string
	endorsedBy []string
}

func ResultInvalid() VerificationResults {
	return VerificationResults{results: []consts.VerificationResult{consts.INVALID}}
}

func (res VerificationResults) Print() {
	lns := []string{"Verified set of tokens. Results:"}
	resultsStrs := make([]string, 0, len(res.results))
	for _, r := range res.results {
		resultsStrs = append( /*@ perm(1/2), @*/ resultsStrs, r.String())
	}
	lns = append( /*@ perm(1/2), @*/ lns, fmt.Sprintf("- Security levels:    %s", strings.Join(resultsStrs, ", ")))
	if len(res.protected) > 0 {
		assets := make([]string, 0, len(res.protected))
		for _, ass := range res.protected {
			assets = append( /*@ perm(1/2), @*/ assets, ass.String())
		}
		lns = append( /*@ perm(1/2), @*/ lns, fmt.Sprintf("- Protected assets:   %s", strings.Join(assets, ", ")))
	}
	if res.issuer != "" {
		lns = append( /*@ perm(1/2), @*/ lns, fmt.Sprintf("- Issuer of emblem:   %s", res.issuer))
	}
	if len(res.endorsedBy) > 0 {
		lns = append( /*@ perm(1/2), @*/ lns, fmt.Sprintf("- Issuer endorsed by: %s", strings.Join(res.endorsedBy, ", ")))
	}
	log.Print(strings.Join(lns, "\n"))
}

var ErrTokenNonCompact = errors.New("token is not in compact serialization")

type TokenVerificationResult struct {
	token *ADEMToken
	err   error
}

// Verify an ADEM token's signature. Designed to be called asynchronously.
// Results will be returned to the [results] channel. Verification keys will be
// obtained from [km].
// Every call to [vfyToken] will write to [results] exactly once.
func vfyToken(rawToken []byte, km *keyManager, results chan *TokenVerificationResult) {
	result /*@@@*/ := TokenVerificationResult{}
	defer doSend(results, &result)

	jwtT, err := jwt.Parse(rawToken, jwt.WithKeyProvider(km))
	if err != nil {
		result.err = err
		return
	}

	if msg, err := jws.Parse(rawToken); err != nil {
		result.err = err
		return
	} else if len(msg.Signatures()) > 1 {
		result.err = ErrTokenNonCompact
		return
	} else if ademT, err := MkADEMToken(km, msg.Signatures()[0], jwtT); err != nil {
		result.err = err
		return
	} else {
		result.token = ademT
	}
}

// Verify a slice of ADEM tokens.

func VerifyTokens(rawTokens [][]byte, trustedKeys jwk.Set) VerificationResults {

	// (lmeinen) 0 - set up chain of promises from root keys to signing keys
	threadCount, km, results := setupPromiseChain(rawTokens, trustedKeys)

	/*
		(lmeinen) Note the nuance in terminology:
			1 To verify a JWT: Check that the encoded string corresponds to a valid JSON encoding of a JWT, and that the JWT's signature is valid w.r.t. to its verification key
			2 To validate a JWT: Check that a JWT's claims stand (and in this case: that the required field 'ass' resp. 'end' is present)
			3 To verify a security level: Assuming the two above steps have been executed, walk the endorsement chain and check the security level of the emblem as defined in ADEM (incl. endorsement constraints)
	*/

	// (lmeinen) 1 - verify the JWT tokens AND that the key chain results in a valid root key only verified keys are used to verify JWT signatures
	ts := awaitTokenSignatureResults(km, threadCount, results)

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	var protected []*ident.AI
	endorsements := []*ADEMToken{}
	for _, t := range ts {
		if t.Headers.ContentType() == string(consts.EmblemCty) {
			if emblem != nil {
				// Multiple emblems
				log.Print("Token set contains multiple emblems")
				return ResultInvalid()
			} else if err := jwt.Validate(t.Token, jwt.WithValidator(tokens.EmblemValidator)); err != nil {
				log.Printf("Invalid emblem: %s", err)
				return ResultInvalid()
			} else {
				emblem = t
			}

			ass, _ := emblem.Token.Get("ass")
			protected = ass.([]*ident.AI)
			if emblem.Headers.Algorithm() == jwa.NoSignature {
				return VerificationResults{
					results:   []consts.VerificationResult{consts.UNSIGNED},
					protected: protected,
				}
			}
		} else if t.Headers.ContentType() == string(consts.EndorsementCty) {
			err := jwt.Validate(t.Token, jwt.WithValidator(tokens.EndorsementValidator))
			if err != nil {
				log.Printf("Invalid endorsement: %s", err)
			} else {
				endorsements = append( /*@ perm(1/2), @*/ endorsements, t)
			}
		} else {
			log.Printf("Token has wrong type: %s", t.Headers.ContentType())
		}
	}

	if emblem == nil {
		log.Print("no emblem found")
		return ResultInvalid()
	}

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root := verifySignedOrganizational(emblem, endorsements, trustedKeys)
	if util.ContainsVerificationResult(vfyResults, consts.INVALID) {
		return ResultInvalid()
	}

	endorsedResults, endorsedBy := verifyEndorsed(emblem, root, endorsements, trustedKeys)
	if util.ContainsVerificationResult(endorsedResults, consts.INVALID) {
		return ResultInvalid()
	}

	// (lmeinen) 4 - return results
	return VerificationResults{
		results:    append( /*@ perm(1/2), @*/ vfyResults, endorsedResults...),
		issuer:     root.Token.Issuer(),
		endorsedBy: endorsedBy,
		protected:  protected,
	}
}

func awaitTokenSignatureResults(km *keyManager, threadCount int, results chan *TokenVerificationResult) []*ADEMToken {
	ts := []*ADEMToken{}
	for {
		// [waiting] is the number of unresolved promises in the key manager, i.e.,
		// blocked threads that wait for a verification key.
		// [threadCount] is the number of threads that could still provide
		// a new verification key in the [results] channel.
		if waiting := km.waiting(); waiting > 0 && waiting == threadCount {
			// If there are as many waiting threads as threads that could result in a
			// new verification, we miss verification keys and verification will be
			// aborted.
			km.killListeners()
		} else if result := <-results; result == nil {
			// All threads have terminated
			break
		} else {
			// We got a new non-nil result from <-results, and hence, one thread must
			// have terminated. Decrement the counter accordingly.
			threadCount -= 1

			if threadCount == 0 {
				// Every call to [vfyToken] will write exactly one result. Hence, only
				// close the [results] channel, when all threads have terminated.
				close(results /*@, 1, 2, PredTrue!<!> @*/)
			}

			if result.err != nil {
				log.Printf("discarding invalid token: %s", result.err)
			} else {
				ts = append( /*@ perm(1/2), @*/ ts, result.token)
				if k, ok := result.token.Token.Get("key"); ok {
					km.put(k.(tokens.EmbeddedKey).Key)
				}
			}
		}
	}
	return ts
}

func setupPromiseChain(rawTokens [][]byte, trustedKeys jwk.Set) (int, *keyManager, chan *TokenVerificationResult) {
	// We maintain a thread count for termination purposes. It might be that we
	// cannot verify all token's verification key and must cancel verification.
	threadCount := len(rawTokens)
	km := NewKeyManager(len(rawTokens))

	// Put trusted public keys into key manager. This allows for termination for
	// tokens without issuer.
	ctx := context.TODO()
	iter := trustedKeys.Keys(ctx)
	for iter.Next(ctx) {
		km.put(iter.Pair().Value.(jwk.Key))
	}

	results := make(chan *TokenVerificationResult)

	// Start verification threads
	for _, rawToken := range rawTokens {
		go vfyToken(rawToken, km, results)
	}

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()
	return threadCount, km, results
}

func doSend(results chan *TokenVerificationResult, result *TokenVerificationResult) {
	// FIXME: (lmeinen) Gobra doesn't handle anonymous function call properly
	results <- result
}
