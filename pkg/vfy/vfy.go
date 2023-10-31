// +gobra
package vfy

import (
	"context"
	"errors"
	"fmt"
	"log"
	"strings"
	// @ "sync"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/ident"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/adem-wg/adem-proto/pkg/util"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
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

// @ ensures acc(res.results) && acc(res.protected) && acc(res.endorsedBy)
func ResultInvalid() (res VerificationResults) {
	return VerificationResults{results: []consts.VerificationResult{consts.INVALID}}
}

// @ trusted
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
// @ trusted
func vfyToken(rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup @*/) {
	result /*@@@*/ := TokenVerificationResult{}
	defer func /*@ f @*/ () {
		results <- &result
		// @ fold resultsSendFraction!<results, threadCount!>()
		// @ vfyWaitGroup.PayDebt(resultsSendFraction!<results, threadCount!>)
		// @ vfyWaitGroup.Done()
	}() /*@ as f @*/

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
// @ requires acc(rawTokens)
// @ requires len(rawTokens) > 0
// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
// @ requires acc(trustedKeys.Mem(), _)
// @ ensures acc(res.results) && acc(res.protected) && (res.endorsedBy != nil ==> acc(res.endorsedBy))
func VerifyTokens(rawTokens [][]byte, trustedKeys jwk.Set) (res VerificationResults) {

	/*
		(lmeinen) Note the nuance in terminology:
			1 To verify a JWT: Check that the encoded string corresponds to a valid JSON encoding of a JWT, and that the JWT's signature is valid w.r.t. to its verification key
			2 To validate a JWT: Check that a JWT's claims stand (and in this case: that the required field 'ass' resp. 'end' is present)
			3 To verify a security level: Assuming the two above steps have been executed, walk the endorsement chain and check the security level of the emblem as defined in ADEM (incl. endorsement constraints)
	*/

	// (lmeinen) 0 - set up chain of promises from root keys to signing keys
	// @ trusted
	// @ requires acc(rawTokens)
	// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
	// @ requires acc(trustedKeys.Mem(), _)
	// @ ensures acc(km) &&
	// @ 	acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km.listeners!>
	// @ ensures threadCount > 0
	// @ ensures results.RecvChannel() &&
	// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
	// @ 	results.RecvGotPerm() == resultsInvariant!<_!> &&
	// @ 	results.Token(PredTrue!<!>) &&
	// @ 	results.ClosureDebt(PredTrue!<!>, 1, 2)
	// @ ensures vfyWaitGroup.WaitGroupP() &&
	// @ 	vfyWaitGroup.WaitMode() &&
	// @ 	len(fractionSeq) == threadCount &&
	// @ 	(forall i int :: 0 <= i && i < len(fractionSeq) ==> (
	// @ 		fractionSeq[i] == resultsSendFraction!<results, threadCount!> &&
	// @ 		vfyWaitGroup.TokenById(fractionSeq[i], i)))
	// @ outline (
	// We maintain a thread count for termination purposes. It might be that we
	// cannot verify all token's verification key and must cancel verification.
	threadCount := len(rawTokens)
	km := NewKeyManager(len(rawTokens))

	// Put trusted public keys into key manager. This allows for termination for
	// tokens without issuer.
	// TODO: (lmeinen) check on Context semantics and encode in lib stub
	ctx := context.TODO()
	iter := trustedKeys.Keys(ctx)
	for iter.Next(ctx) {
		// TODO: (lmeinen) how to do mem permissions with type casts like this? See protected below for second examplej
		km.put(iter.Pair().Value.(jwk.Key))
	}

	results := make(chan *TokenVerificationResult)
	// @ wg@ := sync.WaitGroup {}
	// @ ghost vfyWaitGroup := &wg
	// @ ghost fractionSeq := seq[pred()] {}
	// @ vfyWaitGroup.Init()
	// @ vfyWaitGroup.Add(threadCount, perm(1), PredTrue!<!>)

	// Start verification threads
	for _, rawToken := range rawTokens {
		// @ ghost sendFraction := resultsSendFraction!<results, threadCount!>
		// @ vfyWaitGroup.GenerateTokenAndDebt(sendFraction)
		// @ fold vfyWaitGroup.TokenById(sendFraction, len(fractionSeq))
		// @ fractionSeq = fractionSeq ++ seq[pred()] { sendFraction }
		go vfyToken(rawToken, km, results /*@, threadCount, vfyWaitGroup @*/)
	}

	// @ vfyWaitGroup.Start(perm(1/2), PredTrue!<!>)
	// @ vfyWaitGroup.SetWaitMode(perm(1/2), perm(1/2))

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()
	// @ )

	// TODO: (lmeinen) Capture intuition that the number of listeners in km was set in step 0, and is now only going to decrease continuously
	//			--> write perm to km.listeners in preconditions (promises coming in handy) + suitable postconditions regarding no of listeners
	// TODO: (lmeinen) Come up with suitable termination measure: threadCount decreases and (therefore) SendChannel perm increases --> result will be nil
	// (lmeinen) 1 - verify the JWT tokens AND that the key chain results in a valid root key only verified keys are used to verify JWT signatures
	// @ ghost n := threadCount

	// @ requires 0 < threadCount && threadCount == n
	// @ requires results.RecvChannel() &&
	// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
	// @ 	results.RecvGotPerm() == resultsInvariant!<_!> &&
	// @ 	results.Token(PredTrue!<!>) &&
	// @ 	results.ClosureDebt(PredTrue!<!>, 1, 2)
	// @ requires acc(km) &&
	// @ 	acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km.listeners!>
	// @ requires vfyWaitGroup.WaitGroupP() &&
	// @ 	vfyWaitGroup.WaitMode() &&
	// @ 	len(fractionSeq) == threadCount &&
	// @ 	(forall i int :: 0 <= i && i < len(fractionSeq) ==> (
	// @ 		fractionSeq[i] == resultsSendFraction!<results, threadCount!> &&
	// @ 		vfyWaitGroup.TokenById(fractionSeq[i], i)))
	// @ ensures acc(ts)
	// @ ensures forall i int :: { ts[i] } 0 <= i && i < len(ts) ==> acc(ts[i]) &&
	// @ 	ts[i].VerificationKey != nil &&
	// @ 	ts[i].Headers != nil &&
	// @ 	ts[i].Token != nil
	// @ outline (
	ts := []*ADEMToken{}
	// @ invariant 0 < n && threadCount <= n
	// @ invariant results.RecvChannel() &&
	// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
	// @ 	results.RecvGotPerm() == resultsInvariant!<_!> &&
	// @ 	results.Token(PredTrue!<!>) &&
	// @ 	(threadCount > 0 ==> (
	// @ 		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
	// @ 		vfyWaitGroup.WaitGroupP() &&
	// @ 		vfyWaitGroup.WaitMode() &&
	// @ 		len(fractionSeq) == n &&
	// @ 		(forall i int :: 0 <= i && i < len(fractionSeq) ==> (
	// @ 			fractionSeq[i] == resultsSendFraction!<results, n!> &&
	// @ 			vfyWaitGroup.TokenById(fractionSeq[i], i))))) &&
	// @ 	(threadCount <= 0 ==> results.Closed())
	// @ invariant acc(km) &&
	// @ 	acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km.listeners!>
	// @ invariant acc(ts)
	// @ invariant forall k int :: { ts[k] } 0 <= k && k < len(ts) ==> acc(ts[k]) &&
	// @ 	ts[k].VerificationKey != nil &&
	// @ 	ts[k].Headers != nil &&
	// @ 	ts[k].Token != nil
	for {
		// @ fold PredTrue!<!>()
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
			// TODO: (lmeinen) Prove termination - Gobra currently doesn't support proving that all subsequent receives will return nil
			// All threads have terminated
			break
		} else {
			// @ unfold resultsInvariant!<_!>(result)

			// We got a new non-nil result from <-results, and hence, one thread must
			// have terminated. Decrement the counter accordingly.
			threadCount -= 1

			if threadCount == 0 {
				/*@
				ghost {
					vfyWaitGroup.Wait(perm(1), fractionSeq)
					invariant 0 <= i && i <= n
					invariant forall j int :: i <= j && j < n ==> sync.InjEval(fractionSeq[j], j)
					invariant acc(results.SendChannel(), i / numSendFractions(n))
					for i := 0; i < n; i++ {
						unfold sync.InjEval(fractionSeq[i], i)
						unfold resultsSendFraction!<results, n!>()
					}
				}
				@*/
				// @ fold PredTrue!<!>()
				// Every call to [vfyToken] will write exactly one result. Hence, only
				// close the [results] channel, when all threads have terminated.
				close(results /*@, 1, 2, PredTrue!<!>@*/)
			}

			if result.err != nil {
				log.Printf("discarding invalid token: %s", result.err)
			} else {
				ts = append( /*@ perm(1/2), @*/ ts, result.token)
				if k, ok := result.token.Token.Get("key"); ok {
					// @ assume typeOf(k) == type[tokens.EmbeddedKey]
					// @ inhale acc(k.(tokens.EmbeddedKey).Key.Mem(), _)
					km.put(k.(tokens.EmbeddedKey).Key)
				}
			}
		}
	}
	// @ )

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	// @ ghost emblemIdx := -1
	var protected []*ident.AI
	endorsements := []*ADEMToken{}

	// @ invariant acc(ts)
	// @ invariant forall k int :: { ts[k] } 0 <= k && k < len(ts) ==> acc(ts[k]) &&
	// @ 	ts[k].VerificationKey != nil &&
	// @ 	ts[k].Headers != nil &&
	// @ 	ts[k].Token != nil
	// @ invariant emblem != nil ==> 0 <= emblemIdx && emblemIdx < len(ts) && emblem == ts[emblemIdx]
	// @ invariant acc(endorsements)
	// @ invariant protected != nil ==> acc(protected)
	for _, t := range ts /*@ with i @*/ {
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
				// @ ghost emblemIdx = i
			}

			ass, _ := emblem.Token.Get("ass")
			// this assumption comes from the successful return of the jwt.Parse function + the type constraints set in claims.go
			// @ assume typeOf(ass) == type[[]*ident.AI]
			// @ inhale acc(ass.([]*ident.AI))
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
	if util.ContainsVerificationResult(vfyResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	endorsedResults, endorsedBy := verifyEndorsed(emblem, root, endorsements, trustedKeys)
	if util.ContainsVerificationResult(endorsedResults, consts.INVALID /*@, perm(1/2) @*/) {
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

/*@
ghost
ensures res == 2 * threadCount
pure func numSendFractions(threadCount int) (res int)

pred resultsInvariant(result *TokenVerificationResult) {
	acc(result) &&
			(result.err == nil ==> (
				acc(result.token) &&
				result.token.VerificationKey != nil &&
				result.token.Headers != nil &&
				result.token.Token != nil)) &&
			(result.err != nil ==> result.token == nil)
}

pred resultsSendFraction(results chan *TokenVerificationResult, threadCount int) {
	0 < threadCount && acc(results.SendChannel(), 1 / numSendFractions(threadCount))
}
@*/
