// +gobra
// @ initEnsures PkgMem()
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
	// @ "github.com/adem-wg/adem-proto/pkg/roots"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

func init() {
	// TODO: (lmeinen) Gobra doesn't handle init order properly yet - really these assumptions should already hold
	// @ assume ErrNoKeyFound != nil &&
	// @ 	ErrRootKeyUnbound != nil &&
	// @ 	ErrAlgsDiffer != nil
	// @ fold PkgMem()
}

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
// @ requires threadCount > 0
// @ requires acc(PkgMem(), 1 / threadCount)
// @ requires acc(roots.PkgMem(), 1 / threadCount)
// @ requires acc(tokens.PkgMem(), _)
// @ requires acc(rawToken, _)
// @ requires km.init.UnitDebt(WaitInv!<!>) &&
// @ 	acc(km.lock.LockP(), _) &&
// @ 	km.lock.LockInv() == LockInv!<km!>
// @ requires acc(results.SendChannel(), 1 / numSendFractions(threadCount)) &&
// @ 	results.SendGivenPerm() == SendToken!<loc, threadCount, _!> &&
// @ 	results.SendGotPerm() == PredTrue!<!>
// @ requires acc(SingleUse(loc), 1 / threadCount)
// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
func vfyToken(rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost loc *int, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup @*/) {
	// @ share threadCount, loc, results, vfyWaitGroup
	result /*@@@*/ := TokenVerificationResult{}
	defer
	// @ requires acc(&threadCount) && acc(&loc) && acc(&results) && acc(&vfyWaitGroup)
	// @ requires threadCount > 0
	// @ requires acc(&result) &&
	// @ 			(result.err == nil ==> result.token.Mem()) &&
	// @ 			(result.err != nil ==> result.token == nil)
	// @ requires acc(results.SendChannel(), 1 / numSendFractions(threadCount)) &&
	// @ 	results.SendGivenPerm() == SendToken!<loc, threadCount, _!> &&
	// @ 	results.SendGotPerm() == PredTrue!<!>
	// @ requires acc(SingleUse(loc), 1 / threadCount)
	// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
	func /*@ f @*/ () {
		// @ fold ResultPerm(&result)
		// @ fold SendToken!<loc, threadCount, _!>(&result)
		results <- &result
		// @ fold SendFraction!<results, threadCount!>()
		// @ vfyWaitGroup.PayDebt(SendFraction!<results, threadCount!>)
		// @ vfyWaitGroup.Done()
	}() /*@ as f @*/

	// @ fold km.Mem()
	jwtT, err := jwt.Parse(rawToken, jwt.WithKeyProvider(km))
	if err != nil {
		result.err = err
		return
	}

	if msg, err := jws.Parse(rawToken); err != nil {
		result.err = err
		return
	} else if len(msg.Signatures( /*@ 1/2 @*/ )) > 1 {
		result.err = /*@ unfolding acc(PkgMem(), _) in @*/ ErrTokenNonCompact
		return
	} else if ademT, err := MkADEMToken(km, msg.Signatures( /*@ 1/2 @*/ )[0], jwtT); err != nil {
		result.err = err
		return
	} else {
		result.token = ademT
	}
}

// Verify a slice of ADEM tokens.
// @ requires PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem()
// @ requires acc(rawTokens)
// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
// @ ensures acc(res.results) && acc(res.protected) && (res.endorsedBy != nil ==> acc(res.endorsedBy))
func VerifyTokens(rawTokens [][]byte, trustedKeys jwk.Set) (res VerificationResults) {

	// Early termination for empty rawTokens slice
	if len(rawTokens) == 0 {
		return ResultInvalid()
	}

	// Ensure trustedKeys is non-nil
	if trustedKeys == nil {
		trustedKeys = jwk.NewSet()
	}

	/*
		(lmeinen) Note the nuance in terminology:
			1 To verify a JWT: Check that the encoded string corresponds to a valid JSON encoding of a JWT, and that the JWT's signature is valid w.r.t. to its verification key
			2 To validate a JWT: Check that a JWT's claims stand (and in this case: that the required field 'ass' resp. 'end' is present)
			3 To verify a security level: Assuming the two above steps have been executed, walk the endorsement chain and check the security level of the emblem as defined in ADEM (incl. endorsement constraints)
	*/

	// (lmeinen) 0 - set up chain of promises from root keys to signing keys

	// We maintain a thread count for termination purposes. It might be that we
	// cannot verify all token's verification key and must cancel verification.
	threadCount := len(rawTokens)
	km := NewKeyManager(len(rawTokens))

	// Put trusted public keys into key manager. This allows for termination for
	// tokens without issuer.
	ctx := context.TODO()
	iter := trustedKeys.Keys(ctx)
	// @ invariant acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(tokens.PkgMem(), _)
	for iter.Next(ctx) {
		// TODO: (lmeinen) how to do mem permissions with type casts like this? See protected below for second examplej
		k := iter.Pair().Value
		// @ assume typeOf(k) == type[jwk.Key]
		km.put(k.(jwk.Key))
	}

	// @ x@ := 42
	// @ ghost loc := &x
	// @ fold SingleUse(loc)
	results := make(chan *TokenVerificationResult)
	// @ results.Init(SendToken!<loc, threadCount, _!>, PredTrue!<!>)
	// @ assert results.SendChannel()
	// @ ghost p, q := 1, 2
	// @ ghost sendp := perm(p/q)
	// @ results.CreateDebt(p, q, PredTrue!<!>)
	// @ assert sendp == threadCount / numSendFractions(threadCount)
	// @ assert acc(results.SendChannel(), sendp)
	// @ assert results.ClosureDebt(PredTrue!<!>, p, q) && results.Token(PredTrue!<!>)

	/* the waitgroup is required to later collect all results send fractions in order to be able to close the channel
	--> note that a single send to the results channel is the last thing a goroutine does, and that the main thread only
		calls wg.Wait() when it has received a result from every spawned routine. Therefore, the waitgroup does not
		influence concurrent behavior of the program and can be used as a proof utility.
	*/
	// @ wg@ := sync.WaitGroup {}
	// @ ghost vfyWaitGroup := &wg
	// @ ghost fractionSeq := seq[pred()] {}
	// @ vfyWaitGroup.Init()
	// @ vfyWaitGroup.Add(threadCount, perm(1), PredTrue!<!>)
	// @ vfyWaitGroup.Start(1/2, PredTrue!<!>)

	// Start verification threads
	// @ invariant threadCount == len(rawTokens)
	// @ invariant acc(PkgMem(), (threadCount - i0) / threadCount)
	// @ invariant acc(roots.PkgMem(), (threadCount - i0) / threadCount)
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(rawTokens, _)
	// @ invariant forall i int :: { rawTokens[i] } i0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
	// @ invariant acc(km.init.UnitDebt(WaitInv!<!>), (threadCount - i0)) &&
	// @ 	acc(km.lock.LockP(), _) &&
	// @ 	km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(vfyWaitGroup.UnitDebt(PredTrue!<!>), threadCount - i0)
	// @ invariant i0 < len(rawTokens) ==> (
	// @ 	sendp > 0 &&
	// @ 	sendp == (threadCount - i0) / numSendFractions(threadCount) &&
	// @ 	acc(results.SendChannel(), sendp) &&
	// @ 	results.SendGivenPerm() == SendToken!<loc, threadCount, _!> &&
	// @ 	results.SendGotPerm() == PredTrue!<!> &&
	// @ 	acc(SingleUse(loc), (threadCount - i0) / threadCount))
	// @ invariant len(fractionSeq) == i0 &&
	// @ 	(forall i int :: { fractionSeq[i] } 0 <= i && i < i0 ==> (
	// @ 		fractionSeq[i] == SendFraction!<results, threadCount!> &&
	// @ 		vfyWaitGroup.TokenById(fractionSeq[i], i)))
	for _, rawToken := range rawTokens /*@ with i0 @*/ {
		// @ ghost sendFraction := SendFraction!<results, threadCount!>
		// @ vfyWaitGroup.GenerateTokenAndDebt(sendFraction)
		// @ fold vfyWaitGroup.TokenById(sendFraction, len(fractionSeq))
		// @ fractionSeq = fractionSeq ++ seq[pred()] { sendFraction }
		go vfyToken(rawToken, km, results /*@, loc, threadCount, vfyWaitGroup @*/)
		// @ sendp = sendp - perm(1 / numSendFractions(threadCount))

		// @ assert sendp == (threadCount - i0 - 1) / numSendFractions(threadCount)
		// @ assert i0 < len(rawTokens) - 1 ? sendp > 0 : sendp == 0
	}

	// @ vfyWaitGroup.SetWaitMode(1/2, 1/2)

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()
	//  )

	// TODO: (lmeinen) Capture intuition that the number of listeners in km was set in step 0, and is now only going to decrease continuously
	//			--> write perm to km.listeners in preconditions (promises coming in handy) + suitable postconditions regarding no of listeners
	// TODO: (lmeinen) Come up with suitable termination measure: threadCount decreases and (therefore) SendChannel perm increases --> result will be nil

	// (lmeinen) 1 - verify the JWT tokens AND that the key chain results in a valid root key only verified keys are used to verify JWT signatures
	// @ ghost n := threadCount

	/* ensures:
	- list of tokens, where:
		(a) every token is non-nil
		(b) every token is unique
		(c) every goroutine contributed at most one token
		(d) there are at most as many tokens as there were rawTokens
	*/
	ts := []*ADEMToken{}
	// @ fold TokenList(ts)

	/* invariant:
	- retain receive permission to results channel: allows receiving nil to break out of loop
	- as long as we haven't received all results, the channel is not closed
	- as soon as we have received one result from every goroutine, the channel is closed
	- TokenList(ts) to current list of tokens (see (a)-(d) above)
	*/
	// @ invariant 0 < n && threadCount <= n
	// @ invariant acc(loc, (n - threadCount) / n)
	// @ invariant 0 <= threadCount
	// @ invariant results.RecvChannel() &&
	// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
	// @ 	results.RecvGotPerm() == SendToken!<loc, n, _!> &&
	// @ 	(threadCount > 0 ==> (
	// @ 		results.Token(PredTrue!<!>) &&
	// @ 		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
	// @ 		vfyWaitGroup.WaitGroupP() &&
	// @ 		vfyWaitGroup.WaitMode() &&
	// @ 		len(fractionSeq) == n &&
	// @ 		(forall i int :: { fractionSeq[i] } 0 <= i && i < len(fractionSeq) ==> (
	// @ 			fractionSeq[i] == SendFraction!<results, n!> &&
	// @ 			vfyWaitGroup.TokenById(fractionSeq[i], i))))) &&
	// @ 	(threadCount <= 0 ==> results.Closed())
	// @ invariant acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant TokenList(ts)
	// @ invariant len(ts) <= n - threadCount
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
			// @ unfold SendToken!<loc, n, _!>(result)
			// @ unfold acc(SingleUse(loc), 1 / n)
			// @ unfold ResultPerm(result)

			// We got a new non-nil result from <-results, and hence, one thread must
			// have terminated. Decrement the counter accordingly.
			threadCount -= 1

			if threadCount == 0 {
				// @ vfyWaitGroup.Wait(perm(1), fractionSeq)
				/*@
				ghost {
					invariant 0 <= i && i <= n
					invariant forall j int :: { fractionSeq[j] } i <= j && j < n ==> sync.InjEval(fractionSeq[j], j)
					invariant acc(results.SendChannel(), i / numSendFractions(n))
					for i := 0; i < n; i++ {
						unfold sync.InjEval(fractionSeq[i], i)
						unfold SendFraction!<results, n!>()
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
				// @ unfold TokenList(ts)
				// @ unfold result.token.Mem()
				// @ assert forall k int :: { ts[k] } 0 <= k && k < len(ts) ==> unfolding ts[k].Mem() in ts[k] != result.token
				ts = append( /*@ perm(1/2), @*/ ts, result.token)
				if k, ok := result.token.Token.Get("key"); ok {
					// @ assume typeOf(k) == type[tokens.EmbeddedKey] && k.(tokens.EmbeddedKey).Key != nil
					km.put(k.(tokens.EmbeddedKey).Key)
				}
				// @ fold result.token.Mem()
				// @ fold TokenList(ts)
			}
		}
	}

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	// @ ghost emblemIdx := -1
	// @ ghost endorsementIdx := seq[int] {}
	var protected []*ident.AI
	endorsements := []*ADEMToken{}

	// @ unfold TokenList(ts)

	// @ invariant acc(ts) &&
	// @ 	(forall i int :: { ts[i] } 0 <= i && i < len(ts) ==> ts[i] != nil && ts[i].Mem()) &&
	// @ 	(forall i, j int :: { ts[i], ts[j] } 0 <= i && i < j && j < len(ts) ==> ts[i] != ts[j])
	// @ invariant emblem != nil ==> (
	// @ 	0 <= emblemIdx &&
	// @ 	emblemIdx < i0 &&
	// @ 	emblem == ts[emblemIdx])
	// @ invariant acc(endorsements) &&
	// @ 	len(endorsements) == len(endorsementIdx) &&
	// @ 	(len(endorsements) == 0 || len(endorsements) <= i0) &&
	// @ 	(forall i, j int :: { endorsements[i], endorsements[j] } 0 <= i && i < j && j < len(endorsements) ==> endorsements[i] != endorsements[j]) &&
	// @ 	(forall i, j int :: { endorsementIdx[i], endorsementIdx[j] } 0 <= i && i < j && j < len(endorsements) ==> endorsementIdx[i] != endorsementIdx[j]) &&
	// @ 	(forall i int :: { endorsementIdx[i] } 0 <= i && i < len(endorsementIdx) ==> 0 <= endorsementIdx[i] && endorsementIdx[i] < i0) &&
	// @ 	(forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> endorsements[i] == ts[endorsementIdx[i]])
	// @ invariant protected != nil ==> acc(protected)
	for _, t := range ts /*@ with i0 @*/ {
		// @ unfold t.Mem()
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
				// @ ghost emblemIdx = i0
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
				// @ endorsementIdx = endorsementIdx ++ seq[int] { i0 }
			}
		} else {
			log.Printf("Token has wrong type: %s", t.Headers.ContentType())
		}
		// @ fold t.Mem()
	}

	// @ fold acc(TokenList(endorsements), 1/2)

	if emblem == nil {
		log.Print("no emblem found")
		return ResultInvalid()
	}

	// @ assert acc(emblem.Mem(), 1/2)
	// @ assert acc(TokenList(endorsements), 1/2)

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root := verifySignedOrganizational(emblem, endorsements, trustedKeys /*@, perm(1/2) @*/)
	if util.ContainsVerificationResult(vfyResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	// @ assert acc(TokenList(endorsements), 1/4)
	// @ assert acc(emblem.Mem(), 1/4)
	// @ assert acc(root.Mem(), 1/4)

	endorsedResults, endorsedBy := verifyEndorsed(emblem, root, endorsements, trustedKeys /*@, perm(1/4) @*/)
	if util.ContainsVerificationResult(endorsedResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	// @ unfold acc(root.Mem(), _)

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
requires threadCount > 0
ensures res == 2 * threadCount
pure func numSendFractions(threadCount int) (res int) {
	return 2 * threadCount
}

pred SendToken(loc *int, threadCount int, result *TokenVerificationResult) {
	threadCount > 0 && acc(SingleUse(loc), 1 / threadCount) && ResultPerm(result)
}

pred SingleUse(loc *int) {
	acc(loc)
}

pred ResultPerm(result *TokenVerificationResult) {
	acc(result) &&
			(result.err == nil ==> result.token.Mem()) &&
			(result.err != nil ==> result.token == nil)
}

pred SendFraction(results chan *TokenVerificationResult, threadCount int) {
	0 < threadCount && acc(results.SendChannel(), 1 / numSendFractions(threadCount))
}

pred PkgMem() {
	ErrTokenNonCompact != nil &&
	ErrNoKeyFound != nil &&
	ErrRootKeyUnbound != nil &&
	ErrAlgsDiffer != nil
}

@*/
