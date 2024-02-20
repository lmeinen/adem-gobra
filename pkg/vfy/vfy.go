// +gobra
// ##(--onlyFilesWithHeader)
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
	// @ . "github.com/adem-wg/adem-proto/pkg/goblib"
	// @ "github.com/adem-wg/adem-proto/pkg/roots"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
	//@ "claim"
	//@ "fact"
	//@ "place"
	//@ "iospec"
	//@ "term"
	//@ "pub"
	//@ "fresh"
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
	// @ t term.Term
	err error
}

// Verify an ADEM token's signature. Designed to be called asynchronously.
// Results will be returned to the [results] channel. Verification keys will be
// obtained from [km].
// Every call to [vfyToken] will write to [results] exactly once.
// @ requires threadCount > 0
// @ requires acc(PkgMems(), 1 / threadCount)
// @ requires acc(rawToken, _)
// @ requires km.init.UnitDebt(WaitInv!<!>) &&
// @ 	acc(km.lock.LockP(), _) &&
// @ 	km.lock.LockInv() == LockInv!<km!>
// @ requires acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
// @ requires ValidationPerm(tokenT)
func vfyToken(rid uint64, rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost loc *int, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup, ghost tokenT term.Term @*/) {
	// @ share threadCount, loc, results, vfyWaitGroup

	// @ unfold acc(PkgMems(), 1 / threadCount)
	result /*@@@*/ := TokenVerificationResult{}
	defer
	// @ requires acc(&threadCount) && acc(&loc) && acc(&results) && acc(&vfyWaitGroup)
	// @ requires threadCount > 0
	// @ requires acc(&result) &&
	// @ 			(result.err == nil ==> (
	// @ 				result.token != nil &&
	// @ 				ValidToken(result.token))) &&
	// @ 			(result.err != nil ==> result.token == nil)
	// @ requires acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
	// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
	func /*@ f @*/ () {
		// @ unfold acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
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

//	ensures r != nil ==> Abs(r) == gamma(rT)
//
// @ requires results.RecvChannel() &&
// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
// @ 	results.RecvGotPerm() == SendToken!<loc, n, _!>
// @ requires results.RecvGivenPerm()()
// @ ensures results.RecvChannel() &&
// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
// @ 	results.RecvGotPerm() == SendToken!<loc, n, _!>
// @ ensures r != nil ==> results.RecvGotPerm()(r)
func resultsRecv(results chan *TokenVerificationResult /*@, ghost loc *int, ghost n int, ghost p place.Place, ghost rid term.Term @*/) (r *TokenVerificationResult) {
	r = <-results
	return r
}

// Verify a slice of ADEM tokens.
// @ requires PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem()
// @ requires place.token(p) && iospec.P_Verifier(p, term.freshTerm(fresh.fr_integer64(rid)), mset[fact.Fact]{})
// @ requires acc(&jwt.Custom, 1/2) && acc(jwt.Custom, 1/2) && tokens.CustomFields(jwt.Custom)
// @ requires acc(rawTokens)
// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
// @ requires trustedKeys != nil && trustedKeys.Mem() && jwk.KeySeq(trustedKeys.Elems())
// @ ensures acc(res.results) && acc(res.protected) && (res.endorsedBy != nil ==> acc(res.endorsedBy))
func VerifyTokens(rid uint64, rawTokens [][]byte, trustedKeys jwk.Set /*@, ghost p place.Place @*/) (res VerificationResults) {
	// @ ghost ridT := term.freshTerm(fresh.fr_integer64(rid))
	// @ ghost s := mset[fact.Fact]{}

	// @ unfold iospec.P_Verifier(p, ridT, s)
	// @ unfold iospec.phiRF_Verifier_18(p, ridT, s)
	// @ p = iospec.get_e_Setup_Verifier_placeDst(p, ridT)
	// @ s = mset[fact.Fact] { fact.Setup_Verifier(ridT) }

	// TODO: Is there a better way to do this? Or is this just the assumption that library functions are allowed to make
	// @ inhale place.token(p)

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
	iter := trustedKeys.Keys(ctx /*@, perm(1/2) @*/)
	// @ unfold jwk.KeySeq(trustedKeys.Elems())
	// @ assert forall i int :: { trustedKeys.Elems()[i] } 0 <= i && i < len(trustedKeys.Elems()) ==> trustedKeys.Elems()[i].Mem()

	iterNext := iter.Next(ctx)

	// @ invariant acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(trustedKeys.Mem(), 1/2) &&
	// @ 	iter.IterMem() &&
	// @ 	(iterNext ==> iter.Index() < len(iter.GetIterSeq())) &&
	// @ 	trustedKeys.Elems() == iter.GetIterSeq() &&
	// @ 	(forall i int :: { iter.GetIterSeq()[i] } 0 <= i && i < iter.Index() && i < len(iter.GetIterSeq()) ==> acc(iter.GetIterSeq()[i].(jwk.Key).Mem(), _)) &&
	// @ 	(forall i int :: { iter.GetIterSeq()[i] } iter.Index() <= i && i < len(iter.GetIterSeq()) ==> iter.GetIterSeq()[i].(jwk.Key).Mem())
	// @ decreases len(iter.GetIterSeq()) - iter.Index()
	for iterNext {
		k := iter.Pair( /*@ perm(1/2) @*/ ).Value
		iterNext = iter.Next(ctx)
		km.put(k.(jwk.Key))
		// @ assert acc(k.(jwk.Key).Mem(), _)
	}

	// @ fold acc(jwk.KeySeq(trustedKeys.Elems()), _)

	/*@
	unfold iospec.P_Verifier(p, ridT, s)
	unfold iospec.phiR_Verifier_0(p, ridT, s)
	l := mset[fact.Fact] { fact.Setup_Verifier(ridT) }
	a := mset[claim.Claim] { }
	r := mset[fact.Fact] { fact.St_Verifier_1(ridT) }
	p = iospec.internBIO_e_FinishSetup(p, ridT, l, a, r)
	s = fact.U(l, r, s)
	@*/

	// @ x@ := 42
	// @ ghost loc := &x
	// @ fold SingleUse(loc)
	results := make(chan *TokenVerificationResult)
	// @ results.Init(SendToken!<loc, threadCount, _!>, PredTrue!<!>)
	// @ results.CreateDebt(1, 2, PredTrue!<!>)
	// @ fold ResultsInv(loc, threadCount, results)

	/* the waitgroup is required to later collect all results send fractions in order to be able to close the channel
	--> note that a single send to the results channel is the last thing a goroutine does, and that the main thread only
	calls wg.Wait() when it has received a result from every spawned routine. Therefore, the waitgroup does not
	influence concurrent behavior of the program and can be used as a proof utility.
	*/
	// @ wg@ := sync.WaitGroup {}
	// @ ghost vfyWaitGroup := &wg
	// @ vfyWaitGroup.Init()
	// @ vfyWaitGroup.Add(threadCount, perm(1), PredTrue!<!>)
	// @ vfyWaitGroup.Start(1/2, PredTrue!<!>)
	// @ ghost fractionSeq := generateTokenSeq(vfyWaitGroup, threadCount, results)

	// @ fold PkgMems()

	// Start verification threads
	// @ invariant place.token(p) && fact.St_Verifier_1(ridT) in s && iospec.P_Verifier(p, ridT, s)
	// @ invariant threadCount == len(rawTokens)
	// @ invariant acc(PkgMems(), (threadCount - i0) / threadCount)
	// @ invariant acc(rawTokens, _)
	// @ invariant forall i int :: { rawTokens[i] } i0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
	// @ invariant acc(km.init.UnitDebt(WaitInv!<!>), (threadCount - i0)) &&
	// @ 	acc(km.lock.LockP(), _) &&
	// @ 	km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(ResultsInv(loc, threadCount, results), (threadCount - i0) / threadCount)
	// @ invariant acc(wg.UnitDebt(SendFraction!<results, threadCount!>), threadCount - i0)
	for i, rawToken := range rawTokens /*@ with i0 @*/ {
		// Produce In fact for token
		/*@
		unfold iospec.P_Verifier(p, ridT, s)
		unfold iospec.phiRF_Verifier_16(p, ridT, s)
		tokenT, pp := tokenIn(rawToken, perm(1/2), p, ridT)
		p = pp
		s = s union mset[fact.Fact] { fact.InFact_Verifier(ridT, tokenT) }
		@*/

		// Produce PermitTokenVerificationOut fact
		/*@
		unfold iospec.P_Verifier(p, ridT, s)
		unfold iospec.phiR_Verifier_1(p, ridT, s)
		l := mset[fact.Fact] { fact.St_Verifier_1(ridT), fact.InFact_Verifier(ridT, tokenT) }
		a := mset[claim.Claim] { }
		r := mset[fact.Fact] { fact.St_Verifier_1(ridT), fact.PermitTokenVerificationOut_Verifier(ridT, tokenT) }
		p = iospec.internBIO_e_ReceiveToken(p, ridT, tokenT, l, a, r)
		s = fact.U(l, r, s)
		@*/

		// 'Persist' Out fact
		/*@
		unfold iospec.P_Verifier(p, ridT, s)
		unfold iospec.phiRG_Verifier_14(p, ridT, s)
		assert iospec.e_PermitTokenVerificationOut(p, ridT, tokenT)
		p = permissionOut(p, ridT, tokenT)
		s = s setminus mset[fact.Fact] { fact.PermitTokenVerificationOut_Verifier(ridT, tokenT) }
		@*/

		go vfyToken(uint64(i), rawToken, km, results /*@, loc, threadCount, vfyWaitGroup, tokenT @*/)
	}

	// @ vfyWaitGroup.SetWaitMode(1/2, 1/2)
	// @ fold VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()

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

	/*@
	unfold iospec.P_Verifier(p, ridT, s)
	unfold iospec.phiR_Verifier_2(p, ridT, s)
	l := mset[fact.Fact] { fact.St_Verifier_1(ridT) }
	a := mset[claim.Claim] { }
	r := mset[fact.Fact] { fact.St_Verifier_2(ridT) }
	p = iospec.internBIO_e_ReceiveTokenFinish(p, ridT, l, a, r)
	s = fact.U(l, r, s)
	@*/

	/* invariant:
	- retain receive permission to results channel: allows receiving nil to break out of loop
	- as long as we haven't received all results, the channel is not closed
	- as soon as we have received one result froim every goroutine, the channel is closed
	- TokenList(ts) to current list of tokens (see (a)-(d) above)
	*/
	// @ invariant place.token(p) && fact.St_Verifier_2(ridT) in s && iospec.P_Verifier(p, ridT, s)
	// @ invariant 0 < n && threadCount <= n
	//  invariant acc(loc, (n - threadCount) / n)
	//  invariant 0 <= threadCount
	// @ invariant results.RecvChannel() &&
	// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
	// @ 	results.RecvGotPerm() == SendToken!<loc, n, _!> &&
	// @ 	(threadCount > 0 ==> (
	// @ 		results.Token(PredTrue!<!>) &&
	// @ 		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
	// @ 		VfyWg(vfyWaitGroup, n, results, fractionSeq))) &&
	// @ 	(threadCount <= 0 ==> results.Closed())
	// @ invariant acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant TokenList(ts)
	// @ invariant len(ts) <= n - threadCount
	for {
		// @ fold PredTrue!<!>()
		//  unfold iospec.P_Verifier(p, ridT, s)
		//  unfold iospec.phiRF_Verifier_17(p, ridT, s)
		// [waiting] is the number of unresolved promises in the key manager, i.e.,
		// blocked threads that wait for a verification key.
		// [threadCount] is the number of threads that could still provide
		// a new verification key in the [results] channel.
		if waiting := km.waiting(); waiting > 0 && waiting == threadCount {
			// If there are as many waiting threads as threads that could result in a
			// new verification, we miss verification keys and verification will be
			// aborted.
			km.killListeners()
			// } else if result /*@, resT, p0 @*/ := ResultsRecv(results /*@, loc, n, p, ridT @*/); result == nil {
		} else if result := <-results; result == nil {
			//  p = p0

			// All threads have terminated
			break
		} else {
			//  p = p0
			//  s = s union mset[fact.Fact] { fact.ValidTokenIn_Verifier(ridT, resT) }

			// @ unfold SendToken!<loc, n, _!>(result)
			// @ unfold acc(SingleUse(loc), 1 / n)
			// @ unfold ResultPerm(result)

			// We got a new non-nil result from <-results, and hence, one thread must
			// have terminated. Decrement the counter accordingly.
			threadCount -= 1

			if threadCount == 0 {
				// @ unfold VfyWg(vfyWaitGroup, n, results, fractionSeq)
				// @ vfyWaitGroup.Wait(perm(1), fractionSeq)
				// @ collectDebt(fractionSeq, n, results)
				// @ fold PredTrue!<!>()

				// Every call to [vfyToken] will write exactly one result. Hence, only
				// close the [results] channel, when all threads have terminated.
				close(results /*@, 1, 2, PredTrue!<!>@*/)
			}

			if result.err != nil {
				log.Printf("discarding invalid token: %s", result.err)
			} else {
				// @ unfold TokenList(ts)
				// @ unfold ValidToken(result.token)
				ts = append( /*@ perm(1/2), @*/ ts, result.token)
				if k, ok := result.token.Token.Get("key"); ok {
					// (lmeinen) the below unfold stmt doesn't terminate - replaced with corresponding viper stmts
					//  unfold tokens.KeyMem(k.(tokens.EmbeddedKey))
					// @ assert tokens.KeyMem(k.(tokens.EmbeddedKey))
					// @ exhale tokens.KeyMem(k.(tokens.EmbeddedKey))
					// @ inhale k.(tokens.EmbeddedKey).Key.Mem()
					km.put(k.(tokens.EmbeddedKey).Key)
				}
				// @ fold ValidToken(result.token)
				// @ fold TokenListElem(len(ts) - 1, result.token)
				// @ fold TokenList(ts)
			}
		}
	}

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	var protected []*ident.AI
	endorsements := []*ADEMToken{}
	// @ fold EndorsementList(endorsements)

	// @ assert iospec.P_Verifier(p, ridT, s)

	// @ unfold TokenList(ts)

	// @ invariant iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(ts, _) &&
	// @ 	forall i int :: { ts[i] } 0 <= i && i0 <= i && i < len(ts) ==> TokenListElem(i, ts[i])
	// @ invariant emblem != nil ==> Emblem(emblem)
	// @ invariant EndorsementList(endorsements)
	// @ invariant protected != nil ==> acc(protected)
	for _, t := range ts /*@ with i0 @*/ {
		// @ unfold TokenListElem(i0, t)
		// @ unfold ValidToken(t)
		if t.Headers.ContentType() == string(consts.EmblemCty) {
			// @ fold acc(tokens.EmblemValidator.Mem(), _)
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
			// @ unfold tokens.AssMem(protected)

			if emblem.Headers.Algorithm() == jwa.NoSignature {
				// TODO: Apply IsUnsignedEmblem rule
				// --> constraints on emblem term: <'emblem', $E>

				return VerificationResults{
					results:   []consts.VerificationResult{consts.UNSIGNED},
					protected: protected,
				}
			}

			// @ unfold tokens.EmblemValidator.Constraints(emblem.Token)
			// @ fold Emblem(emblem)
		} else if t.Headers.ContentType() == string(consts.EndorsementCty) {
			// @ fold acc(tokens.EndorsementValidator.Mem(), _)
			o := jwt.WithValidator(tokens.EndorsementValidator)
			err := jwt.Validate(t.Token, o)
			if err != nil {
				log.Printf("Invalid endorsement: %s", err)
			} else {
				// @ unfold tokens.EndorsementValidator.Constraints(t.Token)
				// @ unfold EndorsementList(endorsements)
				endorsements = append( /*@ perm(1/2), @*/ endorsements, t)
				// @ fold acc(ValidToken(t), 1/2)
				// @ fold Endorsement(t)
				// @ fold EndListElem(i0, t)
				// @ fold EndorsementList(endorsements)
			}
		} else {
			log.Printf("Token has wrong type: %s", t.Headers.ContentType())
		}
	}

	if emblem == nil {
		log.Print("no emblem found")
		return ResultInvalid()
	}

	// @ assert acc(Emblem(emblem), 1/2)
	// @ assert acc(EndorsementList(endorsements), 1/2)

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root := verifySignedOrganizational(emblem, endorsements, trustedKeys /*@, perm(1/2) @*/)
	if util.ContainsVerificationResult(vfyResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	// @ assert acc(EndorsementList(endorsements), 1/4)
	// @ assert acc(Emblem(emblem), 1/4)
	// @ assert acc(ValidToken(root), 1/4)

	endorsedResults, endorsedBy := verifyEndorsed(emblem, root, endorsements, trustedKeys /*@, perm(1/4) @*/)
	if util.ContainsVerificationResult(endorsedResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	// @ unfold acc(ValidToken(root), _)

	// (lmeinen) 4 - return results
	return VerificationResults{
		results:    append( /*@ perm(1/2), @*/ vfyResults, endorsedResults...),
		issuer:     root.Token.Issuer(),
		endorsedBy: endorsedBy,
		protected:  protected,
	}
}

/*@

pred SingleUse(loc *int) {
	acc(loc)
}

pred ResultPerm(result *TokenVerificationResult) {
	acc(result) &&
			(result.err == nil ==> (
				result.token != nil &&
				ValidToken(result.token))) &&
			(result.err != nil ==> result.token == nil)
}

pred SendToken(loc *int, threadCount int, result *TokenVerificationResult) {
	threadCount > 0 && acc(SingleUse(loc), 1 / threadCount) && ResultPerm(result)
}

pred ResultsInv(loc *int, threadCount int, results chan *TokenVerificationResult) {
	threadCount > 0 &&
	acc(results.SendChannel(), perm(1/2)) &&
	results.SendGivenPerm() == SendToken!<loc, threadCount, _!> &&
	results.SendGotPerm() == PredTrue!<!> &&
	SingleUse(loc)
}

pred SendFraction(results chan *TokenVerificationResult, n int) {
	0 < n && acc(results.SendChannel(), 1 / (2 * n))
}

pred VfyWg(wg *sync.WaitGroup, n int, results chan *TokenVerificationResult, ghost fractionSeq seq[pred()]) {
	n > 0 &&
	wg.WaitGroupP() &&
	wg.WaitMode() &&
	len(fractionSeq) == n &&
	forall i int :: { fractionSeq[i] } 0 <= i && i < len(fractionSeq) ==> (
		fractionSeq[i] == SendFraction!<results, n!> &&
		wg.TokenById(fractionSeq[i], i))
}

pred PkgMem() {
	ErrTokenNonCompact != nil &&
	ErrNoKeyFound != nil &&
	ErrRootKeyUnbound != nil &&
	ErrAlgsDiffer != nil
}

pred PkgMems() {
	PkgMem() &&
	roots.PkgMem() &&
	acc(tokens.PkgMem(), _) &&
	acc(&jwt.Custom, _) &&
		acc(jwt.Custom, _) &&
		tokens.CustomFields(jwt.Custom)
}

ghost
requires n > 0
requires acc(wg.UnitDebt(PredTrue!<!>), n)
ensures n == old(n)
ensures len(fractionSeq) == n &&
	forall i int :: { fractionSeq[i] } 0 <= i && i < n ==> (
		fractionSeq[i] == SendFraction!<results, n!> &&
		wg.TokenById(fractionSeq[i], i))
ensures acc(wg.UnitDebt(SendFraction!<results, n!>), n)
decreases _
func generateTokenSeq(wg *sync.WaitGroup, n int, results chan *TokenVerificationResult) (fractionSeq seq[pred()]) {
	fractionSeq := seq[pred()] {}
	invariant 0 <= i && i <= n
	invariant acc(wg.UnitDebt(PredTrue!<!>), n - i)
	invariant acc(wg.UnitDebt(SendFraction!<results, n!>), i)
	invariant len(fractionSeq) == i &&
		forall j int :: { fractionSeq[j] } 0 <= j && j < i ==> (
			fractionSeq[j] == SendFraction!<results, n!> &&
			wg.TokenById(fractionSeq[j], j))
	for i := 0; i < n; i++ {
		ghost sendFraction := SendFraction!<results, n!>
		wg.GenerateTokenAndDebt(sendFraction)
		fold wg.TokenById(sendFraction, len(fractionSeq))
		fractionSeq = fractionSeq ++ seq[pred()] { sendFraction }
	}
}

ghost
requires n > 0
requires len(fractionSeq) == n &&
	forall i int :: { fractionSeq[i] } 0 <= i && i < n ==> (
		sync.InjEval(fractionSeq[i], i) &&
		fractionSeq[i] == SendFraction!<results, n!>)
ensures acc(results.SendChannel(), 1/2)
decreases _
func collectDebt(fractionSeq seq[pred()], n int, results chan *TokenVerificationResult) {
	invariant 0 <= i && i <= n
	invariant forall j int :: { fractionSeq[j] } i <= j && j < n ==> sync.InjEval(fractionSeq[j], j)
	invariant acc(results.SendChannel(), i / (2 * n))
	for i := 0; i < n; i++ {
		unfold sync.InjEval(fractionSeq[i], i)
		unfold SendFraction!<results, n!>()
	}
}

ghost
requires tokenP > 0 && acc(rawToken, tokenP)
requires place.token(p) && iospec.e_InFact(p, ridT)
ensures acc(rawToken, tokenP)
ensures gamma(tokenT) == AbsBytes(rawToken)
ensures tokenT == old(iospec.get_e_InFact_r1(p, ridT))
ensures place.token(pp) && pp == old(iospec.get_e_InFact_placeDst(p, ridT))
decreases  _
func tokenIn(rawToken []byte, ghost tokenP perm, ghost p place.Place, ghost ridT term.Term) (ghost tokenT term.Term, ghost pp place.Place) {
	tokenT := iospec.get_e_InFact_r1(p, ridT)
	assume gamma(tokenT) == AbsBytes(rawToken)
	pp := iospec.get_e_InFact_placeDst(p, ridT)
	inhale place.token(pp)
	return tokenT, pp
}

pred ValidationPerm(ghost t term.Term)

ghost
requires place.token(p) && iospec.e_PermitTokenVerificationOut(p, rid, t)
ensures pp == old(iospec.get_e_PermitTokenVerificationOut_placeDst(p, rid, t)) && place.token(pp)
ensures ValidationPerm(t)
decreases _
func permissionOut(ghost p place.Place, ghost rid term.Term, ghost t term.Term) (ghost pp place.Place) {
	exhale place.token(p)
	pp := iospec.get_e_PermitTokenVerificationOut_placeDst(p, rid, t)
	inhale place.token(pp)
	inhale ValidationPerm(t)
}

ghost
decreases _
func permissionIn(ghost p place.Place, ghost rid term.Term, ghost t term.Term) (ghost pp place.Place) {
	// TODO
}

@*/
