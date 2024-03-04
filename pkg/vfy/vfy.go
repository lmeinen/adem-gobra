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
	// @ . "lib"
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
// @ requires ValidationPerm(tokenT) && gamma(tokenT) == AbsBytes(rawToken)
// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
func vfyToken(rid uint64, rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost loc *int, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup, ghost tokenT term.Term @*/) {
	// @ share threadCount, loc, results, vfyWaitGroup, tokenT
	// @ ghost p@ := GenericPlace()
	// @ ghost ridT@ := term.freshTerm(fresh.fr_integer64(rid))
	// @ ghost s := mset[fact.Fact]{}

	// TODO: (lmeinen) argument for why this is sound
	// @ inhale iospec.P_TokenVerifier(p, ridT, s)

	// @ unfold iospec.P_TokenVerifier(p, ridT, s)
	// @ unfold iospec.phiRF_TokenVerifier_11(p, ridT, s)
	// @ p = iospec.get_e_Setup_TokenVerifier_placeDst(p, ridT)
	// @ s = mset[fact.Fact] { fact.Setup_TokenVerifier(ridT) }

	// @ inhale place.token(p)

	// @ unfold acc(PkgMems(), 1 / threadCount)
	result /*@@@*/ := TokenVerificationResult{}
	defer
	// @ requires acc(&threadCount) && acc(&loc) && acc(&results) && acc(&vfyWaitGroup) && acc(&p) && acc(&ridT) && acc(&tokenT)
	// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ requires threadCount > 0
	// @ requires acc(&result) &&
	// @ 			(result.err == nil ==> (
	// @ 				result.token != nil &&
	// @ 				ValidToken(result.token) &&
	// @ 				iospec.e_ValidTokenOut(p, ridT, tokenT) &&
	// @ 				Abs(result.token) == gamma(tokenT))) &&
	// @ 			(result.err != nil ==> result.token == nil)
	// @ requires acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
	// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
	func /*@ f @*/ () {
		// @ unfold acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
		// @ fold ResultPerm(&result)
		// @ fold SendToken(loc, threadCount, &result)
		resultsSend(results, &result /*@, loc, threadCount, p, ridT, tokenT @*/)
		// @ fold SendFraction!<results, threadCount!>()
		// @ vfyWaitGroup.PayDebt(SendFraction!<results, threadCount!>)
		// @ vfyWaitGroup.Done()
	}() /*@ as f @*/

	// @ unfold iospec.P_TokenVerifier(p, ridT, s)
	// @ unfold iospec.phiRF_TokenVerifier_7(p, ridT, s)
	// @ tokenT, p = permissionIn(tokenT, p, ridT)
	// @ s = s union mset[fact.Fact] { fact.PermitTokenVerificationIn_TokenVerifier(ridT, tokenT) }

	// @ fold TokenVerifierInitState(p, ridT, s, tokenT)
	// @ fold km.Mem()
	options := []jwt.ParseOption{jwt.WithKeyProvider(km)}
	jwtT /*@, p, s @*/, err := jwt.Parse(rawToken /*@, p, ridT, s, tokenT @*/, options...)
	if err != nil {
		result.err = err
		return
	}
	// @ unfold TokenVerifierTermState(p, ridT, s, tokenT)

	// @ assert place.token(p) && iospec.P_TokenVerifier(p, ridT, s) &&
	// @ 	fact.St_TokenVerifier_0(ridT) in s && fact.ValidTokenOut_TokenVerifier(ridT, tokenT) in s &&
	// @ 	jwtT.Abs() == gamma(tokenT)

	if msg, err := jws.Parse(rawToken); err != nil {
		result.err = err
		return
	} else if len(msg.Signatures()) > 1 {
		result.err = /*@ unfolding acc(PkgMem(), _) in @*/ ErrTokenNonCompact
		return
	} else if ademT, err := MkADEMToken(km, msg.Signatures()[0], jwtT /*@, tokenT @*/); err != nil {
		result.err = err
		return
	} else {
		// TODO: (lmeinen) get rid of all the inhale stmts
		// @ unfold iospec.P_TokenVerifier(p, ridT, s)
		// @ unfold iospec.phiRG_TokenVerifier_6(p, ridT, s)
		result.token = ademT
		// Note that we don't have access to the IOSpec past this point
	}
}

// @ preserves n > 0 &&
// @ 	acc(results.SendChannel(), perm(1/(2 * n))) &&
// @ 	results.SendGivenPerm() == SendToken!<loc, n, _!> &&
// @ 	results.SendGotPerm() == PredTrue!<!>
// @ requires SendToken(loc, n, result)
// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires unfolding SendToken(loc, n, result) in unfolding ResultPerm(result) in result.err == nil ==> Abs(result.token) == gamma(tokenT)
// @ requires let isValid := (unfolding SendToken(loc, n, result) in unfolding ResultPerm(result) in result.err == nil) in
// @ 	isValid ==>  iospec.e_ValidTokenOut(p, rid, tokenT)
// @ ensures PredTrue!<!>()
func resultsSend(results chan *TokenVerificationResult, result *TokenVerificationResult /*@, ghost loc *int, ghost n int, ghost p place.Place, ghost rid term.Term, ghost tokenT term.Term @*/) {
	// we use the non-partially-evaluated version of SendToken in the precondition as Gobra doesn't support unfolding ... in stmts otherwise
	// @ unfold SendToken(loc, n, result)
	// @ fold SendToken!<loc, n, _!>(result)
	results <- result
}

// TODO: (lmeinen) Add ValidTokenIn_Verifier stuff
// --> or do we instead add a sort of "exchange" function which takes the ValidTokenOut pred from vfyToken and produces a corresonding In fact
// @ preserves n > 0 &&
// @ 	results.RecvChannel() &&
// @ 	results.RecvGivenPerm() == PredTrue!<!> &&
// @ 	results.RecvGotPerm() == SendToken!<loc, n, _!>
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires PredTrue!<!>()
// @ requires iospec.e_ValidTokenIn(p, rid)
// @ ensures r != nil ==> SendToken(loc, n, r) && unfolding SendToken(loc, n, r) in unfolding ResultPerm(r) in r.err == nil ==> Abs(r.token) == gamma(tokenT)
// @ ensures place.token(pp) && pp == old(iospec.get_e_ValidTokenIn_placeDst(p, rid)) && tokenT == old(iospec.get_e_ValidTokenIn_r1(p, rid))
func resultsRecv(results chan *TokenVerificationResult /*@, ghost loc *int, ghost n int, ghost p place.Place, ghost rid term.Term @*/) (r *TokenVerificationResult /*@, ghost pp place.Place, ghost tokenT term.Term @*/) {
	r = <-results
	/*@
	ghost pp := iospec.get_e_ValidTokenIn_placeDst(p, rid)
	ghost tokenT := iospec.get_e_ValidTokenIn_r1(p, rid)

	ghost {
		inhale place.token(pp)
		if r != nil {
			unfold SendToken!<loc, n, _!>(r)
			fold SendToken(loc, n, r)
			assume unfolding SendToken(loc, n, r) in unfolding ResultPerm(r) in r.err == nil ==> Abs(r.token) == gamma(tokenT)
		}
	}
	@*/
	return r /*@, pp, tokenT @*/
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
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
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

	// @ ghost tTs := seq[term.Term]{}

	/*@
	unfold iospec.P_Verifier(p, ridT, s)
	unfold iospec.phiR_Verifier_2(p, ridT, s)
	l := mset[fact.Fact] { fact.St_Verifier_1(ridT) }
	a := mset[claim.Claim] { }
	r := mset[fact.Fact] { fact.St_Verifier_2(ridT) }
	p = iospec.internBIO_e_ReceiveTokenFinish(p, ridT, l, a, r)
	s = fact.U(l, r, s)
	@*/

	// TODO: (lmeinen) Collect token terms

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
	// @ invariant unfolding TokenList(ts) in
	// @ 	len(ts) == len(tTs) &&
	// @ 	forall i int :: { ts[i] } { tTs[i] } 0 <= i && i < len(tTs) ==> ((unfolding TokenListElem(i, ts[i]) in Abs(ts[i]) == gamma(tTs[i]))) && (fact.ValidTokenIn_Verifier(ridT, tTs[i]) in s)
	// @ invariant len(ts) <= n - threadCount
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
		} else {
			// @ fold PredTrue!<!>()
			// @ unfold iospec.P_Verifier(p, ridT, s)
			// @ unfold iospec.phiRF_Verifier_17(p, ridT, s)
			// @ s = s union mset[fact.Fact] { fact.ValidTokenIn_Verifier(ridT, iospec.get_e_ValidTokenIn_r1(p, ridT)) }
			if result /*@, pp, tokenT @*/ := resultsRecv(results /*@, loc, n, p, ridT @*/); result == nil {
				// @ p = pp

				// All threads have terminated
				break
			} else {
				// @ p = pp

				// @ unfold SendToken(loc, n, result)
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
					// @ assert len(tTs) == len(ts)
					// @ assert Abs(result.token) == gamma(tokenT)
					// @ unfold TokenList(ts)
					// @ unfold ValidToken(result.token)
					ts = append( /*@ perm(1/2), @*/ ts, result.token)
					// @ tTs = tTs ++ seq[term.Term] { tokenT }
					if k, ok := result.token.Token.Get("key"); ok {
						// @ unfold jwt.FieldMem(result.token.Token.Values())
						// @ unfold tokens.KeyMem(k.(tokens.EmbeddedKey))
						km.put(k.(tokens.EmbeddedKey).Key)
						// @ fold acc(tokens.KeyMem(k.(tokens.EmbeddedKey)), _)
						// @ fold acc(jwt.FieldMem(result.token.Token.Values()), _)
					}
					// @ fold acc(ValidToken(result.token), _)
					// @ assume Abs(result.token) == gamma(tokenT)
					// @ assert Abs(ts[len(ts) - 1]) == gamma(tTs[len(tTs) - 1])
					// @ fold TokenListElem(len(ts) - 1, result.token)
					// @ fold TokenList(ts)
				}
			}
		}
	}

	// @ assert iospec.P_Verifier(p, ridT, s)

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	var protected []*ident.AI
	endorsements := []*ADEMToken{}
	// @ fold EndorsementList(endorsements)

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
		// @ unfold acc(ValidToken(t), _)
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
			// @ unfold acc(jwt.FieldMem(emblem.Token.Values()), _)
			// @ unfold acc(tokens.AssMem(protected), _)

			if emblem.Headers.Algorithm() == jwa.NoSignature {
				// TODO: Apply IsUnsignedEmblem rule
				// --> constraints on emblem term: <'emblem', $E>
				// @ assert emblem.Headers.ContentType() == string(consts.EmblemCty) && emblem.Headers.Algorithm() == jwa.NoSignature
				return VerificationResults{
					results:   []consts.VerificationResult{consts.UNSIGNED},
					protected: protected,
				}
			}

			// @ unfold tokens.EmblemValidator.Constraints(emblem.Token)
			// @ fold acc(ValidToken(emblem), _)
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
				// @ fold acc(ValidToken(t), _)
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

	// @ assert iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root /*@, p, s, aiT, oiT, rootKeyT @*/ := verifySignedOrganizational(emblem, endorsements, trustedKeys /*@, p, ridT, s @*/)
	if util.ContainsVerificationResult(vfyResults, consts.INVALID /*@, perm(1/2) @*/) {
		return ResultInvalid()
	}

	var endorsedResults []consts.VerificationResult
	var endorsedBy []string

	if util.ContainsVerificationResult(vfyResults, consts.ORGANIZATIONAL /*@, perm(1/2) @*/) {
		endorsedResults, endorsedBy = verifyEndorsed(emblem, root, endorsements, trustedKeys)
	}

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
