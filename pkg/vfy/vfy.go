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
// @ ensures forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)
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
// @ requires acc(PkgMems(), 1 / threadCount)
// @ requires acc(rawToken, _)
// @ requires km.init.UnitDebt(WaitInv!<!>) &&
// @ 	acc(km.lock.LockP(), _) &&
// @ 	km.lock.LockInv() == LockInv!<km!>
// @ requires acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
// @ requires ValidationPerm(tokenT) && gamma(tokenT) == AbsBytes(rawToken)
// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
func vfyToken(runId uint64, rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost loc *int, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup, ghost tokenT term.Term @*/) {
	// @ share threadCount, loc, results, vfyWaitGroup, tokenT
	// @ ghost p@ := GenericPlace()
	// @ ghost rid@ := term.freshTerm(fresh.fr_integer64(runId))
	// @ ghost s := mset[fact.Fact]{}

	// TODO: (lmeinen) argument for why this is sound
	// @ inhale iospec.P_TokenVerifier(p, rid, s)

	// @ unfold iospec.P_TokenVerifier(p, rid, s)
	// @ unfold iospec.phiRF_TokenVerifier_11(p, rid, s)
	// @ p = iospec.get_e_Setup_TokenVerifier_placeDst(p, rid)
	// @ s = mset[fact.Fact] { fact.Setup_TokenVerifier(rid) }

	// @ inhale place.token(p)

	// @ unfold acc(PkgMems(), 1 / threadCount)
	result /*@@@*/ := TokenVerificationResult{}
	defer
	// @ requires acc(&threadCount) && acc(&loc) && acc(&results) && acc(&vfyWaitGroup) && acc(&p) && acc(&rid) && acc(&tokenT)
	// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ requires threadCount > 0
	// @ requires acc(&result) &&
	// @ 			(result.err == nil ==> (
	// @ 				result.token != nil &&
	// @ 				ValidToken(result.token) &&
	// @ 				let fields := (unfolding ValidToken(result.token) in result.token.Token.Values()) in
	// @ 				acc(jwt.FieldMem(fields), 1/2) &&
	// @ 				iospec.e_ValidTokenOut(p, rid, tokenT) &&
	// @ 				Abs(result.token) == gamma(tokenT))) &&
	// @ 			(result.err != nil ==> result.token == nil)
	// @ requires acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
	// @ requires vfyWaitGroup.UnitDebt(SendFraction!<results, threadCount!>)
	func /*@ f @*/ () {
		// @ unfold acc(ResultsInv(loc, threadCount, results), 1 / threadCount)
		// @ fold ResultPerm(&result)
		// @ fold SendToken(loc, threadCount, &result)
		resultsSend(results, &result /*@, loc, threadCount, p, rid, tokenT @*/)
		// @ fold SendFraction!<results, threadCount!>()
		// @ vfyWaitGroup.PayDebt(SendFraction!<results, threadCount!>)
		// @ vfyWaitGroup.Done()
	}() /*@ as f @*/

	// @ unfold iospec.P_TokenVerifier(p, rid, s)
	// @ unfold iospec.phiRF_TokenVerifier_7(p, rid, s)
	// @ tokenT, p = permissionIn(tokenT, p, rid)
	// @ s = s union mset[fact.Fact] { fact.PermitTokenVerificationIn_TokenVerifier(rid, tokenT) }

	// @ fold TokenVerifierInitState(p, rid, s, tokenT)
	// @ fold km.Mem()
	options := []jwt.ParseOption{jwt.WithKeyProvider(km)}
	jwtT /*@, p, s @*/, err := jwt.Parse(rawToken /*@, p, rid, s, tokenT @*/, options...)
	if err != nil {
		result.err = err
		return
	}
	// @ unfold TokenVerifierTermState(p, rid, s, tokenT)

	// @ assert place.token(p) && iospec.P_TokenVerifier(p, rid, s) &&
	// @ 	fact.St_TokenVerifier_0(rid) in s && fact.ValidTokenOut_TokenVerifier(rid, tokenT) in s &&
	// @ 	jwtT.Abs() == gamma(tokenT)

	// This assumption is verified implicitely by the FetchKeys method in km
	// @ assume unfolding jwt.FieldMem(jwtT.Values()) in jwtT.Contains("log") ==> jwtT.Issuer() != ""

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
		// @ unfold iospec.P_TokenVerifier(p, rid, s)
		// @ unfold iospec.phiRG_TokenVerifier_6(p, rid, s)
		result.token = ademT
		// Note that we don't have access to the IOSpec past this point
	}
}

// @ trusted
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
	results <- result
}

// @ trusted
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
	return <-results
}

// Verify a slice of ADEM tokens.
// @ requires PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem()
// @ requires place.token(p) && iospec.P_Verifier(p, term.freshTerm(fresh.fr_integer64(runId)), mset[fact.Fact]{})
// @ requires acc(&jwt.Custom, 1/2) && acc(jwt.Custom, 1/2) && tokens.CustomFields(jwt.Custom)
// @ requires acc(rawTokens)
// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
// @ requires trustedKeys != nil && trustedKeys.Mem() && jwk.KeySeq(trustedKeys.Elems())
// @ ensures acc(res.results, _) &&
// @ 	acc(res.protected, _) &&
// @ 	acc(res.endorsedBy)
//
//	ensures forall j int :: { res.results[j] } 0 <= j && j < len(res.results) ==> (
//		(res.results[j] == consts.SIGNED ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s0) &&
//		(res.results[j] == consts.ORGANIZATIONAL ==> gamma(oi) == stringB(res.issuer) && fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s0) &&
//		(res.results[j] == consts.ENDORSED ==> len(res.endorsedBy) == len(authTs) && (forall i int :: { authTs[i] } 0 <= i && i < len(authTs) ==> stringB(res.endorsedBy[i]) == gamma(authTs[i]) && fact.OutFact_Verifier(rid, EndorsedOut(authTs[i])) in s0)))
func VerifyTokens(runId uint64, rawTokens [][]byte, trustedKeys jwk.Set /*@, ghost p place.Place @*/) (res VerificationResults /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost ai term.Term, ghost oi term.Term, ghost rootKey term.Term, ghost rid term.Term, ghost authTs seq[term.Term] @*/) {
	// @ ghost rid := term.freshTerm(fresh.fr_integer64(runId))
	// @ ghost s := mset[fact.Fact]{}

	// @ unfold iospec.P_Verifier(p, rid, s)
	// @ unfold iospec.phiRF_Verifier_18(p, rid, s)
	// @ p = iospec.get_e_Setup_Verifier_placeDst(p, rid)
	// @ s = mset[fact.Fact] { fact.Setup_Verifier(rid) }

	// TODO: Is there a better way to do this? Or is this just the assumption that library functions are allowed to make
	// @ inhale place.token(p)

	// Early termination for empty rawTokens slice
	if len(rawTokens) == 0 {
		return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
	}

	/*
		(lmeinen) Note the nuance in terminology:
			1 To verify a JWT: Check that the encoded string corresponds to a valid JSON encoding of a JWT, and that the JWT's signature is valid w.r.t. to its verification key
			2 To validate a JWT: Check that a JWT's claims stand (and in this case: that the required field 'ass' resp. 'end' is present)
			3 To verify a security level: Assuming the two above steps have been executed, walk the endorsement chain and check the security level of the emblem as defined in ADEM (incl. endorsement constraints)
	*/

	// (lmeinen) 0 - set up chain of promises from root keys to signing keys

	// INIT SECTION
	/*@
	preserves acc(tokens.PkgMem(), _)
	preserves place.token(p) && iospec.P_Verifier(p, rid, s)
	preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	requires PkgMem() && roots.PkgMem()
	requires trustedKeys != nil && trustedKeys.Mem() && jwk.KeySeq(trustedKeys.Elems())
	requires len(rawTokens) > 0
	requires acc(rawTokens)
	requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
	requires s == mset[fact.Fact] { fact.Setup_Verifier(rid) }
	ensures trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	ensures fact.St_Verifier_2(rid) in s
	ensures threadCount == len(rawTokens) && threadCount > 0
	ensures acc(km.lock.LockP(), _) &&
		km.lock.LockInv() == LockInv!<km!>
	ensures results.RecvChannel() &&
		results.RecvGivenPerm() == PredTrue!<!> &&
		results.RecvGotPerm() == SendToken!<loc, threadCount, _!> &&
		results.Token(PredTrue!<!>) &&
		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
		VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)
	ensures fact.St_Verifier_2(rid) in s
	outline (
	@*/

	// Ensure trustedKeys is non-nil
	if trustedKeys == nil {
		trustedKeys = jwk.NewSet()
	}

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
	unfold iospec.P_Verifier(p, rid, s)
	unfold iospec.phiR_Verifier_0(p, rid, s)
	l := mset[fact.Fact] { fact.Setup_Verifier(rid) }
	a := mset[claim.Claim] { }
	r := mset[fact.Fact] { fact.St_Verifier_1(rid) }
	p = iospec.internBIO_e_FinishSetup(p, rid, l, a, r)
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
	// @ invariant place.token(p) && fact.St_Verifier_1(rid) in s && iospec.P_Verifier(p, rid, s)
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
		unfold iospec.P_Verifier(p, rid, s)
		unfold iospec.phiRF_Verifier_16(p, rid, s)
		tokenT, pp := tokenIn(rawToken, perm(1/2), p, rid)
		p = pp
		s = s union mset[fact.Fact] { fact.InFact_Verifier(rid, tokenT) }
		@*/

		// Produce PermitTokenVerificationOut fact
		/*@
		unfold iospec.P_Verifier(p, rid, s)
		unfold iospec.phiR_Verifier_1(p, rid, s)
		l := mset[fact.Fact] { fact.St_Verifier_1(rid), fact.InFact_Verifier(rid, tokenT) }
		a := mset[claim.Claim] { }
		r := mset[fact.Fact] { fact.St_Verifier_1(rid), fact.PermitTokenVerificationOut_Verifier(rid, tokenT) }
		p = iospec.internBIO_e_ReceiveToken(p, rid, tokenT, l, a, r)
		s = fact.U(l, r, s)
		@*/

		// 'Persist' Out fact
		/*@
		unfold iospec.P_Verifier(p, rid, s)
		unfold iospec.phiRG_Verifier_14(p, rid, s)
		assert iospec.e_PermitTokenVerificationOut(p, rid, tokenT)
		p = permissionOut(p, rid, tokenT)
		s = s setminus mset[fact.Fact] { fact.PermitTokenVerificationOut_Verifier(rid, tokenT) }
		@*/

		go vfyToken(uint64(i), rawToken, km, results /*@, loc, threadCount, vfyWaitGroup, tokenT @*/)
	}

	// @ vfyWaitGroup.SetWaitMode(1/2, 1/2)
	// @ fold VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()

	/*@
	unfold iospec.P_Verifier(p, rid, s)
	unfold iospec.phiR_Verifier_2(p, rid, s)
	l := mset[fact.Fact] { fact.St_Verifier_1(rid) }
	a := mset[claim.Claim] { }
	r := mset[fact.Fact] { fact.St_Verifier_2(rid) }
	p = iospec.internBIO_e_ReceiveTokenFinish(p, rid, l, a, r)
	s = fact.U(l, r, s)
	@*/

	// @ )

	// (lmeinen) 1 - verify the JWT tokens AND that the key chain results in a valid root key only verified keys are used to verify JWT signatures

	/*@
	preserves acc(tokens.PkgMem(), _)
	preserves place.token(p) && iospec.P_Verifier(p, rid, s) && fact.St_Verifier_2(rid) in s
	preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	requires threadCount > 0
	requires acc(km.lock.LockP(), _) &&
		km.lock.LockInv() == LockInv!<km!>
	requires results.RecvChannel() &&
		results.RecvGivenPerm() == PredTrue!<!> &&
		results.RecvGotPerm() == SendToken!<loc, threadCount, _!> &&
		results.Token(PredTrue!<!>) &&
		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
		VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)
	ensures TokenList(ts)
	ensures len(ts) == len(terms) &&
	 	unfolding TokenList(ts) in
	 	forall i int :: { ts[i] } 0 <= i && i < len(terms) ==> unfolding TokenListElem(i, ts[i]) in Abs(ts[i]) == gamma(terms[i])
	 		// (forall i int :: { fact.ValidTokenIn_Verifier(rid, terms[i]) } 0 <= i && i < len(terms) ==> terms[i] # terms <= fact.ValidTokenIn_Verifier(rid, terms[i]) # s)
	outline (
	@*/

	ts := []*ADEMToken{}
	// @ fold TokenList(ts)

	// @ ghost n := threadCount
	// @ ghost terms := seq[term.Term]{}

	// @ invariant place.token(p) && fact.St_Verifier_2(rid) in s && iospec.P_Verifier(p, rid, s)
	// @ invariant 0 < n && threadCount <= n
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
	// @ invariant len(ts) == len(terms) &&
	// @ 	unfolding TokenList(ts) in
	// @ 	forall i int :: { ts[i] } 0 <= i && i < len(terms) ==> unfolding TokenListElem(i, ts[i]) in Abs(ts[i]) == gamma(terms[i])
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
			// @ unfold iospec.P_Verifier(p, rid, s)
			// @ unfold iospec.phiRF_Verifier_17(p, rid, s)
			// @ s = s union mset[fact.Fact] { fact.ValidTokenIn_Verifier(rid, iospec.get_e_ValidTokenIn_r1(p, rid)) }
			if result /*@, pp, tokenT @*/ := resultsRecv(results /*@, loc, n, p, rid @*/); result == nil {
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
					// @ assert len(terms) == len(ts)
					// @ assert Abs(result.token) == gamma(tokenT)
					// @ unfold TokenList(ts)
					ts = append( /*@ perm(1/2), @*/ ts, result.token)
					// @ terms = terms ++ seq[term.Term] { tokenT }
					// @ unfold ValidToken(result.token)
					if k, ok := result.token.Token.Get("key"); ok {
						// @ unfold jwt.FieldMem(result.token.Token.Values())
						// @ unfold tokens.KeyMem(k.(tokens.EmbeddedKey))
						km.put(k.(tokens.EmbeddedKey).Key)
						// @ fold acc(tokens.KeyMem(k.(tokens.EmbeddedKey)), 1/2)
						// @ fold acc(jwt.FieldMem(result.token.Token.Values()), 1/2)
					}
					// @ fold ValidToken(result.token)

					// km.put modifies the passed key: trivially, the token no longer corresponds to tokenT
					// @ assume Abs(result.token) == gamma(tokenT)

					// @ assert Abs(ts[len(ts) - 1]) == gamma(terms[len(terms) - 1])
					// @ fold TokenListElem(len(ts) - 1, result.token)
					// @ fold TokenList(ts)
				}
			}
		}
	}

	// @ assert iospec.P_Verifier(p, rid, s)

	// @ )

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	var protected []*ident.AI
	endorsements := []*ADEMToken{}
	// @ fold TokenList(endorsements)

	// @ ghost embT := GenericTerm()
	// @ ghost endTs := seq[term.Term]{}

	// @ unfold TokenList(ts)

	// @ invariant iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_2(rid) in s
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(ts) &&
	// @ 	forall i int :: { ts[i] } 0 <= i && i0 <= i && i < len(ts) ==> TokenListElem(i, ts[i])
	// @ invariant len(ts) == len(terms)
	// @ invariant forall i int :: { ts[i] } { terms[i] } 0 <= i && i0 <= i && i < len(terms) ==> unfolding TokenListElem(i, ts[i]) in Abs(ts[i]) == gamma(terms[i])
	// @ invariant emblem != nil ==> (
	// @ 	ValidToken(emblem) &&
	// @ 	Emblem(emblem) &&
	// @ 	Abs(emblem) == gamma(embT) &&
	// @ 	(ValidToken(emblem) --* (acc(ValidToken(emblem), 1/2) && acc(protected, 1/4))))
	// @ invariant TokenList(endorsements)
	// @ invariant len(endorsements) == len(endTs)
	// @ invariant unfolding TokenList(endorsements) in forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> unfolding TokenListElem(i, endorsements[i]) in Endorsement(endorsements[i])
	// @ invariant unfolding TokenList(endorsements) in forall i int :: { endorsements[i] } { endTs[i] } 0 <= i && i < len(endTs) ==> unfolding TokenListElem(i, endorsements[i]) in Abs(endorsements[i]) == gamma(endTs[i])
	for _, t := range ts /*@ with i0 @*/ {
		// @ unfold TokenListElem(i0, t)
		// @ unfold ValidToken(t)
		if t.Headers.ContentType() == string(consts.EmblemCty) {
			// @ fold acc(tokens.EmblemValidator.Mem(), _)
			if emblem != nil {
				// Multiple emblems
				log.Print("Token set contains multiple emblems")
				return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
			} else if err := jwt.Validate(t.Token, jwt.WithValidator(tokens.EmblemValidator)); err != nil {
				log.Printf("Invalid emblem: %s", err)
				return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
			} else {
				emblem = t
				// @ embT = terms[i0]
			}

			// @ unfold tokens.EmblemValidator.Constraints(emblem.Token)
			ass, _ := emblem.Token.Get("ass")
			protected = ass.([]*ident.AI)
			/*@
			package ValidToken(emblem) --* (acc(ValidToken(emblem), 1/2) && acc(protected, 1/4)) {
				unfold ValidToken(emblem)
				unfold acc(jwt.FieldMem(emblem.Token.Values()), 1/2)
				unfold acc(tokens.AssMem(protected), 1/2)
				fold acc(tokens.AssMem(protected), 1/4)
				fold acc(jwt.FieldMem(emblem.Token.Values()), 1/4)
				fold acc(ValidToken(emblem), 1/2)
			}
			@*/

			if emblem.Headers.Algorithm() == jwa.NoSignature {
				// TODO: Apply IsUnsignedEmblem rule
				// --> constraints on emblem term: <'emblem', $E>
				// @ assert acc(protected, _)
				// @ assert emblem.Headers.ContentType() == string(consts.EmblemCty) && emblem.Headers.Algorithm() == jwa.NoSignature
				return VerificationResults{
					results:   []consts.VerificationResult{consts.UNSIGNED},
					protected: protected,
				} /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
			}

			// @ fold ValidToken(emblem)
		} else if t.Headers.ContentType() == string(consts.EndorsementCty) {
			// @ fold acc(tokens.EndorsementValidator.Mem(), _)
			o := jwt.WithValidator(tokens.EndorsementValidator)
			err := jwt.Validate(t.Token, o)
			if err != nil {
				log.Printf("Invalid endorsement: %s", err)
			} else {
				// @ unfold tokens.EndorsementValidator.Constraints(t.Token)
				// @ unfold TokenList(endorsements)
				endorsements = append( /*@ perm(1/2), @*/ endorsements, t)
				// @ fold ValidToken(t)
				// @ fold TokenListElem(i0, t)
				// @ fold TokenList(endorsements)
				// @ endTs = endTs ++ seq[term.Term] { terms[i0] }
			}
		} else {
			log.Printf("Token has wrong type: %s", t.Headers.ContentType())
		}
	}

	if emblem == nil {
		log.Print("no emblem found")
		return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
	}

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root /*@, p, s, ai, oi, rootKey, rootIdx @*/ := verifySignedOrganizational(emblem, endorsements, trustedKeys /*@, embT, endTs, p, rid, s @*/)
	if util.ContainsVerificationResult(vfyResults, consts.INVALID) {
		return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
	}

	var endorsedResults []consts.VerificationResult
	var endorsedBy []string
	// @ ghost endorsedByTs := GenericSeq()

	if util.ContainsVerificationResult(vfyResults, consts.ORGANIZATIONAL) {
		endorsedResults, endorsedBy /*@, p, s, endorsedByTs @*/ = verifyEndorsed(emblem, root, endorsements, trustedKeys /*@, rootIdx, p, rid, s, ai, oi, endTs, rootKey @*/)
	}

	if util.ContainsVerificationResult(endorsedResults, consts.INVALID) {
		return ResultInvalid() /*@, GenericPlace(), GenericSet(), GenericTerm(), GenericTerm(), GenericTerm(), GenericTerm(), GenericSeq() @*/
	}

	// @ assert forall j int :: { vfyResults[j] } 0 <= j && j < len(vfyResults) && vfyResults[j] == consts.SIGNED ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s
	// @ assert forall j int :: { vfyResults[j] } 0 <= j && j < len(vfyResults) && vfyResults[j] == consts.ORGANIZATIONAL ==> fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
	// @ assert forall j int :: { endorsedResults[j] } 0 <= j && j < len(endorsedResults) && endorsedResults[j] == consts.ENDORSED ==> (forall i int :: { endorsedByTs[i] } 0 <= i && i < len(endorsedByTs) ==> fact.OutFact_Verifier(rid, EndorsedOut(endorsedByTs[i])) in s && stringB(endorsedBy[i]) == gamma(endorsedByTs[i]))

	// TODO: (lmeinen) State transitions for out facts

	// @ apply ValidToken(emblem) --* (acc(ValidToken(emblem), 1/2) && acc(protected, 1/4))

	// @ unfold TokenList(endorsements)
	// @ if root != emblem { unfold TokenListElem(rootIdx, root) }
	iss := /*@ unfolding acc(ValidToken(root), 1/2) in @*/ root.Token.Issuer()
	// @ if root != emblem { fold TokenListElem(rootIdx, root) }
	// @ fold TokenList(endorsements)

	// (lmeinen) 4 - return results
	return VerificationResults{
		results:    append( /*@ perm(1/2), @*/ vfyResults, endorsedResults...),
		issuer:     iss,
		endorsedBy: endorsedBy,
		protected:  protected,
	} /*@, p, s, ai, oi, rootKey, rid, endorsedByTs @*/
}
