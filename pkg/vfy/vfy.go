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
// @ ensures len(res.results) == 1 && res.results[0] == consts.INVALID
// @ ensures len(res.protected) == 0
// @ ensures len(res.endorsedBy) == 0
func ResultInvalid() (res VerificationResults) {
	return VerificationResults{results: []consts.VerificationResult{consts.INVALID}}
}

// @ trusted
// @ requires acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
// @ requires place.token(p) && iospec.e_OutFact(p, rid, SignedOut(ai)) && gamma(ai) == ident.AbsAI(protected)
// @ ensures acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
// @ ensures err == nil ==> place.token(p0) && p0 == old(iospec.get_e_OutFact_placeDst(p, rid, SignedOut(ai)))
func DoOutputSigned(protected []*ident.AI /*@, ghost p place.Place, ghost rid term.Term, ghost ai term.Term @*/) (err error /*@, ghost p0 place.Place @*/) {
	assets := make([]string, 0, len(protected))
	if len(protected) > 0 {
		for _, ass := range protected {
			assets = append( /*@ perm(1/2), @*/ assets, ass.String())
		}
	}
	log.Print(fmt.Sprintf("('SIGNED', <%s>)", strings.Join(assets, ", ")))
	return nil /*@, p @*/
}

// @ trusted
// @ requires acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
// @ requires place.token(p) && iospec.e_OutFact(p, rid, OrganizationalOut(ai, oi)) && gamma(ai) == ident.AbsAI(protected) && gamma(oi) == stringB(iss)
// @ ensures acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
// @ ensures err == nil ==> place.token(p0) && p0 == old(iospec.get_e_OutFact_placeDst(p, rid, OrganizationalOut(ai, oi)))
func DoOutputOrganizational(protected []*ident.AI, iss string /*@, ghost p place.Place, ghost rid, ai, oi Term @*/) (err error /*@, ghost p0 place.Place @*/) {
	assets := make([]string, 0, len(protected))
	if len(protected) > 0 {
		for _, ass := range protected {
			assets = append( /*@ perm(1/2), @*/ assets, ass.String())
		}
	}
	log.Print(fmt.Sprintf("('ORGANIZATIONAL', <%s>, %s)", strings.Join(assets, ", "), iss))
	return nil /*@, p @*/
}

// @ trusted
// @ requires place.token(p) && iospec.e_OutFact(p, rid, EndorsedOut(t)) && gamma(t) == stringB(auth)
// @ ensures err == nil ==> place.token(p0) && p0 == old(iospec.get_e_OutFact_placeDst(p, rid, EndorsedOut(t)))
func DoOutputEndorsed(auth string /*@, ghost p place.Place, ghost rid, t term.Term @*/) (err error /*@, ghost p0 place.Place @*/) {
	log.Print(fmt.Sprintf("('ENDORSED', %s)", auth))
	return nil /*@, p @*/
}

// we mark this function as trusted as it is only meant for demonstration purposes on the usage of I/O permissions
// @ trusted
// @ requires place.token(p) && iospec.P_Verifier(p, rid, s)
// @ requires acc(res.results, _) &&
// @ 	acc(res.protected, _) &&
// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
// @ 	acc(res.endorsedBy, _)
// @ requires forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
// @ requires (exists j int :: { res.results[j] } 0 <= j && j < len(res.results) && res.results[j] == consts.SIGNED) ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s && ident.AbsAI(res.protected) == gamma(ai)
// @ requires (exists j int :: { res.results[j] } 0 <= j && j < len(res.results) && res.results[j] == consts.ORGANIZATIONAL) ==> fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s && ident.AbsAI(res.protected) == gamma(ai) && stringB(res.issuer) == gamma(oi)
// @ requires len(res.endorsedBy) == len(authTs) &&
// @ 	(forall i int :: { authTs[i] } 0 <= i && i < len(authTs) ==> fact.OutFact_Verifier(rid, EndorsedOut(authTs[i])) in s && stringB(res.endorsedBy[i]) == gamma(authTs[i]))
// @ ensures err == nil ==> place.token(p0) && iospec.P_Verifier(p0, rid, s0)
func (res VerificationResults) Output( /*@ ghost p place.Place, ghost s mset[fact.Fact], ghost rid, ai, oi term.Term, ghost authTs seq[term.Term] @*/ ) (err error /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact] @*/) {
	/*
	   Similar to the input facts in VerifyTokens, we assume the presence of output facts where needed.
	   We do this due to constraints in the Gobra program verifier that lead to significant verification times
	*/

	// @ invariant place.token(p) && iospec.P_Verifier(p, rid, s)
	// @ invariant acc(res.results, _) &&
	// @ 	acc(res.protected, _) &&
	// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
	// @ 	acc(res.endorsedBy, _)
	// @ invariant forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
	// @ invariant (exists i int :: { res.results[i] == consts.SIGNED } 0 <= i && i0 <= i && i < len(res.results) && res.results[i] == consts.SIGNED) ==> ident.AbsAI(res.protected) == gamma(ai)
	// @ invariant (exists i int :: { res.results[i] == consts.ORGANIZATIONAL } 0 <= i && i0 <= i && i < len(res.results) && res.results[i] == consts.ORGANIZATIONAL) ==> ident.AbsAI(res.protected) == gamma(ai) && stringB(res.issuer) == gamma(oi)
	// @ invariant (exists i int :: { res.results[i] == consts.ENDORSED } 0 <= i && i0 <= i && i < len(res.results) && res.results[i] == consts.ENDORSED) ==> len(res.endorsedBy) == len(authTs) &&
	// @ 	(forall i int :: { authTs[i] } 0 <= i && i < len(authTs) ==> stringB(res.endorsedBy[i]) == gamma(authTs[i]))
	for _, r := range res.results /*@ with i0 @*/ {
		switch r {
		case consts.INVALID:
			// TODO
		case consts.UNSIGNED:
			// TODO
		case consts.SIGNED:
			// @ assume fact.OutFact_Verifier(rid, SignedOut(ai)) in s
			// @ s = GetOutPerm(p, s, rid, SignedOut(ai))
			if err /*@, p @*/ = DoOutputSigned(res.protected /*@, p, rid, ai @*/); err != nil {
				log.Print("Could not output security level SIGNED")
				return err /*@, p, s @*/
			}
		case consts.ORGANIZATIONAL:
			// @ assume fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
			// @ s = GetOutPerm(p, s, rid, OrganizationalOut(ai, oi))
			if err /*@, p @*/ = DoOutputOrganizational(res.protected, res.issuer /*@, p, rid, ai, oi @*/); err != nil {
				log.Print("Could not output security level ORGANIZATIONAL")
				return err /*@, p, s @*/
			}
		case consts.ENDORSED:
			// @ invariant place.token(p) && iospec.P_Verifier(p, rid, s)
			// @ invariant acc(res.endorsedBy, _)
			// @ invariant len(res.endorsedBy) == len(authTs) &&
			// @ 	(forall i int :: { gamma(authTs[i]) } 0 <= i && i < len(authTs) ==> stringB(res.endorsedBy[i]) == gamma(authTs[i]))
			for _, iss := range res.endorsedBy /*@ with j0 @*/ {
				// Similar to in facts, we assume the presence of a required Out fact due to restrictions in mset multiplicity
				// @ assume fact.OutFact_Verifier(rid, EndorsedOut(authTs[j0])) in s
				// @ s = GetOutPerm(p, s, rid, EndorsedOut(authTs[j0]))
				if err /*@, p @*/ = DoOutputEndorsed(iss /*@, p, rid, authTs[j0] @*/); err != nil {
					log.Print("Could not output security level ENDORSED")
					return err /*@, p, s @*/
				}
			}
		default:
			// Do nothing
		}
	}
	return nil /*@, p, s @*/
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
	// @ s = mset[fact.Fact] { fact.Setup_TokenVerifier(rid), fact.PermitTokenVerificationIn_TokenVerifier(rid, tokenT) }

	// @ fold km.Mem()
	options := []jwt.ParseOption{jwt.WithKeyProvider(km)}
	jwtT /*@, p, s @*/, err := jwt.Parse(rawToken /*@, p, rid, s, tokenT @*/, options...)
	if err != nil {
		result.err = err
		return
	}

	// @ assert place.token(p) && iospec.P_TokenVerifier(p, rid, s) &&
	// @ 	s == mset[fact.Fact] { fact.St_TokenVerifier_0(rid), fact.ValidTokenOut_TokenVerifier(rid, tokenT) } &&
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
// @ ensures place.token(p0) && iospec.P_Verifier(p0, rid, s0)
// @ ensures acc(res.results, _) &&
// @ 	acc(res.protected, _) &&
// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
// @ 	acc(res.endorsedBy, _)
// @ ensures forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
// @ ensures (exists j int :: { res.results[j] } 0 <= j && j < len(res.results) && res.results[j] == consts.SIGNED) ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s0 && ident.AbsAI(res.protected) == gamma(ai)
// @ ensures (exists j int :: { res.results[j] } 0 <= j && j < len(res.results) && res.results[j] == consts.ORGANIZATIONAL) ==> fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s0 && ident.AbsAI(res.protected) == gamma(ai) && stringB(res.issuer) == gamma(oi)
// @ ensures len(res.endorsedBy) == len(authTs) &&
// @ 	(forall i int :: { authTs[i] } 0 <= i && i < len(authTs) ==> fact.OutFact_Verifier(rid, EndorsedOut(authTs[i])) in s0 && stringB(res.endorsedBy[i]) == gamma(authTs[i]))
func VerifyTokens(runId uint64, rawTokens [][]byte, trustedKeys jwk.Set /*@, ghost p place.Place @*/) (res VerificationResults /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost rid, ai, oi term.Term, ghost authTs seq[term.Term] @*/) {
	// @ ghost rid := term.freshTerm(fresh.fr_integer64(runId))
	// @ ghost s := mset[fact.Fact]{}

	// @ unfold iospec.P_Verifier(p, rid, s)
	// @ unfold iospec.phiRF_Verifier_18(p, rid, s)
	// @ p = iospec.get_e_Setup_Verifier_placeDst(p, rid)
	// @ s = mset[fact.Fact] { fact.Setup_Verifier(rid) }

	// @ inhale place.token(p)

	// Early termination for empty rawTokens slice
	if len(rawTokens) == 0 {
		return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
	}

	/*
		(lmeinen) Note the nuance in terminology:
			1 To verify a JWT: Check that the encoded string corresponds to a valid JSON encoding of a JWT, and that the JWT's signature is valid w.r.t. to its verification key
			2 To validate a JWT: Check that a JWT's claims stand (and in this case: that the required field 'ass' resp. 'end' is present)
			3 To verify a security level: Assuming the two above steps have been executed, walk the endorsement chain and check the security level of the emblem as defined in ADEM (incl. endorsement constraints)
	*/

	// (lmeinen) 0 - set up chain of promises from root keys to signing keys

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
	// @ 	Abs(emblem) == gamma(embT))
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
				return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
			} else if err := jwt.Validate(t.Token, jwt.WithValidator(tokens.EmblemValidator)); err != nil {
				log.Printf("Invalid emblem: %s", err)
				return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
			} else {
				emblem = t
				// @ embT = terms[i0]
			}

			// @ unfold tokens.EmblemValidator.Constraints(emblem.Token)
			ass, _ := emblem.Token.Get("ass")
			protected = ass.([]*ident.AI)

			if emblem.Headers.Algorithm() == jwa.NoSignature {
				// TODO: Apply IsUnsignedEmblem rule
				// --> constraints on emblem term: <'emblem', $E>
				// @ assert acc(protected, _)
				// @ assert emblem.Headers.ContentType() == string(consts.EmblemCty) && emblem.Headers.Algorithm() == jwa.NoSignature
				return VerificationResults{
					results:   []consts.VerificationResult{consts.UNSIGNED},
					protected: protected,
				} /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
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
		return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
	}

	// (lmeinen) 3 - verify/determine the security levels of the emblem
	vfyResults, root /*@, p, s, ai, oi, rootKey, rootIdx @*/ := verifySignedOrganizational(emblem, endorsements, trustedKeys /*@, embT, endTs, p, rid, s @*/)
	// @ assert forall i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) ==> vfyResults[i] in seq[consts.VerificationResult] { consts.INVALID, consts.SIGNED, consts.SIGNED_TRUSTED, consts.ORGANIZATIONAL, consts.ORGANIZATIONAL_TRUSTED }
	// @ assert forall i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) ==> vfyResults[i] != consts.ENDORSED
	// @ assert forall i, j int :: 0 <= i && i < j && j < len(vfyResults) ==> vfyResults[i] != vfyResults[j]
	if util.ContainsVerificationResult(vfyResults, consts.INVALID) {
		return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
	}

	var endorsedResults []consts.VerificationResult
	var endorsedBy []string
	// @ ghost endorsedByTs := seq[term.Term] {}

	if util.ContainsVerificationResult(vfyResults, consts.ORGANIZATIONAL) {
		endorsedResults, endorsedBy /*@, p, s, endorsedByTs @*/ = verifyEndorsed(emblem, root, endorsements, trustedKeys /*@, rootIdx, p, rid, s, ai, oi, endTs, rootKey @*/)
	}

	if util.ContainsVerificationResult(endorsedResults, consts.INVALID) {
		return ResultInvalid() /*@, p, s, rid, GenericTerm(), GenericTerm(), seq[term.Term] {} @*/
	}

	// @ unfold acc(ValidToken(emblem), 1/2)
	// @ unfold acc(jwt.FieldMem(emblem.Token.Values()), 1/4)
	ass, _ := emblem.Token.Get("ass")
	protected = ass.([]*ident.AI)
	// @ unfold acc(tokens.AssMem(protected), 1/4)
	// @ assert ident.AbsAI(protected) == gamma(ai)

	// @ unfold TokenList(endorsements)
	// @ if root != emblem { unfold TokenListElem(rootIdx, root) }
	iss := /*@ unfolding acc(ValidToken(root), 1/2) in @*/ root.Token.Issuer()
	// @ if root != emblem { fold TokenListElem(rootIdx, root) }
	// @ fold TokenList(endorsements)

	// @ assert (exists i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) && vfyResults[i] == consts.SIGNED) ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s
	// @ assert (exists i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) && vfyResults[i] == consts.ORGANIZATIONAL) ==> fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
	// @ assert forall i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) ==> vfyResults[i] != consts.ENDORSED

	// @ assert forall i, j int :: { endorsedResults[i] } 0 <= i && i < j && j < len(endorsedResults) ==> endorsedResults[i] != endorsedResults[j]
	// @ assert len(endorsedByTs) == len(endorsedBy)
	// @ assert forall i int :: { endorsedByTs[i] } 0 <= i && i < len(endorsedByTs) ==> fact.OutFact_Verifier(rid, EndorsedOut(endorsedByTs[i])) in s && stringB(endorsedBy[i]) == gamma(endorsedByTs[i])

	securityLevels := append( /*@ perm(1/2), @*/ vfyResults, endorsedResults...)
	// @ assert (exists i int :: { securityLevels[i] } 0 <= i && i < len(securityLevels) && securityLevels[i] == consts.SIGNED) ==> fact.OutFact_Verifier(rid, SignedOut(ai)) in s
	// @ assert (exists i int :: { securityLevels[i] } 0 <= i && i < len(securityLevels) && securityLevels[i] == consts.ORGANIZATIONAL) ==> fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
	// @ assert forall i, j int :: { securityLevels[i] } 0 <= i && i < j && j < len(securityLevels) ==> securityLevels[i] != securityLevels[j]

	// (lmeinen) 4 - return results
	return VerificationResults{
		results:    securityLevels,
		issuer:     iss,
		endorsedBy: endorsedBy,
		protected:  protected,
	} /*@, p, s, rid, ai, oi, endorsedByTs @*/
}
