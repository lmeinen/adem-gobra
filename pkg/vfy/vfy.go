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
// @ ensures acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
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
// @ ensures acc(protected, _) &&
// @ 	forall i int :: 0 <= i && i < len(protected) ==> acc(protected[i].Mem(), _)
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
func DoOutputEndorsed(auth string /*@, ghost p place.Place, ghost rid, t term.Term @*/) (err error /*@, ghost p0 place.Place @*/) {
	log.Print(fmt.Sprintf("('ENDORSED', %s)", auth))
	return nil /*@, p @*/
}

// we mark this function as trusted as it is only meant for demonstration purposes on the usage of I/O permissions
// @ trusted
// @ requires acc(res.results, _) &&
// @ 	acc(res.protected, _) &&
// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
// @ 	acc(res.endorsedBy, _)
// @ requires forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
func (res VerificationResults) Output( /*@ ghost p place.Place, ghost s mset[fact.Fact], ghost rid, ai, oi term.Term, ghost authTs seq[term.Term] @*/ ) (err error /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact] @*/) {
	/*
	   Similar to the input facts in VerifyTokens, we assume the presence of output facts where needed.
	   We do this due to constraints in the Gobra program verifier that lead to significant verification times
	*/

	// @ invariant acc(res.results, _) &&
	// @ 	acc(res.protected, _) &&
	// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
	// @ 	acc(res.endorsedBy, _)
	// @ invariant forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
	for _, r := range res.results /*@ with i0 @*/ {
		switch r {
		case consts.INVALID:
			// TODO
		case consts.UNSIGNED:
			// TODO
		case consts.SIGNED:
			if err /*@, p @*/ = DoOutputSigned(res.protected /*@, p, rid, ai @*/); err != nil {
				log.Print("Could not output security level SIGNED")
				return err /*@, p, s @*/
			}
		case consts.ORGANIZATIONAL:
			if err /*@, p @*/ = DoOutputOrganizational(res.protected, res.issuer /*@, p, rid, ai, oi @*/); err != nil {
				log.Print("Could not output security level ORGANIZATIONAL")
				return err /*@, p, s @*/
			}
		case consts.ENDORSED:
			// @ invariant acc(res.endorsedBy, _)
			for _, iss := range res.endorsedBy /*@ with j0 @*/ {
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
// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
func vfyToken(runId uint64, rawToken []byte, km *keyManager, results chan *TokenVerificationResult /*@, ghost loc *int, ghost threadCount int, ghost vfyWaitGroup *sync.WaitGroup, ghost tokenT term.Term @*/) {
	// @ share threadCount, loc, results, vfyWaitGroup, tokenT
	// @ ghost p@ := GenericPlace()
	// @ ghost rid@ := term.freshTerm(fresh.fr_integer64(runId))
	// @ ghost s := mset[fact.Fact]{}

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
	// @ 				acc(jwt.FieldMem(fields), 1/2))) &&
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

	// @ fold km.Mem()
	options := []jwt.ParseOption{jwt.WithKeyProvider(km)}
	jwtT /*@, p, s @*/, err := jwt.Parse(rawToken /*@, p, rid, s, tokenT @*/, options...)
	if err != nil {
		result.err = err
		return
	}

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
// @ ensures r != nil ==> SendToken(loc, n, r)
func resultsRecv(results chan *TokenVerificationResult /*@, ghost loc *int, ghost n int, ghost p place.Place, ghost rid term.Term @*/) (r *TokenVerificationResult /*@, ghost pp place.Place, ghost tokenT term.Term @*/) {
	return <-results
}

// Verify a slice of ADEM tokens.
// @ requires PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem()
// @ requires acc(&jwt.Custom, 1/2) && acc(jwt.Custom, 1/2) && tokens.CustomFields(jwt.Custom)
// @ requires acc(rawTokens)
// @ requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
// @ requires trustedKeys != nil && trustedKeys.Mem() && jwk.KeySeq(trustedKeys.Elems())
// @ ensures acc(res.results, _) &&
// @ 	acc(res.protected, _) &&
// @ 		(forall i int :: 0 <= i && i < len(res.protected) ==> acc(res.protected[i].Mem(), _)) &&
// @ 	acc(res.endorsedBy, _)
// @ ensures forall i, j int :: { res.results[i] } 0 <= i && i < j && j < len(res.results) ==> res.results[i] != res.results[j]
func VerifyTokens(runId uint64, rawTokens [][]byte, trustedKeys jwk.Set /*@, ghost p place.Place @*/) (res VerificationResults /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost rid, ai, oi term.Term, ghost authTs seq[term.Term] @*/) {
	// @ ghost rid := term.freshTerm(fresh.fr_integer64(runId))
	// @ ghost s := mset[fact.Fact]{}

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
	// preserves place.token(p) && iospec.P_Verifier(p, rid, s)
	preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	requires PkgMem() && roots.PkgMem()
	requires trustedKeys != nil && trustedKeys.Mem() && jwk.KeySeq(trustedKeys.Elems())
	requires len(rawTokens) > 0
	requires acc(rawTokens)
	requires forall i int :: { rawTokens[i] } 0 <= i && i < len(rawTokens) ==> acc(rawTokens[i])
	ensures trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	ensures threadCount == len(rawTokens) && threadCount > 0
	ensures acc(km.lock.LockP(), _) &&
		km.lock.LockInv() == LockInv!<km!>
	ensures results.RecvChannel() &&
		results.RecvGivenPerm() == PredTrue!<!> &&
		results.RecvGotPerm() == SendToken!<loc, threadCount, _!> &&
		results.Token(PredTrue!<!>) &&
		results.ClosureDebt(PredTrue!<!>, 1, 2) &&
		VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)
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
	//  invariant place.token(p) && fact.St_Verifier_1(rid) in s && iospec.P_Verifier(p, rid, s)
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
		go vfyToken(uint64(i), rawToken, km, results /*@, loc, threadCount, vfyWaitGroup, GenericTerm() @*/)
	}

	// @ vfyWaitGroup.SetWaitMode(1/2, 1/2)
	// @ fold VfyWg(vfyWaitGroup, threadCount, results, fractionSeq)

	// Wait until all verification threads obtained a verification key promise.
	km.waitForInit()

	// @ )

	// (lmeinen) 1 - verify the JWT tokens AND that the key chain results in a valid root key only verified keys are used to verify JWT signatures

	/*@
	preserves acc(tokens.PkgMem(), _)
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
	outline (
	@*/

	ts := []*ADEMToken{}
	// @ fold TokenList(ts)

	// @ ghost n := threadCount
	// @ ghost terms := seq[term.Term]{}

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
					// @ unfold TokenList(ts)
					ts = append( /*@ perm(1/2), @*/ ts, result.token)
					// @ unfold ValidToken(result.token)
					if k, ok := result.token.Token.Get("key"); ok {
						// @ unfold jwt.FieldMem(result.token.Token.Values())
						// @ unfold tokens.KeyMem(k.(tokens.EmbeddedKey))
						km.put(k.(tokens.EmbeddedKey).Key)
						// @ fold acc(tokens.KeyMem(k.(tokens.EmbeddedKey)), 1/2)
						// @ fold acc(jwt.FieldMem(result.token.Token.Values()), 1/2)
					}
					// @ fold ValidToken(result.token)

					// @ fold TokenListElem(len(ts) - 1, result.token)
					// @ fold TokenList(ts)
				}
			}
		}
	}

	// @ )

	// (lmeinen) 2 - validate the JWT tokens AND that the required fields are present and valid
	var emblem *ADEMToken
	var protected []*ident.AI
	endorsements := []*ADEMToken{}
	// @ fold TokenList(endorsements)

	// @ ghost embT := GenericTerm()
	// @ ghost endTs := seq[term.Term]{}

	// @ unfold TokenList(ts)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(ts) &&
	// @ 	forall i int :: { ts[i] } 0 <= i && i0 <= i && i < len(ts) ==> TokenListElem(i, ts[i])
	// @ invariant emblem != nil ==> (
	// @ 	ValidToken(emblem) &&
	// @ 	Emblem(emblem))
	// @ invariant TokenList(endorsements)
	// @ invariant unfolding TokenList(endorsements) in forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> unfolding TokenListElem(i, endorsements[i]) in Endorsement(endorsements[i])
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
			}

			// @ unfold tokens.EmblemValidator.Constraints(emblem.Token)
			ass, _ := emblem.Token.Get("ass")
			protected = ass.([]*ident.AI)

			if emblem.Headers.Algorithm() == jwa.NoSignature {
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

	// @ unfold TokenList(endorsements)
	// @ if root != emblem { unfold TokenListElem(rootIdx, root) }
	iss := /*@ unfolding acc(ValidToken(root), 1/2) in @*/ root.Token.Issuer()
	// @ if root != emblem { fold TokenListElem(rootIdx, root) }
	// @ fold TokenList(endorsements)

	// @ assert forall i int :: { vfyResults[i] } 0 <= i && i < len(vfyResults) ==> vfyResults[i] != consts.ENDORSED

	// @ assert forall i, j int :: { endorsedResults[i] } 0 <= i && i < j && j < len(endorsedResults) ==> endorsedResults[i] != endorsedResults[j]

	securityLevels := append( /*@ perm(1/2), @*/ vfyResults, endorsedResults...)
	// @ assert forall i, j int :: { securityLevels[i] } 0 <= i && i < j && j < len(securityLevels) ==> securityLevels[i] != securityLevels[j]

	// (lmeinen) 4 - return results
	return VerificationResults{
		results:    securityLevels,
		issuer:     iss,
		endorsedBy: endorsedBy,
		protected:  protected,
	} /*@, p, s, rid, ai, oi, endorsedByTs @*/
}
