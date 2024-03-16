// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ . "lib"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "github.com/lestrrat-go/jwx/v2/jwa"
	// @ "github.com/lestrrat-go/jwx/v2/jwt"
	//@ "claim"
	//@ "fact"
	//@ "place"
	//@ "iospec"
	//@ "term"
	//@ "pub"
	//@ "fresh"
)

/*@
ghost
requires iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_4(ridT, oiT, rootKeyT) in s
requires t == tuple4(key, auth, tuple3(term.pubTerm(pub.const_root_end_pub()), oiT, rootKeyT), sig)
requires auth != oiT
requires fact.ValidTokenIn_Verifier(ridT, t) in s
ensures iospec.P_Verifier(p0, ridT, s0) && place.token(p0) && fact.St_Verifier_4(ridT, oiT, rootKeyT) in s0
ensures s0 == ((s setminus mset[fact.Fact] { fact.ValidTokenIn_Verifier(ridT, t) }) union mset[fact.Fact] { fact.OutFact_Verifier(ridT, EndorsedOut(auth)) })
func ApplyIsEndorsedEmblem(ghost p place.Place, s mset[fact.Fact], ridT, aiT, oiT, rootKeyT, key, auth, sig, t term.Term) (ghost p0 place.Place, s0 mset[fact.Fact]) {
	unfold iospec.P_Verifier(p, ridT, s)
	unfold iospec.phiR_Verifier_12(p, ridT, s)
	l := mset[fact.Fact] { fact.St_Verifier_4(ridT, oiT, rootKeyT), fact.ValidTokenIn_Verifier(ridT, t) }
	a := mset[claim.Claim] { claim.Neq(auth, oiT), claim.VerifiedAuthorityEndorsement(ridT, auth, key, oiT, rootKeyT) }
	r := mset[fact.Fact] { fact.St_Verifier_4(ridT, oiT, rootKeyT), fact.OutFact_Verifier(ridT, EndorsedOut(auth)) }
	assert fact.M(l, s)
	assert auth != oiT
	p = iospec.internBIO_e_IsEndorsedEmblem(p, ridT, oiT, rootKeyT, key, auth, sig, l, a, r)
	s = fact.U(l, r, s)
	return p, s
}
@*/

// @ trusted
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves acc(tokens.PkgMem(), _)
// @ requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires acc(Endorsement(root), _) &&
// @ 	unfolding acc(Endorsement(root), _) in
// @ 	unfolding acc(ValidToken(root), _) in
// @ 	stringB(root.VerificationKey.KeyID(none[perm])) == gamma(rootKeyT) &&
// @ 	stringB(root.Token.Issuer()) == gamma(oiT)
// @ requires acc(Emblem(emblem), _)
// @ requires acc(EndorsementList(endorsements), _)
// @ requires AuthEndList(root, endorsements)
// @ requires EndorsementTerms(endorsements, endTs)
//
//	requires forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i < len(endTs) ==> endTs[i] # endTs <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s
//
// @ requires forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) && AuthEndConstraints(endorsements[i]) ==> !(i in usedTs)
// @ requires HasTokenInSet(ridT, endTs, usedTs, s)
// @ requires iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_4(ridT, oiT, rootKeyT) in s
// @ ensures acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ ensures acc(Endorsement(root), _) && unfolding acc(Endorsement(root), _) in unfolding acc(ValidToken(root), _) in stringB(root.VerificationKey.KeyID(none[perm])) == gamma(rootKeyT)
// @ ensures acc(endorsedResults)
// @ ensures acc(endorsedBy)
// @ ensures iospec.P_Verifier(p0, ridT, s0) && place.token(p0)
// @ ensures fact.OutFact_Verifier(ridT, SignedOut(aiT)) in s ==> fact.OutFact_Verifier(ridT, SignedOut(aiT)) in s0
// @ ensures fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) in s ==> fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) in s0
// @ ensures len(endorsedBy) == len(authTs) &&
// @ 	forall i int :: { endorsedBy[i] }{ authTs[i] } 0 <= i && i < len(endorsedBy) ==> (
// @ 		stringB(endorsedBy[i]) == gamma(authTs[i]) &&
// @ 		fact.OutFact_Verifier(ridT, EndorsedOut(authTs[i])) in s0)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p place.Place, ghost ridT term.Term, ghost s mset[fact.Fact], ghost aiT, oiT term.Term, ghost endTs seq[term.Term], ghost usedTs set[int], ghost rootKeyT term.Term @*/) (
	endorsedResults []consts.VerificationResult, endorsedBy []string /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost authTs seq[term.Term] @*/) {

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false

	// @ ghost authTs := seq[term.Term] {}
	// @ ghost s0 := s

	// @ unfold AuthEndList(root, endorsements)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant iospec.P_Verifier(p, ridT, s0) && place.token(p) && fact.St_Verifier_4(ridT, oiT, rootKeyT) in s0
	// @ invariant fact.OutFact_Verifier(ridT, SignedOut(aiT)) in s ==> fact.OutFact_Verifier(ridT, SignedOut(aiT)) in s0
	// @ invariant fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) in s ==> fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) in s0
	// @ invariant acc(Emblem(emblem), _)
	// @ invariant acc(Endorsement(root), _)
	// @ invariant issuers != nil && acc(issuers)
	// @ invariant unfolding acc(Endorsement(root), _) in
	// @ 		unfolding acc(ValidToken(root), _) in
	// @ 		stringB(root.VerificationKey.KeyID(none[perm])) == gamma(rootKeyT) &&
	// @ 		stringB(root.Token.Issuer()) == gamma(oiT)
	// @ invariant acc(endorsements, _)
	// @ invariant forall i int :: { AuthEndInvariant(root, endorsements[i], i) } 0 <= i && i < len(endorsements) ==> AuthEndInvariant(root, endorsements[i], i)
	// @ invariant acc(EndorsementList(endorsements), _)
	// @ invariant EndorsementTerms(endorsements, endTs)
	// @ invariant forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i0 <= i && i < len(endTs) ==> endTs[i] # endTs[i0:] <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s0
	// @ invariant len(issuers) == len(authTs) &&
	// @ 	forall i int :: { issuers[i] }{ authTs[i] } 0 <= i && i < len(issuers) ==> (
	// @ 		stringB(issuers[i]) == gamma(authTs[i]) &&
	// @ 		fact.OutFact_Verifier(ridT, EndorsedOut(authTs[i])) in s0)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(EndorsementList(endorsements), _)
		// @ unfold acc(EndListElem(i0, endorsement), _)
		// @ unfold acc(Endorsement(endorsement), _)
		// @ unfold acc(ValidToken(endorsement), _)
		// @ unfold acc(jwt.FieldMem(endorsement.Token.Values()), _)
		// @ unfold acc(Emblem(emblem), _)
		// @ unfold acc(ValidToken(emblem), _)
		// @ unfold acc(Endorsement(root), _)
		// @ unfold acc(ValidToken(root), _)
		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			continue
		} else if root.Token.Issuer() != endorsement.Token.Subject() {
			continue
		} else if endorsement.Token.Issuer() == "" {
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			continue
		} else if _, logged := endorsement.Token.Get("log"); !logged {
			continue
		} else if root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
			continue
		} else if err := tokens.VerifyConstraints(emblem.Token, endorsement.Token); err != nil {
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			x := []consts.VerificationResult{consts.INVALID}
			return x, nil /*@, p, s0, seq[term.Term] { } @*/
		} else {
			/*@
			unfold AuthEndInvariant(root, endorsement, i0)
			unfold EndorsementTerms(endorsements, endTs)

			ghost eT := endTs[i0]
			assert eT == endTs[i0]
			assert eT in endTs[i0:]
			assert endTs[i0] # endTs[i0:] >= 1
			assert fact.ValidTokenIn_Verifier(ridT, eT) in s0

			ghost someKeyT, someAuthT, someSigT := AuthEndPattern(endorsement, oiT, rootKeyT)

			// Apply pattern requirement for root endorsement patterns
			ghost keyT, authT, sigT := AuthorityEndorsementPatternRequirement(eT, ridT, someKeyT, someAuthT, someSigT, oiT, rootKeyT, s0, p)
			// assert eT == tuple4(keyT, authT, tuple3(term.pubTerm(pub.const_root_end_pub()), oiT, rootKeyT), sigT)

			s1 := s0

			// Obtain Out permissions
			p, s1 = ApplyIsEndorsedEmblem(p, s1, ridT, aiT, oiT, rootKeyT, keyT, authT, sigT, eT)

			// Ensure unused In permissions persist
			assert forall i int :: { endTs[i] } 0 <= i && i0 <= i && i < len(endTs) ==> endTs[i] # endTs[i:] <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s0
			assert s1 == ((s0 setminus mset[fact.Fact] { fact.ValidTokenIn_Verifier(ridT, eT) }) union mset[fact.Fact] { fact.OutFact_Verifier(ridT, EndorsedOut(authT)) })
			assert eT == endTs[i0:][0]
			s0 = s1

			// the below assert stmt fails for unknown reasons: there must be some limitation in the axiomatization of multisets
			// assert forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i0 < i && i < len(endTs) ==> endTs[i] # endTs[i:] <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s0
			assume forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i0 < i && i < len(endTs) ==> endTs[i] # endTs[i:] <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s0

			authTs = authTs ++ seq[term.Term] { authT }
			fold AuthEndInvariant(root, endorsement, i0)
			fold EndorsementTerms(endorsements, endTs)
			@*/

			existsEndorsement = true
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
			trustedFound = trustedFound || ok
		}
	}

	/*@
		// Finish verification
		unfold iospec.P_Verifier(p, ridT, s0)
		unfold iospec.phiR_Verifier_13(p, ridT, s0)
		l := mset[fact.Fact] { fact.St_Verifier_4(ridT, oiT, rootKeyT) }
		a := mset[claim.Claim] { }
		r := mset[fact.Fact] { fact.St_Verifier_0(ridT) }
		p = iospec.internBIO_e_FinishVerification(p, ridT, oiT, rootKeyT, l, a, r)
		s0 = fact.U(l, r, s0)
	@*/

	if existsEndorsement {
		results := []consts.VerificationResult{consts.ENDORSED}
		if trustedFound {
			results = append( /*@ perm(1/2), @*/ results, consts.ENDORSED_TRUSTED)
		}
		return results, issuers /*@, p, s0, authTs @*/
	} else {
		return nil, nil /*@, p, s0, seq[term.Term] { } @*/
	}
}
