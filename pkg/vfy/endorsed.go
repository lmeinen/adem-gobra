// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "github.com/adem-wg/adem-proto/pkg/ident"
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

// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves ValidToken(emblem) && Emblem(emblem) &&
// @ 	unfolding ValidToken(emblem) in
// @ 	unfolding acc(jwt.FieldMem(emblem.Token.Values()), 1/8) in
// @ 	let ass := emblem.Token.PureGet("ass").([]*ident.AI) in
// @ 	unfolding acc(tokens.AssMem(ass), 1/8) in
// @ 	ident.AbsAI(ass) == gamma(ai)
// @ preserves TokenList(endorsements)
// @ preserves len(endorsements) == len(terms)
// @ preserves unfolding TokenList(endorsements) in
// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
// @ 		unfolding TokenListElem(i, endorsements[i]) in
// @ 		Endorsement(endorsements[i]) &&
// @ 		Abs(endorsements[i]) == gamma(terms[i]))
// @ preserves unfolding TokenList(endorsements) in
// @ 	0 <= rootIdx && rootIdx < len(endorsements) &&
// @ 	endorsements[rootIdx] == root &&
// @ 	unfolding TokenListElem(rootIdx, root) in
// @ 	unfolding ValidToken(root) in
// @ 	root.Token.Contains("key") &&
// @ 	root.Token.PureKeyID() != root.VerificationKey.KeyID(none[perm]) &&
// @ 	stringB(root.VerificationKey.KeyID(none[perm])) == gamma(rootKey) &&
// @ 	stringB(root.Token.Issuer()) == gamma(oi) &&
// @ 	unfolding ValidToken(emblem) in
// @ 	(root.Token.Issuer() == emblem.Token.Issuer())
// @ preserves unfolding TokenList(endorsements) in
// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) && i != rootIdx ==> (
// @ 		unfolding TokenListElem(i, endorsements[i]) in
// @ 		unfolding TokenListElem(rootIdx, root) in
// @ 		endorsements[i].Endorses(root) ==> (
// @ 			unfolding ValidToken(endorsements[i]) in
// @ 			unfolding ValidToken(root) in
// @ 			root.Token.Issuer() != endorsements[i].Token.Issuer() ||
// @ 			!endorsements[i].Token.PureGet("end").(bool)))
// @ requires iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_4(rid, oi, rootKey) in s
// @ requires fact.OutFact_Verifier(rid, SignedOut(ai)) in s
// @ requires fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
// @ ensures acc(endorsedResults)
// @ ensures len(endorsedResults) <= 2 &&
// @ 	(forall i int :: { endorsedResults[i] } 0 <= i && i < len(endorsedResults) ==> endorsedResults[i] in seq[consts.VerificationResult] { consts.INVALID, consts.ENDORSED, consts.ENDORSED_TRUSTED }) &&
// @ 	(forall i, j int :: { endorsedResults[i] } 0 <= i && i < j && j < len(endorsedResults) ==> endorsedResults[i] != endorsedResults[j]) &&
// @ 	((exists i int :: { endorsedResults[i] } 0 <= i && i < len(endorsedResults) && endorsedResults[i] == consts.INVALID) ==> len(endorsedResults) == 1)
// @ ensures acc(endorsedBy)
// @ ensures iospec.P_Verifier(p0, rid, s0) && place.token(p0)
// @ ensures fact.OutFact_Verifier(rid, SignedOut(ai)) in s0
// @ ensures fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s0
// @ ensures len(endorsedBy) == len(authTs) &&
// @ 	forall i int :: { authTs[i] } 0 <= i && i < len(endorsedBy) ==> (
// @ 		stringB(endorsedBy[i]) == gamma(authTs[i]) &&
// @ 		fact.OutFact_Verifier(rid, EndorsedOut(authTs[i])) in s0)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost rootIdx int, ghost p place.Place, ghost rid term.Term, ghost s mset[fact.Fact], ghost ai, oi term.Term, ghost terms seq[term.Term], ghost rootKey term.Term @*/) (
	endorsedResults []consts.VerificationResult, endorsedBy []string /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost authTs seq[term.Term] @*/) {

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false

	// @ unfold TokenList(endorsements)
	// @ ghost defer fold TokenList(endorsements)

	// @ ghost authTs := seq[term.Term] {}

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_4(rid, oi, rootKey) in s
	// @ invariant fact.OutFact_Verifier(rid, SignedOut(ai)) in s
	// @ invariant fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s
	// @ invariant ValidToken(emblem) && Emblem(emblem) &&
	// @ 	unfolding ValidToken(emblem) in
	// @ 	unfolding acc(jwt.FieldMem(emblem.Token.Values()), 1/8) in
	// @ 	let ass := emblem.Token.PureGet("ass").([]*ident.AI) in
	// @ 	unfolding acc(tokens.AssMem(ass), 1/8) in
	// @ 	ident.AbsAI(ass) == gamma(ai)
	// @ invariant acc(endorsements)
	// @ invariant forall i int :: { TokenListElem(i, endorsements[i]) } 0 <= i && i < len(endorsements) ==> TokenListElem(i, endorsements[i])
	// @ invariant forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 	unfolding TokenListElem(i, endorsements[i]) in
	// @ 	Endorsement(endorsements[i]) &&
	// @ 	Abs(endorsements[i]) == gamma(terms[i]))
	// @ invariant 0 <= rootIdx && rootIdx < len(endorsements) &&
	// @ 	endorsements[rootIdx] == root &&
	// @ 	unfolding TokenListElem(rootIdx, root) in
	// @ 	unfolding ValidToken(root) in
	// @ 	root.Token.Contains("key") &&
	// @ 	root.Token.PureKeyID() != root.VerificationKey.KeyID(none[perm]) &&
	// @ 	stringB(root.VerificationKey.KeyID(none[perm])) == gamma(rootKey) &&
	// @ 	stringB(root.Token.Issuer()) == gamma(oi) &&
	// @ 	unfolding ValidToken(emblem) in
	// @ 	(root.Token.Issuer() == emblem.Token.Issuer())
	// @ invariant forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) && i != rootIdx ==> (
	// @ 	unfolding TokenListElem(i, endorsements[i]) in
	// @ 	unfolding TokenListElem(rootIdx, root) in
	// @ 	endorsements[i].Endorses(root) ==> (
	// @ 		unfolding ValidToken(endorsements[i]) in
	// @ 		unfolding ValidToken(root) in
	// @ 		root.Token.Issuer() != endorsements[i].Token.Issuer() ||
	// @ 		!endorsements[i].Token.PureGet("end").(bool)))
	// @ invariant issuers != nil && acc(issuers)
	// @ invariant len(issuers) == len(authTs) &&
	// @ 	forall i int :: { issuers[i] }{ authTs[i] } 0 <= i && i < len(issuers) ==> (
	// @ 		stringB(issuers[i]) == gamma(authTs[i]) &&
	// @ 		fact.OutFact_Verifier(rid, EndorsedOut(authTs[i])) in s)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(TokenListElem(i0, endorsements[i0]), 1/2)
		// @ unfold acc(ValidToken(endorsement), 1/2)

		// @ unfold acc(TokenListElem(rootIdx, root), 1/2)
		// @ unfold acc(ValidToken(root), 1/2)

		// @ unfold acc(ValidToken(emblem), 1/2)

		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if root.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if endorsement.Token.Issuer() == "" {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if _, logged := endorsement.Token.Get("log"); !logged {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if err := tokens.VerifyConstraints(emblem.Token, endorsement.Token); err != nil {
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			x := []consts.VerificationResult{consts.INVALID}
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			// @ assert len(x) == 1
			return x, nil /*@, p, s, seq[term.Term] { } @*/
		} else {
			/*@
			assert endorsement != root
			fold acc(ValidToken(emblem), 1/2)
			fold acc(ValidToken(root), 1/2)
			fold acc(TokenListElem(rootIdx, root), 1/2)
			unfold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			fold acc(ValidToken(endorsement), 1/2)

			assume fact.ValidTokenIn_Verifier(rid, terms[i0]) in s

			ghost var authT term.Term
			p, s, authT = ApplyIsEndorsedEmblem(endorsement, p, s, rid, oi, rootKey, terms[i0])

			authTs = authTs ++ seq[term.Term] { authT }
			@*/

			existsEndorsement = true
			// @ unfold acc(ValidToken(endorsement), 1/2)
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
			// @ fold acc(ValidToken(endorsement), 1/2)
			trustedFound = trustedFound || ok

			// @ fold TokenListElem(i0, endorsements[i0])
		}
	}

	/*@
		// Finish verification
		unfold iospec.P_Verifier(p, rid, s)
		unfold iospec.phiR_Verifier_13(p, rid, s)
		l := mset[fact.Fact] { fact.St_Verifier_4(rid, oi, rootKey) }
		a := mset[claim.Claim] { }
		r := mset[fact.Fact] { fact.St_Verifier_0(rid) }
		p = iospec.internBIO_e_FinishVerification(p, rid, oi, rootKey, l, a, r)
		s = fact.U(l, r, s)
	@*/

	if existsEndorsement {
		results := []consts.VerificationResult{consts.ENDORSED}
		if trustedFound {
			results = append( /*@ perm(1/2), @*/ results, consts.ENDORSED_TRUSTED)
		}
		// @ assert len(results) <= 2
		return results, issuers /*@, p, s, authTs @*/
	} else {
		return nil, nil /*@, p, s, seq[term.Term] {} @*/
	}
}
