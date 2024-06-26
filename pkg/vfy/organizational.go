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
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves ValidToken(emblem) && Emblem(emblem) && Abs(emblem) == gamma(embT)
// @ preserves TokenList(endorsements)
// @ preserves len(endorsements) == len(terms)
// @ preserves unfolding TokenList(endorsements) in
// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
// @ 		unfolding TokenListElem(i, endorsements[i]) in
// @ 		Endorsement(endorsements[i]) &&
// @ 		Abs(endorsements[i]) == gamma(terms[i]))
// @ requires iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_2(rid) in s
// @ ensures iospec.P_Verifier(p0, rid, s0) && place.token(p0)
// @ ensures acc(vfyResults)
// @ ensures t != nil && t != emblem ==> unfolding TokenList(endorsements) in
// @ 	0 <= rootIdx && rootIdx < len(endorsements) && t == endorsements[rootIdx]
// @ ensures 0 < len(vfyResults) && len(vfyResults) <= 4 &&
// @ 	(forall i int :: 0 <= i && i < len(vfyResults) ==> vfyResults[i] in seq[consts.VerificationResult] { consts.INVALID, consts.SIGNED, consts.SIGNED_TRUSTED, consts.ORGANIZATIONAL, consts.ORGANIZATIONAL_TRUSTED }) &&
// @ 	(forall i, j int :: 0 <= i && i < j && j < len(vfyResults) ==> vfyResults[i] != vfyResults[j]) &&
// @ 	((exists i int :: 0 <= i && i < len(vfyResults) && vfyResults[i] == consts.INVALID) ? len(vfyResults) == 1 : vfyResults[0] == consts.SIGNED) &&
// @	((exists i int :: 0 <= i && i < len(vfyResults) && vfyResults[i] == consts.SIGNED) ==> (
// @		t != nil &&
// @		(fact.OutFact_Verifier(rid, SignedOut(ai)) in s0) &&
// @		unfolding ValidToken(emblem) in
// @ 		unfolding acc(jwt.FieldMem(emblem.Token.Values()), 1/8) in
// @ 		let ass := emblem.Token.PureGet("ass").([]*ident.AI) in
// @ 		unfolding acc(tokens.AssMem(ass), 1/8) in
// @ 		ident.AbsAI(ass) == gamma(ai))) &&
// @	((exists i int :: 0 <= i && i < len(vfyResults) && vfyResults[i] == consts.ORGANIZATIONAL) ==> (
// @		t != nil && t != emblem &&
// @		(fact.St_Verifier_4(rid, oi, rootKey) in s0) &&
// @		(fact.OutFact_Verifier(rid, OrganizationalOut(ai, oi)) in s0) &&
// @		unfolding ValidToken(emblem) in
// @		emblem.Token.Issuer() != "" && stringB(emblem.Token.Issuer()) == gamma(oi) &&
// @ 		unfolding TokenList(endorsements) in
// @ 		(forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) && i != rootIdx ==> (
// @ 			unfolding TokenListElem(i, endorsements[i]) in
// @ 			unfolding TokenListElem(rootIdx, t) in
// @ 			endorsements[i].Endorses(t) ==> (
// @ 				unfolding ValidToken(endorsements[i]) in
// @ 				unfolding ValidToken(t) in
// @ 				t.Token.Issuer() != endorsements[i].Token.Issuer() ||
// @ 				!endorsements[i].Token.PureGet("end").(bool)))) &&
// @ 		unfolding TokenListElem(rootIdx, t) in
// @ 		unfolding ValidToken(t) in
// @ 		t.Token.Contains("key") &&
// @ 		t.Token.PureKeyID() != t.VerificationKey.KeyID(none[perm]) &&
// @ 		t.Token.Issuer() == emblem.Token.Issuer() &&
// @ 		stringB(t.VerificationKey.KeyID(none[perm])) == gamma(rootKey) &&
// @ 		stringB(t.Token.Issuer()) == gamma(oi)))
func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost embT term.Term, ghost terms seq[term.Term], ghost p place.Place, ghost rid term.Term, ghost s mset[fact.Fact] @*/) (
	vfyResults []consts.VerificationResult, t *ADEMToken /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost ai, oi, rootKey term.Term, ghost rootIdx int @*/) {

	// @ ghost ai := GenericTerm()
	// @ ghost oi := GenericTerm()
	// @ ghost rootKey := GenericTerm()

	endorsedBy := make(map[string]*ADEMToken)
	// @ ghost endorsedByIdx := dict[string]int {}

	// @ unfold TokenList(endorsements)
	// @ ghost defer fold TokenList(endorsements)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_2(rid) in s
	// @ invariant ValidToken(emblem) && Emblem(emblem) && Abs(emblem) == gamma(embT)
	// @ invariant acc(endorsements)
	// @ invariant len(endorsements) == len(terms)
	// @ invariant forall i int :: { TokenListElem(i, endorsements[i]) } 0 <= i && i < len(endorsements) ==> TokenListElem(i, endorsements[i])
	// @ invariant forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 		unfolding TokenListElem(i, endorsements[i]) in
	// @ 		Endorsement(endorsements[i]) &&
	// @ 		Abs(endorsements[i]) == gamma(terms[i]))
	// @ invariant acc(endorsedBy)
	// @ invariant forall k string :: { endorsedByIdx[k] } k in domain(endorsedByIdx) ==> 0 <= endorsedByIdx[k] && endorsedByIdx[k] < len(endorsements)
	// @ invariant forall k string :: { endorsedBy[k] } k in domain(endorsedBy) ==> (
	// @ 	k in domain(endorsedByIdx) &&
	// @ 	let t, _ := endorsedBy[k] in
	// @ 	t == endorsements[endorsedByIdx[k]] &&
	// @ 	unfolding TokenListElem(endorsedByIdx[k], t) in
	// @ 	unfolding ValidToken(t) in
	// @ 		t.Token.Contains("key") &&
	// @ 		t.Token.PureKeyID() == k &&
	// @ 	unfolding ValidToken(emblem) in
	// @ 		t.Token.Subject() == emblem.Token.Issuer() &&
	// @ 		t.Token.Issuer() == emblem.Token.Issuer())
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold TokenListElem(i0, endorsements[i0])
		// @ assert Endorsement(endorsements[i0])
		// @ unfold acc(ValidToken(endorsement), 1/2)
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
			continue
		} else if /*@ unfolding ValidToken(emblem) in @*/ emblem.Token.Issuer() != endorsement.Token.Issuer() {
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
			continue
		} else if /*@ unfolding ValidToken(emblem) in @*/ emblem.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
			continue
		} else if kid != ( /*@ unfolding ValidToken(emblem) in @*/ emblem.VerificationKey.KeyID( /*@ none[perm] @*/ )) && !end.(bool) {
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			log.Println("illegal branch in endorsements")
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
			return []consts.VerificationResult{consts.INVALID}, nil /*@, p, s, ai, oi, rootKey, GenericInt() @*/
		} else {
			endorsedBy[kid] = endorsement
			// @ endorsedByIdx[kid] = i0
			// @ fold acc(ValidToken(endorsement), 1/2)
			// @ fold TokenListElem(i0, endorsements[i0])
		}
	}

	var root *ADEMToken
	trustedFound := false
	last := emblem
	// @ ghost rootIdx := GenericInt()

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(trustedKeys.Mem(), 1/2) && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, rid, s) && place.token(p) && fact.St_Verifier_2(rid) in s
	// @ invariant ValidToken(emblem) && Emblem(emblem) && Abs(emblem) == gamma(embT)
	// @ invariant acc(endorsements)
	// @ invariant len(endorsements) == len(terms)
	// @ invariant forall i int :: { TokenListElem(i, endorsements[i]) } 0 <= i && i < len(endorsements) ==> TokenListElem(i, endorsements[i])
	// @ invariant forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 		unfolding TokenListElem(i, endorsements[i]) in
	// @ 		Endorsement(endorsements[i]) &&
	// @ 		Abs(endorsements[i]) == gamma(terms[i]))
	// @ invariant acc(endorsedBy, 1/2)
	// @ invariant forall k string :: { endorsements[endorsedByIdx[k]] } k in domain(endorsedByIdx) ==> 0 <= endorsedByIdx[k] && endorsedByIdx[k] < len(endorsements)
	// @ invariant forall k string :: { endorsedBy[k] } k in endorsedBy ==> (
	// @ 	k in domain(endorsedByIdx) && 0 <= endorsedByIdx[k] && endorsedByIdx[k] < len(endorsements) &&
	// @ 	let t, _ := endorsedBy[k] in
	// @ 	t == endorsements[endorsedByIdx[k]] &&
	// @ 	unfolding TokenListElem(endorsedByIdx[k], t) in
	// @ 	unfolding ValidToken(t) in
	// @ 		t.Token.Contains("key") &&
	// @ 		t.Token.PureKeyID() == k &&
	// @ 	unfolding ValidToken(emblem) in
	// @ 		t.Token.Subject() == emblem.Token.Issuer() &&
	// @ 		t.Token.Issuer() == emblem.Token.Issuer())
	// @ invariant last != emblem ==>
	// @ 		0 <= rootIdx && rootIdx < len(endorsements) &&
	// @ 		last == endorsements[rootIdx] && (
	// @ 		unfolding TokenListElem(rootIdx, last) in
	// @ 		unfolding ValidToken(last) in
	// @ 		unfolding ValidToken(emblem) in
	// @ 			last.Token.Contains("key") &&
	// @ 			last.Token.Subject() == emblem.Token.Issuer() &&
	// @ 			last.Token.Issuer() == emblem.Token.Issuer())
	// @ invariant root != nil ==> root == last
	for root == nil {
		// @ ghost { if last != emblem { unfold acc(TokenListElem(rootIdx, last), 1/2) } }
		_, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(last), 1/2) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
		trustedFound = trustedFound || ok

		kid := /*@ unfolding acc(ValidToken(last), 1/2) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ )
		if endorsing := endorsedBy[kid]; endorsing != nil {
			// @ assert endorsing != emblem
			// @ assert endorsing == endorsements[endorsedByIdx[kid]]

			// @ unfold acc(ValidToken(emblem), 1/2)
			// @ unfold acc(TokenListElem(endorsedByIdx[kid], endorsing), 1/2)
			// @ unfold acc(ValidToken(endorsing), 1/2)
			if err := tokens.VerifyConstraints(emblem.Token, endorsing.Token); err != nil {
				// @ fold acc(ValidToken(endorsing), 1/2)
				// @ fold acc(TokenListElem(endorsedByIdx[kid], endorsing), 1/2)
				// @ fold acc(ValidToken(emblem), 1/2)
				// @ ghost { if last != emblem { fold acc(TokenListElem(rootIdx, last), 1/2) } }
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil /*@, p, s, ai, oi, rootKey, GenericInt() @*/
			} else {
				// @ fold acc(ValidToken(endorsing), 1/2)
				// @ assert endorsing.Endorses(last)
				// @ fold acc(TokenListElem(endorsedByIdx[kid], endorsing), 1/2)
				// @ fold acc(ValidToken(emblem), 1/2)
				// @ ghost { if last != emblem { fold acc(TokenListElem(rootIdx, last), 1/2) } }
				last = endorsing
				// @ rootIdx = endorsedByIdx[kid]
			}
		} else {
			root = last
			// @ ghost { if last != emblem { fold acc(TokenListElem(rootIdx, last), 1/2) } }
		}
	}

	results := []consts.VerificationResult{consts.SIGNED}
	if trustedFound {
		results = append( /*@ perm(1/2), @*/ results, consts.SIGNED_TRUSTED)
	}

	// @ assert len(results) <= 2

	// @ ghost { if root != emblem { unfold TokenListElem(rootIdx, root) } }
	// @ unfold acc(ValidToken(root), 1/2)
	_, rootLogged := root.Token.Get("log")
	// @ fold acc(ValidToken(root), 1/2)
	// @ ghost { if root != emblem { fold TokenListElem(rootIdx, root) } }
	if /*@ unfolding ValidToken(emblem) in @*/ emblem.Token.Issuer() != "" && !rootLogged {
		return []consts.VerificationResult{consts.INVALID}, nil /*@, p, s, ai, oi, rootKey, rootIdx @*/
	} else if rootLogged {
		// @ unfold TokenListElem(rootIdx, root)

		// @ p, s, oi, rootKey, ai = GetOrganizationalOut(emblem, root, p, s, rid, terms[rootIdx], embT)

		// TODO: (lmeinen) Explicitely verify the below assumptions
		// (both require more involved specification of the endorsedBy map, which led to problems with non-termination)

		// Root token doesn't endorse itself - can be derived from the termination of the above loop
		// @ unfold ValidToken(root)
		// @ assume root.Token.Contains("key") &&
		// @ 	root.Token.PureKeyID() != root.VerificationKey.KeyID(none[perm])
		// @ fold ValidToken(root)

		// Any endorsement of the root token is either of a different organization or doesn't allow further endorsements
		// @ assume forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) && i != rootIdx ==> (
		// @ 	unfolding TokenListElem(i, endorsements[i]) in
		// @ 	endorsements[i].Endorses(root) ==> (
		// @ 		unfolding ValidToken(endorsements[i]) in
		// @ 		unfolding ValidToken(root) in
		// @ 		root.Token.Issuer() != endorsements[i].Token.Issuer() ||
		// @ 		!endorsements[i].Token.PureGet("end").(bool)))

		// @ fold TokenListElem(rootIdx, root)

		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID( /*@ unfolding TokenListElem(rootIdx, root) in unfolding ValidToken(root) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
		// @ assert len(results) <= 4
	} else {
		// apply state transition 2 -> 0
		/*@
			// unfold acc(ValidToken(emblem), 3/4)

			// Parse emblem pattern
			ghost someKey, someAi, someSig := AnonEmblemPattern(emblem)

			// fold acc(ValidToken(emblem), 3/4)

			ghost var keyT term.Term
			ghost var sigT term.Term

			// Apply pattern requirement for anon emblem patterns
			keyT, ai, sigT = AnonEmblemPatternRequirement(embT, rid, someKey, someAi, someSig, s, p)

			assume fact.ValidTokenIn_Verifier(rid, embT) in s

			// Apply IsSignedEmblem rule
			unfold iospec.P_Verifier(p, rid, s)
			unfold iospec.phiR_Verifier_5(p, rid, s)
			l := mset[fact.Fact] { fact.St_Verifier_2(rid), fact.ValidTokenIn_Verifier(rid, embT) }
			a := mset[claim.Claim] { }
			r := mset[fact.Fact] { fact.St_Verifier_0(rid), fact.OutFact_Verifier(rid, SignedOut(ai)) }
			p = iospec.internBIO_e_IsSignedEmblem(p, rid, keyT, ai, sigT, l, a, r)
			s = fact.U(l, r, s)
		@*/
		// @ assert len(results) <= 2
	}

	// @ assert consts.SIGNED == results[0]

	return results, root /*@, p, s, ai, oi, rootKey, rootIdx @*/
}
