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

// TODO: (lmeinen) Add term equivalence for ai
// TODO: (lmeinen) Add state transitions until we can add proper return values

// @ trusted
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves ValidToken(emblem) && EmblemF(emblem) && Abs(emblem) == gamma(embT)
// @ preserves TokenList(endorsements)
// @ preserves len(endorsements) == len(endTs)
// @ preserves unfolding TokenList(endorsements) in forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> unfolding TokenListElem(i, endorsements[i]) in EndorsementF(endorsements[i])
// @ preserves unfolding TokenList(endorsements) in forall i int :: { endorsements[i] } { endTs[i] } 0 <= i && i < len(endTs) ==> unfolding TokenListElem(i, endorsements[i]) in Abs(endorsements[i]) == gamma(endTs[i])
// @ requires InFacts(ridT, endTs ++ seq[term.Term] { embT }, set[int] {}, s)
// @ requires iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
// @ ensures InFacts(ridT, endTs ++ seq[term.Term] { embT }, orgIdx, s0)
// @ ensures iospec.P_Verifier(p0, ridT, s0) && place.token(p0)
// @ ensures acc(vfyResults)
// @ ensures t != nil ==> 0 <= rootIdx && rootIdx < len(endorsements) &&
// @ 	ValidRoot(t, emblem, endorsements, rootIdx) &&
// @ 	unfolding TokenList(endorsements) in
// @ 	unfolding TokenListElem(rootIdx, t) in
// @ 	unfolding ValidToken(t) in
// @ 	stringB(t.VerificationKey.KeyID(none[perm])) == gamma(rootKeyT) &&
// @ 	stringB(t.Token.Issuer()) == gamma(oiT)
// @ ensures let resSeq := toSeqResult(vfyResults) in
// @ 	(!(consts.INVALID in resSeq) ==> t != nil) &&
// @ 	(consts.SIGNED in resSeq ==> (
// @ 		t != nil &&
// @ 		(fact.OutFact_Verifier(ridT, SignedOut(aiT)) in s0))) &&
// @ 	(consts.ORGANIZATIONAL in resSeq ==> (
// @ 		t != nil &&
// @ 		(fact.St_Verifier_4(ridT, oiT, rootKeyT) in s0) &&
// @ 		(fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) in s0) &&
// @ 		unfolding ValidToken(emblem) in
// @ 		emblem.Token.Issuer() != "" && stringB(emblem.Token.Issuer()) == gamma(oiT)))
func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost embT term.Term, ghost endTs seq[term.Term], ghost p place.Place, ghost ridT term.Term, ghost s mset[fact.Fact] @*/) (
	vfyResults []consts.VerificationResult, t *ADEMToken /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost orgIdx set[int], ghost aiT, oiT, rootKeyT term.Term, ghost rootIdx int @*/) {
	// @ unfold acc(EndorsementList(endorsements), _)

	// @ ghost aiT := GenericTerm()
	// @ ghost oiT := GenericTerm()
	// @ ghost rootKeyT := GenericTerm()

	/*
		I need:
		- to be able to start at root and walk the token chain until emblem
		- for each token I need to have the corresponding term
		- for each token I need to know that the index in endorsements is unique OR that it is the emblem
			--> Such that I then know that the ValidTokenIn facts in s are enough
	*/

	endorsedBy := make(map[string]*ADEMToken)
	// @ ghost endorsedByIdx := dict[string]int {}

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
	//  invariant forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i < len(endTs) ==> endTs[i] # endTs <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s
	// @ invariant InFacts(ridT, endTs ++ seq[term.Term] { embT }, set[int] {}, s)
	// @ invariant fact.ValidTokenIn_Verifier(ridT, embT) in s
	// @ invariant acc(Emblem(emblem), _) && unfolding acc(Emblem(emblem), _) in Abs(emblem) == gamma(embT)
	// @ invariant acc(endorsements, _) &&
	// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> acc(EndListElem(i, endorsements[i]), _)
	// @ invariant acc(endorsedBy)
	// @ invariant forall k string :: { endorsedByIdx[k] } k in domain(endorsedByIdx) ==> k in endorsedBy && 0 <= endorsedByIdx[k] && endorsedByIdx[k] < i0
	// @ invariant forall k1, k2 string :: { endorsedByIdx[k1] } k1 != k2 && k1 in domain(endorsedByIdx) && k2 in domain(endorsedByIdx) ==> endorsedByIdx[k1] != endorsedByIdx[k2]
	// @ invariant forall k string :: { endorsedBy[k] } k in domain(endorsedBy) ==> (
	// @ 		k in domain(endorsedByIdx) &&
	// @ 		let t, _ := endorsedBy[k] in
	// @ 		acc(EndorsedByElem(k, t), _) &&
	// @ 		t == endorsements[endorsedByIdx[k]])
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(EndListElem(i0, endorsements[i0]), _)
		// @ unfold acc(Endorsement(endorsement), _)
		// @ unfold acc(ValidToken(endorsement), _)
		// @ unfold acc(Emblem(emblem), _)
		// @ unfold acc(ValidToken(emblem), _)
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			continue
		} else if emblem.Token.Issuer() != endorsement.Token.Issuer() {
			continue
		} else if emblem.Token.Issuer() != endorsement.Token.Subject() {
			continue
		} else if kid != emblem.VerificationKey.KeyID( /*@ none[perm] @*/ ) && !end.(bool) {
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			log.Println("illegal branch in endorsements")
			return []consts.VerificationResult{consts.INVALID}, nil /*@, p, s, aiT, oiT, rootKeyT @*/
		} else {
			endorsedBy[kid] = endorsement
			// @ endorsedByIdx[kid] = i0
			// @ fold acc(EndorsedByElem(kid, endorsement), _)
		}
	}

	// @ ghost endorses := none[string]
	//  ghost rootIdx int // starting point
	// @ ghost endorsesIdx := dict[int]int {} // invert endorsedBy

	var root *ADEMToken
	trustedFound := false
	last := emblem

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(trustedKeys.Mem(), 1/2) && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
	//  invariant forall i int :: { fact.ValidTokenIn_Verifier(ridT, endTs[i]) } 0 <= i && i < len(endTs) ==> endTs[i] # endTs <= fact.ValidTokenIn_Verifier(ridT, endTs[i]) # s
	// @ invariant InFacts(ridT, endTs ++ seq[term.Term] { embT }, set[int] {}, s)
	// @ invariant fact.ValidTokenIn_Verifier(ridT, embT) in s
	// @ invariant acc(Emblem(emblem), _) && unfolding acc(Emblem(emblem), _) in Abs(emblem) == gamma(embT)
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy && some(k) != endorses ==> let t, _ := endorsedBy[k] in acc(EndorsedByElem(k, t), _)
	// @ invariant endorses == none[string] ?
	// @ 	last == emblem :
	// @ 	get(endorses) in endorsedBy && endorsedBy[get(endorses)] == last && acc(Endorsement(last), _)
	// @ invariant root != nil ==> root == last
	for root == nil {
		// @ ghost { if endorses == none[string] { unfold acc(Emblem(last), _) } else { unfold acc(Endorsement(last), _) } }
		_, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(last), _) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
		trustedFound = trustedFound || ok

		kid := /*@ unfolding acc(ValidToken(last), _) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ )
		if endorsing := endorsedBy[kid]; endorsing != nil {
			/*@
			ghost {
				if some(kid) != endorses {
					unfold acc(EndorsedByElem(kid, endorsing), _)
					unfold acc(Endorsement(endorsing), _)
				}
			}
			@*/
			// @ unfold acc(Emblem(emblem), _)
			// @ unfold acc(ValidToken(emblem), _)
			// @ unfold acc(ValidToken(endorsing), _)
			if err := tokens.VerifyConstraints(emblem.Token, endorsing.Token); err != nil {
				//  fold acc(Emblem(emblem), _)
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil /*@, GenericPlace(), GenericSet(), aiT, oiT, rootKeyT @*/
			} else {
				//  fold acc(Emblem(emblem), _)
				/*
					ghost {
						if endorses == none[string] {
							fold acc(Emblem(last), _)
						} else {
							fold acc(Endorsement(last), _)
							if some(kid) != endorses {
								fold acc(EndorsedByElem(get(endorses), last), _)
							}
						}

						if some(kid) != endorses {
							fold acc(Endorsement(endorsing), _)
						}
					}
				*/
				last = endorsing
				// @ endorses = some(kid)
			}
		} else {
			//  ghost { if endorses == none[string] { fold acc(Emblem(last), _) } else { fold acc(Endorsement(last), _) } }
			root = last
		}
	}

	// @ assume false

	/*@ assert
		unfolding acc(Emblem(emblem), _) in
		unfolding acc(ValidToken(emblem), _) in
		emblem.Headers.ContentType() == string(consts.EmblemCty) &&
		emblem.Headers.Algorithm() != jwa.NoSignature
	@*/
	results := []consts.VerificationResult{consts.SIGNED}
	if trustedFound {
		results = append( /*@ perm(1/2), @*/ results, consts.SIGNED_TRUSTED)
	}

	// @ ghost { if endorses == none[string] { unfold acc(Emblem(root), _) } else { unfold acc(Endorsement(root), _) } }
	// @ unfold acc(ValidToken(root), _)
	_, rootLogged := root.Token.Get("log")
	if /*@ unfolding acc(Emblem(emblem), _) in unfolding acc(ValidToken(emblem), _) in @*/ emblem.Token.Issuer() != "" && !rootLogged {
		return []consts.VerificationResult{consts.INVALID}, nil /*@, GenericPlace(), GenericSet(), aiT, oiT, rootKeyT @*/
	} else if rootLogged {
		// TODO: (lmeinen) Apply state transitions for 2 -> 3 -> ... -> 3 -> 4
		// we need: an ordering of endorsements, equivalences between their keys, oiT and aiT

		// things I need here: terms for all tokens + constraints on everything in endorsedBy

		/*@
			ghost rootT := GenericTerm()
			// Parse root pattern
			ghost someRootKey, someOi, someEndorsedKey, someSig := RootEndPattern(root)

			// Apply pattern requirement for root patterns
			ghost rootKeyT, oiT, endorsedKeyT, sigT := RootEndorsementPatternRequirement(rootT, ridT, someRootKey, someOi, someEndorsedKey, someSig, s, p)

			// Apply IsOrganizationalEmblem rule
			unfold iospec.P_Verifier(p, ridT, s)
			unfold iospec.phiR_Verifier_6(p, ridT, s)
			l := mset[fact.Fact] { fact.St_Verifier_2(ridT), fact.ValidTokenIn_Verifier(ridT, rootT) }
			a := mset[claim.Claim] { }
			r := mset[fact.Fact] { fact.St_Verifier_3(ridT, oiT, rootKeyT, endorsedKeyT) }
			p = iospec.internBIO_e_IsOrganizationalEmblem(p, ridT, rootKeyT, oiT, endorsedKeyT, sigT, l, a, r)
			s = fact.U(l, r, s)

			// ...

			// Parse emblem pattern
			ghost someAi, someSig := SignedEmblemPattern(emblem, endorsedKeyT, oiT)

			// Apply pattern requirement for anon emblem patterns
			ghost aiT, sigT := SignedEmblemPatternRequirement(embT, ridT, rootKeyT, oiT, endorsedKeyT, someAi, someSig, s, p)

			// Apply CollectAuthorityEndorsements rule
			unfold iospec.P_Verifier(p, ridT, s)
			unfold iospec.phiR_Verifier_11(p, ridT, s)
			l := mset[fact.Fact] { fact.St_Verifier_3(ridT, oiT, rootKeyT, endorsedKeyT), fact.ValidTokenIn_Verifier(ridT, embT) }
			a := mset[claim.Claim] { claim.VerifiedEndorsed(ridT, oiT, aiT, endorsedKeyT), claim.VerifiedRootEndorsement(ridT, oiT, rootKeyT) }
			r := mset[fact.Fact] { fact.St_Verifier_4(ridT, oiT, rootKeyT),
		                           fact.OutFact_Verifier(ridT, SignedOut(aiT)),
		                           fact.OutFact_Verifier(ridT, OrganizationalOut(aiT, oiT)) }
			p = iospec.internBIO_e_CollectAuthorityEndorsements(p, ridT, oiT, rootKeyT, endorsedKeyT, aiT, sigT, l, a, r)
			s = fact.U(l, r, s)
		@*/

		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(root), _) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
	} else {
		// TODO: (lmeinen) apply state transition 2 -> 0
		/*@
			unfold acc(Emblem(emblem), _)

			// Parse emblem pattern
			ghost someKey, someAi, someSig := AnonEmblemPattern(emblem)

			// Apply pattern requirement for anon emblem patterns
			ghost keyT, aiT, sigT := AnonEmblemPatternRequirement(embT, ridT, someKey, someAi, someSig, s, p)

			// Apply IsSignedEmblem rule
			unfold iospec.P_Verifier(p, ridT, s)
			unfold iospec.phiR_Verifier_5(p, ridT, s)
			l := mset[fact.Fact] { fact.St_Verifier_2(ridT), fact.ValidTokenIn_Verifier(ridT, embT) }
			a := mset[claim.Claim] { }
			r := mset[fact.Fact] { fact.St_Verifier_0(ridT), fact.OutFact_Verifier(ridT, SignedOut(aiT)) }
			p = iospec.internBIO_e_IsSignedEmblem(p, ridT, keyT, aiT, sigT, l, a, r)
			s = fact.U(l, r, s)
		@*/
	}

	return results, root /*@, p, s, aiT, oiT, rootKeyT @*/
}

/*@

pred EndorsedByElem(_ string, t *ADEMToken) {
	t != nil && Endorsement(t) &&
	unfolding acc(Endorsement(t), _) in
	unfolding acc(ValidToken(t), _) in
	t.Token.Contains("key")
}

@*/
