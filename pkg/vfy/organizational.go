// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "github.com/adem-wg/adem-proto/pkg/ident"
	// @ "lib"
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

//	trusted
//
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ requires iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
// @ requires acc(Emblem(emblem), _) &&
// @ 	unfolding acc(Emblem(emblem), _) in
// @ 	unfolding acc(ValidToken(emblem), _) in
// @ 	emblem.Headers.ContentType() == string(consts.EmblemCty) &&
// @ 	emblem.Headers.Algorithm() != jwa.NoSignature
// @ requires EndorsementList(endorsements)
// @ ensures acc(Emblem(emblem), _)
// @ ensures acc(EndorsementList(endorsements), _)
// @ ensures acc(vfyResults)
// @ ensures !lib.GhostContainsResult(vfyResults, consts.INVALID) ==> (
// @ 	t != nil && acc(ValidToken(t), _) &&
// @ 	lib.GhostContainsResult(vfyResults, consts.SIGNED) &&
// @ 	iospec.P_Verifier(p, ridT, s) && place.token(p))
// @ ensures lib.GhostContainsResult(vfyResults, consts.SIGNED) ==> (
// @ 	!lib.GhostContainsResult(vfyResults, consts.INVALID) &&
// @ 	fact.OutFact_Verifier(ridT, lib.SignedOut(aiT)) in s0 &&
// @ 	(!lib.GhostContainsResult(vfyResults, consts.ORGANIZATIONAL) ==> fact.St_Verifier_0(ridT) in s0))
// @ ensures lib.GhostContainsResult(vfyResults, consts.ORGANIZATIONAL) ==> (
// @ 	!lib.GhostContainsResult(vfyResults, consts.INVALID) &&
// @ 	let oiB := lib.stringB(emblem.Token.Issuer()) in
// @ 	let rootKeyB := AbsKey(t.VerificationKey) in
// @ 		emblem.Token.Issuer() != "" && oiB == lib.gamma(oiT) &&
// @ 		rootKeyB == lib.gamma(rootKeyT) &&
// @ 		(fact.St_Verifier_4(ridT, oiT, rootKeyT) in s0) && (fact.OutFact_Verifier(ridT, lib.OrganizationalOut(aiT, oiT)) in s0))
func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p place.Place, ghost ridT term.Term, ghost s mset[fact.Fact] @*/) (vfyResults []consts.VerificationResult, t *ADEMToken /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost aiT term.Term, ghost oiT term.Term, ghost rootKeyT term.Term @*/) {
	// @ unfold EndorsementList(endorsements)
	// @ ghost defer fold acc(EndorsementList(endorsements), _)

	// @ ghost aiT := lib.GenericTerm()
	// @ ghost oiT := lib.GenericTerm()
	// @ ghost rootKeyT := lib.GenericTerm()

	endorsedBy := make(map[string]*ADEMToken)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
	// @ invariant acc(Emblem(emblem), _)
	// @ invariant acc(endorsements) &&
	// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 		(i < i0 ==> acc(EndListElem(i, endorsements[i]), _)) &&
	// @ 		(i0 <= i ==> EndListElem(i, endorsements[i])))
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy ==> let t, _ := endorsedBy[k] in acc(EndorsedByElem(k, t), _)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold EndListElem(i0, endorsements[i0])
		// @ unfold Endorsement(endorsement)
		// @ unfold acc(ValidToken(endorsement), _)
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		// @ fold Endorsement(endorsement)
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			// @ fold EndListElem(i0, endorsements[i0])
			continue
		} else if /*@ unfolding acc(Emblem(emblem), _) in unfolding acc(ValidToken(emblem), _) in unfolding Endorsement(endorsement) in unfolding acc(ValidToken(endorsement), _) in @*/ emblem.Token.Issuer() != endorsement.Token.Issuer() {
			// @ fold EndListElem(i0, endorsements[i0])
			continue
		} else if /*@ unfolding acc(Emblem(emblem), _) in unfolding acc(ValidToken(emblem), _) in unfolding Endorsement(endorsement) in unfolding acc(ValidToken(endorsement), _) in @*/ emblem.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold EndListElem(i0, endorsements[i0])
			continue
		} else if /*@ unfolding acc(Emblem(emblem), _) in unfolding acc(ValidToken(emblem), _) in @*/ kid != emblem.VerificationKey.KeyID( /*@ none[perm] @*/ ) && !end.(bool) {
			// @ fold EndListElem(i0, endorsements[i0])
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			// @ fold EndListElem(i0, endorsements[i0])
			log.Println("illegal branch in endorsements")
			return []consts.VerificationResult{consts.INVALID}, nil /*@, lib.GenericPlace(), lib.GenericSet(), aiT, oiT, rootKeyT @*/
		} else {
			// @ fold acc(EndListElem(i0, endorsements[i0]), _)
			// @ fold acc(EndorsedByElem(kid, endorsement), _)
			endorsedBy[kid] = endorsement
		}
	}

	// @ ghost endorses := none[string]

	var root *ADEMToken
	trustedFound := false
	last := emblem

	// @ invariant acc(Emblem(emblem), _)
	// @ invariant acc(trustedKeys.Mem(), 1/2) && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant iospec.P_Verifier(p, ridT, s) && place.token(p) && fact.St_Verifier_2(ridT) in s
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
				// @ fold acc(Emblem(emblem), _)
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil /*@, lib.GenericPlace(), lib.GenericSet(), aiT, oiT, rootKeyT @*/
			} else {
				// @ fold acc(Emblem(emblem), _)
				/*@
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
				@*/
				last = endorsing
				// @ endorses = some(kid)
			}
		} else {
			// @ ghost { if endorses == none[string] { fold acc(Emblem(last), _) } else { fold acc(Endorsement(last), _) } }
			root = last
		}
	}

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
		return []consts.VerificationResult{consts.INVALID}, nil /*@, lib.GenericPlace(), lib.GenericSet(), aiT, oiT, rootKeyT @*/
	} else if rootLogged {
		// TODO: We don't actually know this
		//  assert emblem.Token.Issuer() != ""
		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(root), _) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
	}

	return results, root /*@, p, s, aiT, oiT, rootKeyT @*/
}

/*@

pred EndorsedByElem(_ string, t *ADEMToken) {
	t != nil && Endorsement(t)
}

@*/
