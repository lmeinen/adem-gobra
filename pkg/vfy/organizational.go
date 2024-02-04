// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "github.com/lestrrat-go/jwx/v2/jwt"
)

// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ requires p > 0
// @ requires acc(Emblem(emblem), p)
// @ requires acc(EndorsementList(endorsements), p)
// @ ensures acc(Emblem(emblem), p / 2)
// @ ensures acc(EndorsementList(endorsements), p / 2)
// @ ensures acc(vfyResults)
// @ ensures !goblib.GhostContainsResult(vfyResults, consts.INVALID) ==> t != nil && acc(ValidToken(t), p / 2)
func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p perm @*/) (vfyResults []consts.VerificationResult, t *ADEMToken) {
	// @ unfold acc(EndorsementList(endorsements), p)
	// @ ghost defer fold acc(EndorsementList(endorsements), p / 2)

	endorsedBy := make(map[string]*ADEMToken)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(Emblem(emblem), p)
	// @ invariant acc(endorsements, p) &&
	// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 		(i < i0 ==> acc(EndListElem(i, endorsements[i]), p / 2)) &&
	// @ 		(i0 <= i ==> acc(EndListElem(i, endorsements[i]), p)))
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy ==> let t, _ := endorsedBy[k] in acc(EndorsedByElem(k, t), p / 2)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(EndListElem(i0, endorsements[i0]), p)
		// @ unfold acc(Endorsement(endorsement), p)
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		// @ fold acc(Endorsement(endorsement), p)
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			// @ fold acc(EndListElem(i0, endorsements[i0]), p)
			continue
		} else if /*@ unfolding acc(Emblem(emblem), p) in unfolding acc(Endorsement(endorsement), p) in @*/ emblem.Token.Issuer() != endorsement.Token.Issuer() {
			// @ fold acc(EndListElem(i0, endorsements[i0]), p)
			continue
		} else if /*@ unfolding acc(Emblem(emblem), p) in unfolding acc(Endorsement(endorsement), p) in @*/ emblem.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(EndListElem(i0, endorsements[i0]), p)
			continue
		} else if /*@ unfolding acc(Emblem(emblem), p) in unfolding acc(ValidToken(emblem), p / 2) in @*/ kid != emblem.VerificationKey.KeyID( /*@ none[perm] @*/ ) && !end.(bool) {
			// @ fold acc(EndListElem(i0, endorsements[i0]), p)
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			// @ fold acc(EndListElem(i0, endorsements[i0]), p)
			log.Println("illegal branch in endorsements")
			return []consts.VerificationResult{consts.INVALID}, nil
		} else {
			// @ fold acc(EndListElem(i0, endorsements[i0]), p / 2)
			// @ fold acc(EndorsedByElem(kid, endorsement), p / 2)
			endorsedBy[kid] = endorsement
		}
	}

	// @ ghost endorses := none[string]

	var root *ADEMToken
	trustedFound := false
	last := emblem

	// @ invariant acc(Emblem(emblem), p)
	// @ invariant acc(trustedKeys.Mem(), 1/2) && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy && some(k) != endorses ==> let t, _ := endorsedBy[k] in acc(EndorsedByElem(k, t), p / 2)
	// @ invariant endorses == none[string] ?
	// @ 	last == emblem :
	// @ 	get(endorses) in endorsedBy && endorsedBy[get(endorses)] == last && acc(Endorsement(last), p / 2)
	// @ invariant root != nil ==> root == last
	for root == nil {
		// @ ghost { if endorses == none[string] { unfold acc(Emblem(last), p / 2) } else { unfold acc(Endorsement(last), p / 2) } }
		_, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(last), p / 4) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
		trustedFound = trustedFound || ok

		kid := /*@ unfolding acc(ValidToken(last), p / 4) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ )
		if endorsing := endorsedBy[kid]; endorsing != nil {
			/*@
			ghost {
				if some(kid) != endorses {
					unfold acc(EndorsedByElem(kid, endorsing), p / 2)
					unfold acc(Endorsement(endorsing), p / 2)
				}
			}
			@*/
			if err := tokens.VerifyConstraints(
				/*@ unfolding acc(Emblem(emblem), p / 2) in unfolding acc(ValidToken(emblem), p / 4) in @*/ emblem.Token,
				/*@ unfolding acc(ValidToken(endorsing), p / 4) in @*/ endorsing.Token); err != nil {
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil
			} else {
				/*@
				ghost {
					if endorses == none[string] {
						fold acc(Emblem(last), p / 2)
					} else {
						fold acc(Endorsement(last), p / 2)
						if some(kid) != endorses {
							fold acc(EndorsedByElem(get(endorses), last), p / 2)
						}
					}

					if some(kid) != endorses {
						fold acc(Endorsement(endorsing), p / 2)
					}
				}
				@*/
				last = endorsing
				// @ endorses = some(kid)
			}
		} else {
			// @ ghost { if endorses == none[string] { fold acc(Emblem(last), p / 2) } else { fold acc(Endorsement(last), p / 2) } }
			root = last
		}
	}

	results := []consts.VerificationResult{consts.SIGNED}
	if trustedFound {
		results = append( /*@ perm(1/2), @*/ results, consts.SIGNED_TRUSTED)
	}

	// @ ghost { if endorses == none[string] { unfold acc(Emblem(root), p / 2) } else { unfold acc(Endorsement(root), p / 2) } }
	// @ unfold acc(ValidToken(root), p / 4)
	_, rootLogged := root.Token.Get("log")
	// @ fold acc(ValidToken(root), p / 2)
	if /*@ unfolding acc(Emblem(emblem), p / 2) in @*/ emblem.Token.Issuer() != "" && !rootLogged {
		return []consts.VerificationResult{consts.INVALID}, nil
	} else if rootLogged {
		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(ValidToken(root), p / 2) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
	}

	return results, root
}

/*@

pred EndorsedByElem(_ string, t *ADEMToken) {
	t != nil && Endorsement(t)
}

@*/
