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
// @ preserves trustedKeys != nil && trustedKeys.Mem()
// @ requires p > 0
// @ requires acc(emblem.Mem(), p)
// @ requires acc(TokenList(endorsements), p)
// @ ensures acc(emblem.Mem(), p / 2)
// @ ensures acc(TokenList(endorsements), p / 2)
// @ ensures acc(vfyResults)
// @ ensures !goblib.GhostContainsResult(vfyResults, consts.INVALID) ==> t != nil && acc(t.Mem(), p / 2)
func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p perm @*/) (vfyResults []consts.VerificationResult, t *ADEMToken) {
	// @ unfold acc(TokenList(endorsements), p)
	// @ ghost defer fold acc(TokenList(endorsements), p / 2)

	endorsedBy := make(map[string]*ADEMToken)

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(emblem.Mem(), p)
	// @ invariant acc(endorsements, p) &&
	// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 		(i < i0 ==> acc(endorsements[i].ListElem(i), p / 2)) &&
	// @ 		(i0 <= i ==> acc(endorsements[i].ListElem(i), p)))
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy ==> let t, _ := endorsedBy[k] in acc(t.MapElem(k), p / 2)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(endorsement.ListElem(i0), p)
		// @ unfold acc(endorsement.Mem(), p)
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		// TODO: (lmeinen) not a registered claim - bugfix
		// TODO: (lmeinen) Return mem permissions from library
		// @ assume typeOf(end) == type[bool]
		// @ fold acc(endorsement.Mem(), p)
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if /*@ unfolding acc(emblem.Mem(), p) in unfolding acc(endorsement.Mem(), p) in @*/ emblem.Token.Issuer() != endorsement.Token.Issuer() {
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if /*@ unfolding acc(emblem.Mem(), p) in unfolding acc(endorsement.Mem(), p) in @*/ emblem.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if /*@ unfolding acc(emblem.Mem(), p) in @*/ kid != emblem.VerificationKey.KeyID( /*@ none[perm] @*/ ) && !end.(bool) {
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			// @ fold acc(endorsement.ListElem(i0), p)
			log.Println("illegal branch in endorsements")
			return []consts.VerificationResult{consts.INVALID}, nil
		} else {
			// @ fold acc(endorsement.ListElem(i0), p / 2)
			// @ fold acc(endorsement.MapElem(kid), p / 2)
			endorsedBy[kid] = endorsement
		}
	}

	// @ ghost prev := none[string]

	var root *ADEMToken
	trustedFound := false
	last := emblem

	// @ invariant acc(emblem.Mem(), p / 2)
	// @ invariant trustedKeys.Mem()
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant acc(endorsedBy) &&
	// @ 	forall k string :: { endorsedBy[k] } k in endorsedBy && some(k) != prev ==> let t, _ := endorsedBy[k] in acc(t.MapElem(k), p / 2)
	// @ invariant prev == none[string] ? last == emblem : (get(prev) in endorsedBy && endorsedBy[get(prev)] == last)
	// @ invariant acc(last.Mem(), p / 2)
	// @ invariant root != nil ==> root == last
	for root == nil {
		_, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(last.Mem(), p / 2) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ ))
		trustedFound = trustedFound || ok

		kid := /*@ unfolding acc(last.Mem(), p / 2) in @*/ last.VerificationKey.KeyID( /*@ none[perm] @*/ )
		if endorsing := endorsedBy[kid]; endorsing != nil {
			// @ ghost { if some(kid) != prev { unfold acc(endorsing.MapElem(kid), p / 2) } }
			if err := tokens.VerifyConstraints(
				/*@ unfolding acc(emblem.Mem(), p / 2) in @*/ emblem.Token,
				/*@ unfolding acc(endorsing.Mem(), p / 2) in @*/ endorsing.Token); err != nil {
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil
			} else {
				// @ ghost { if some(kid) != prev { fold acc(last.MapElem(get(prev)), p / 2) } }
				last = endorsing
				// @ prev = some(kid)
			}
		} else {
			root = last
		}
	}

	results := []consts.VerificationResult{consts.SIGNED}
	if trustedFound {
		results = append( /*@ perm(1/2), @*/ results, consts.SIGNED_TRUSTED)
	}

	// @ unfold acc(root.Mem(), p / 2)
	_, rootLogged := root.Token.Get("log")
	// @ fold acc(root.Mem(), p / 2)
	if /*@ unfolding acc(emblem.Mem(), p / 2) in @*/ emblem.Token.Issuer() != "" && !rootLogged {
		return []consts.VerificationResult{consts.INVALID}, nil
	} else if rootLogged {
		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID( /*@ unfolding acc(root.Mem(), p / 2) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ )); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
	}

	return results, root
}
