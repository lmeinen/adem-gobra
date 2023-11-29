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

// @ preserves p > 0
// @ preserves acc(emblem.Mem(), p)
// @ preserves acc(root.Mem(), p)
// @ preserves trustedKeys.Mem()
// @ preserves acc(TokenList(endorsements), p)
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires trustedKeys != nil
// @ ensures endorsedResults != nil ==> (
// @	acc(endorsedResults) &&
// @	(!goblib.GhostContainsResult(endorsedResults, consts.INVALID) ==> endorsedBy != nil))
// @ ensures endorsedBy != nil ==> acc(endorsedBy)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p perm @*/) (endorsedResults []consts.VerificationResult, endorsedBy []string) {
	// @ unfold acc(TokenList(endorsements), p)
	// @ ghost defer fold acc(TokenList(endorsements), p)

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false
	// @ invariant acc(emblem.Mem(), p)
	// @ invariant acc(root.Mem(), p)
	// @ invariant trustedKeys.Mem()
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant issuers != nil && acc(issuers)
	// @ invariant acc(endorsements, p) &&
	// @ 	(forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> acc(endorsements[i].ListElem(i), p))
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(endorsement.ListElem(i0), p)
		// @ unfold acc(endorsement.Mem(), p)
		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			// @ fold acc(endorsement.Mem(), p)
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if /*@ unfolding acc(root.Mem(), p) in @*/ root.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(endorsement.Mem(), p)
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else if endorsement.Token.Issuer() == "" {
			// @ fold acc(endorsement.Mem(), p)
			// @ fold acc(endorsement.ListElem(i0), p)
			continue
		} else {
			// TODO: (lmeinen) Add constraints as precondition
			// @ assume endorsement.Token.Contains("end")
			end, _ := endorsement.Token.Get("end")
			if !end.(bool) {
				// @ fold acc(endorsement.Mem(), p)
				// @ fold acc(endorsement.ListElem(i0), p)
				continue
			} else if /*@ unfolding acc(root.Mem(), p) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
				// @ fold acc(endorsement.Mem(), p)
				// @ fold acc(endorsement.ListElem(i0), p)
				continue
			} else if err := tokens.VerifyConstraints( /*@ unfolding acc(emblem.Mem(), p) in @*/ emblem.Token, endorsement.Token); err != nil {
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				// @ fold acc(endorsement.Mem(), p)
				// @ fold acc(endorsement.ListElem(i0), p)
				x := []consts.VerificationResult{consts.INVALID}
				return x, nil
			} else {
				existsEndorsement = true
				issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
				_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ))
				trustedFound = trustedFound || ok
				// @ fold acc(endorsement.Mem(), p)
				// @ fold acc(endorsement.ListElem(i0), p)
			}
		}
	}

	if existsEndorsement {
		results := []consts.VerificationResult{consts.ENDORSED}
		if trustedFound {
			results = append( /*@ perm(1/2), @*/ results, consts.ENDORSED_TRUSTED)
		}
		return results, issuers
	} else {
		return nil, nil
	}
}
