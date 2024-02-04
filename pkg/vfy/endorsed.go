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
// @ preserves acc(Emblem(emblem), p)
// @ preserves acc(ValidToken(root), p)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves acc(EndorsementList(endorsements), p)
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires trustedKeys != nil
// @ ensures endorsedResults != nil ==> (
// @	acc(endorsedResults) &&
// @	(!goblib.GhostContainsResult(endorsedResults, consts.INVALID) ==> endorsedBy != nil))
// @ ensures endorsedBy != nil ==> acc(endorsedBy)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p perm @*/) (endorsedResults []consts.VerificationResult, endorsedBy []string) {
	// @ unfold acc(EndorsementList(endorsements), p)
	// @ ghost defer fold acc(EndorsementList(endorsements), p)

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false
	// @ invariant acc(Emblem(emblem), p)
	// @ invariant acc(ValidToken(root), p)
	// @ invariant trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant issuers != nil && acc(issuers)
	// @ invariant acc(endorsements, p) &&
	// @ 	(forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> acc(EndListElem(i, endorsements[i]), p))
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(EndListElem(i0, endorsement), p)
		// @ unfold acc(Endorsement(endorsement), p)
		// @ unfold acc(ValidToken(endorsement), p / 2)
		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			continue
		} else if /*@ unfolding acc(ValidToken(root), p) in @*/ root.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			continue
		} else if endorsement.Token.Issuer() == "" {
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			continue
		} else if /*@ unfolding acc(ValidToken(root), p) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			continue
		} else if err := tokens.VerifyConstraints( /*@ unfolding acc(Emblem(emblem), p) in unfolding acc(ValidToken(emblem), p / 2) in @*/ emblem.Token, endorsement.Token); err != nil {
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			x := []consts.VerificationResult{consts.INVALID}
			return x, nil
		} else {
			existsEndorsement = true
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
			trustedFound = trustedFound || ok
			// @ fold acc(ValidToken(endorsement), p / 2)
			// @ fold acc(Endorsement(endorsement), p)
			// @ fold acc(EndListElem(i0, endorsement), p)
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
