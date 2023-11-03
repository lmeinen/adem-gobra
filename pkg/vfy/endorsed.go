// +gobra
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
	"github.com/lestrrat-go/jwx/v2/jwk"
)

// @ trusted
// @ preserves acc(emblem.Mem(), _)
// @ preserves acc(root.Mem(), _)
// @ preserves p > 0 && acc(TokenList(endorsements), p)
// @ ensures endorsedResults != nil ==> (
// @	acc(endorsedResults) &&
// @	(!goblib.GhostContainsResult(endorsedResults, consts.INVALID) ==> endorsedBy != nil))
// @ ensures endorsedBy != nil ==> acc(endorsedBy)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost p perm @*/) (endorsedResults []consts.VerificationResult, endorsedBy []string) {
	issuers := []string{}
	trustedFound := false
	existsEndorsement := false
	for _, endorsement := range endorsements {
		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			continue
		} else if root.Token.Issuer() != endorsement.Token.Subject() {
			continue
		} else if endorsement.Token.Issuer() == "" {
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			continue
		} else if root.VerificationKey.KeyID() != endorsedKID {
			continue
		} else if err := tokens.VerifyConstraints(emblem.Token, endorsement.Token); err != nil {
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			return []consts.VerificationResult{consts.INVALID}, nil
		} else {
			existsEndorsement = true
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID())
			trustedFound = trustedFound || ok
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
