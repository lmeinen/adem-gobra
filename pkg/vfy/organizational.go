// +gobra

package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/lestrrat-go/jwx/v2/jwk"
)

func verifySignedOrganizational(emblem *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set) ([]consts.VerificationResult, *ADEMToken) {
	endorsedBy := make(map[string]*ADEMToken)
	for _, endorsement := range endorsements {
		kid, err := tokens.GetEndorsedKID(endorsement.Token)
		end, _ := endorsement.Token.Get("end")
		if err != nil {
			log.Printf("could not get endorsed kid: %s\n", err)
			continue
		} else if emblem.Token.Issuer() != endorsement.Token.Issuer() {
			continue
		} else if emblem.Token.Issuer() != endorsement.Token.Subject() {
			continue
		} else if kid != emblem.VerificationKey.KeyID() && !end.(bool) {
			continue
		} else if _, ok := endorsedBy[kid]; ok {
			log.Println("illegal branch in endorsements")
			return []consts.VerificationResult{consts.INVALID}, nil
		} else {
			endorsedBy[kid] = endorsement
		}
	}

	var root *ADEMToken
	trustedFound := false
	last := emblem
	for root == nil {
		_, ok := trustedKeys.LookupKeyID(last.VerificationKey.KeyID())
		trustedFound = trustedFound || ok

		if endorsing := endorsedBy[last.VerificationKey.KeyID()]; endorsing != nil {
			if err := tokens.VerifyConstraints(emblem.Token, endorsing.Token); err != nil {
				log.Printf("emblem does not comply with endorsement constraints: %s", err)
				return []consts.VerificationResult{consts.INVALID}, nil
			} else {
				last = endorsing
			}
		} else {
			root = last
		}
	}

	results := []consts.VerificationResult{consts.SIGNED}
	if trustedFound {
		results = append( /*@ perm(1/2), @*/ results, consts.SIGNED_TRUSTED)
	}

	_, rootLogged := root.Token.Get("log")
	if emblem.Token.Issuer() != "" && !rootLogged {
		return []consts.VerificationResult{consts.INVALID}, nil
	} else if rootLogged {
		results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL)
		if _, ok := trustedKeys.LookupKeyID(root.VerificationKey.KeyID()); ok {
			results = append( /*@ perm(1/2), @*/ results, consts.ORGANIZATIONAL_TRUSTED)
		}
	}
	return results, root
}
