// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "lib"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "github.com/lestrrat-go/jwx/v2/jwa"
	// @ "github.com/lestrrat-go/jwx/v2/jwt"
)

// @ trusted
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves acc(EndorsementList(endorsements), _)
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires acc(Emblem(emblem), _)
// @ requires acc(ValidToken(root), _)
// @ requires trustedKeys != nil
// @ ensures endorsedResults != nil ==> (
// @	acc(endorsedResults) &&
// @	(!lib.GhostContainsResult(endorsedResults, consts.INVALID) ==> endorsedBy != nil))
// @ ensures endorsedBy != nil ==> acc(endorsedBy)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set) (endorsedResults []consts.VerificationResult, endorsedBy []string) {
	// @ unfold acc(EndorsementList(endorsements), _)
	// @ ghost defer fold acc(EndorsementList(endorsements), _)

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false
	// @ invariant acc(Emblem(emblem), _)
	// @ invariant acc(ValidToken(root), _)
	// @ invariant trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant issuers != nil && acc(issuers)
	// @ invariant acc(endorsements, _) &&
	// @ 	(forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> acc(EndListElem(i, endorsements[i]), _))
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(EndListElem(i0, endorsement), _)
		// @ unfold acc(Endorsement(endorsement), _)
		// @ unfold acc(ValidToken(endorsement), _)
		// @ unfold acc(Emblem(emblem), _)
		// @ unfold acc(ValidToken(emblem), _)
		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if /*@ unfolding acc(ValidToken(root), _) in @*/ root.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if endorsement.Token.Issuer() == "" {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if _, logged := endorsement.Token.Get("log"); !logged {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if /*@ unfolding acc(ValidToken(root), _) in @*/ root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			continue
		} else if err := tokens.VerifyConstraints(emblem.Token, endorsement.Token); err != nil {
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			x := []consts.VerificationResult{consts.INVALID}
			return x, nil
		} else {
			existsEndorsement = true
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
			trustedFound = trustedFound || ok
			// @ fold acc(Emblem(emblem), _)
			// @ fold acc(Endorsement(endorsement), _)
			// @ fold acc(EndListElem(i0, endorsement), _)
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
