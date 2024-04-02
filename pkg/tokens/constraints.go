// +gobra
// ##(--onlyFilesWithHeader)
package tokens

import (
	"errors"

	"github.com/adem-wg/adem-proto/pkg/ident"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

// Check that the given emblem's ass claim complies with the given ass
// constraints.
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
// @ preserves emblem != nil && acc(emblem.Mem(), _) && emblem.Contains("ass") && acc(jwt.FieldMem(emblem.Values()), 1/8)
// @ preserves acc(constraints.Assets, 1/8) &&
// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> acc(constraints.Assets[i].Mem(), 1/8)
func checkAssetConstraint(emblem jwt.Token, constraints EmblemConstraints) bool {
	ass, _ := emblem.Get("ass")

	// FIXME: (lmeinen) Gobra can't parse the range expression properly when the type cast is inlined
	casted := ass.([]*ident.AI)
	// @ unfold acc(jwt.FieldMem(emblem.Values()), 1/8)
	// @ ghost defer fold acc(jwt.FieldMem(emblem.Values()), 1/8)
	// @ unfold acc(AssMem(casted), 1/8)
	// @ ghost defer fold acc(AssMem(casted), 1/8)

	// @ invariant acc(casted, 1/8) &&
	// @ 	forall i int :: 0 <= i && i < len(casted) ==> acc(casted[i].Mem(), 1/8)
	// @ invariant acc(constraints.Assets, 1/8) &&
	// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> acc(constraints.Assets[i].Mem(), 1/8)
	for _, ai := range casted {
		// FIXME: (lmeinen) Gobra parses unannotated Go code for reserved keywords - had to rename match variable to constraintFound
		constraintFound := false
		// @ invariant acc(ai.Mem(), 1/8)
		// @ invariant acc(constraints.Assets, 1/8) &&
		// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> acc(constraints.Assets[i].Mem(), 1/8)
		for _, constraint := range constraints.Assets {
			if constraint.MoreGeneral(ai) {
				constraintFound = true
				break
			}
		}
		if !constraintFound {
			return false
		}
	}

	return true
}

var ErrAssetConstraint = errors.New("emblem does not satisfy asset constraint")
var ErrPrpConstraint = errors.New("emblem does not satisfy prp constraint")
var ErrDstConstraint = errors.New("emblem does not satisfy dst constraint")
var ErrWndConstraint = errors.New("emblem does not satisfy wnd constraint")

// Verify that the given emblem complies with the given endorsement's
// constraints.
// @ preserves acc(PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
// @ preserves emblem != nil && acc(emblem.Mem(), _) && emblem.Contains("ass") && acc(jwt.FieldMem(emblem.Values()), 1/4)
// @ preserves endorsement != nil && acc(endorsement.Mem(), _) && acc(jwt.FieldMem(endorsement.Values()), 1/4)
func VerifyConstraints(emblem jwt.Token, endorsement jwt.Token) error {
	endCnstrs, ok := endorsement.Get("emb")
	// @ unfold acc(jwt.FieldMem(emblem.Values()), 1/8)
	// @ ghost defer fold acc(jwt.FieldMem(emblem.Values()), 1/8)
	// @ unfold acc(jwt.FieldMem(endorsement.Values()), 1/8)
	// @ ghost defer fold acc(jwt.FieldMem(endorsement.Values()), 1/8)
	if !ok {
		return nil
	} else {
		// @ unfold acc(EmbMem(endCnstrs.(EmblemConstraints)), 1/8)
		// @ ghost defer fold acc(EmbMem(endCnstrs.(EmblemConstraints)), 1/8)
		if !checkAssetConstraint(emblem, endCnstrs.(EmblemConstraints)) {
			return /*@ unfolding acc(PkgMem(), _) in @*/ ErrAssetConstraint
		} else if embCnstrs, ok := emblem.Get("emb"); !ok {
			return nil
		} else {
			// @ unfold acc(EmbMem(embCnstrs.(EmblemConstraints)), 1/8)
			// @ ghost defer fold acc(EmbMem(embCnstrs.(EmblemConstraints)), 1/8)
			embPrp := embCnstrs.(EmblemConstraints).Purpose
			endPrp := endCnstrs.(EmblemConstraints).Purpose
			if endPrp != nil && *endPrp&*embPrp != *embPrp {
				return /*@ unfolding acc(PkgMem(), _) in @*/ ErrPrpConstraint
			}
			embDst := embCnstrs.(EmblemConstraints).Distribution
			endDst := endCnstrs.(EmblemConstraints).Distribution
			if endDst != nil && *endDst&*embDst != *embDst {
				return /*@ unfolding acc(PkgMem(), _) in @*/ ErrDstConstraint
			}
			wnd := endCnstrs.(EmblemConstraints).Window
			if wnd != nil && emblem.Expiration().Unix()-emblem.NotBefore().Unix() > int64(*wnd) {
				return /*@ unfolding acc(PkgMem(), _) in @*/ ErrWndConstraint
			}
		}
	}
	return nil
}
