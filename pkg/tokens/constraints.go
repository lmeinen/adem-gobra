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
// @ requires emblem != nil
// @ requires acc(constraints.Assets) &&
// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> constraints.Assets[i].Mem()
func checkAssetConstraint(emblem jwt.Token, constraints EmblemConstraints) bool {
	// TODO: (lmeinen) Add constraints as precondition
	// @ assume emblem.Contains("ass")
	ass, _ := emblem.Get("ass")

	// FIXME: (lmeinen) Gobra can't parse the range expression properly when the type cast is inlined
	casted := ass.([]*ident.AI)
	// @ unfold AssMem(casted)

	// @ invariant acc(casted) &&
	// @ 	forall i int :: 0 <= i && i < len(casted) ==> casted[i].Mem()
	// @ invariant acc(constraints.Assets) &&
	// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> constraints.Assets[i].Mem()
	for _, ai := range casted {
		// FIXME: (lmeinen) Gobra parses unannotated Go code for reserved keywords - had to rename match variable to constraintFound
		constraintFound := false
		// @ invariant ai.Mem()
		// @ invariant acc(constraints.Assets) &&
		// @ 	forall i int :: 0 <= i && i < len(constraints.Assets) ==> constraints.Assets[i].Mem()
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
// @ requires emblem != nil
// @ requires endorsement != nil
func VerifyConstraints(emblem jwt.Token, endorsement jwt.Token) error {
	endCnstrs, ok := endorsement.Get("emb")
	if !ok {
		return nil
	} else {
		// @ unfold EmbMem(endCnstrs.(EmblemConstraints))
		if !checkAssetConstraint(emblem, endCnstrs.(EmblemConstraints)) {
			return /*@ unfolding acc(PkgMem(), _) in @*/ ErrAssetConstraint
		} else if embCnstrs, ok := emblem.Get("emb"); !ok {
			return nil
		} else {
			// @ unfold EmbMem(embCnstrs.(EmblemConstraints))
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
