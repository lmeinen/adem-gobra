// +gobra
// ##(--onlyFilesWithHeader)
package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
	// @ "lib"
)

// FIXME: (lmeinen) Needed two separate concrete type instantiations for generic Contains function

// @ preserves acc(slice, 1/2)
// @ ensures !res == forall j int :: { slice[j] } 0 <= j && j < len(slice) ==> slice[j] != v
func ContainsVerificationResult(slice []consts.VerificationResult, v consts.VerificationResult) (res bool) {
	// @ invariant acc(slice, 1/2)
	// @ invariant forall j int :: 0 <= j && j < i && j < len(slice) ==> slice[j] != v
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true
		}
	}
	return false
}

// @ preserves acc(slice, 1/2)
// @ ensures !res == forall j int :: { slice[j] } 0 <= j && j < len(slice) ==> slice[j] != v
func ContainsString(slice []string, v string) (res bool) {
	// @ invariant acc(slice, 1/2)
	// @ invariant forall j int :: 0 <= j && j < i && j < len(slice) ==> slice[j] != v
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true
		}
	}
	return false
}
