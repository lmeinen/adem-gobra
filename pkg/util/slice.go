// +gobra
// ##(--onlyFilesWithHeader)
package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
)

// FIXME: (lmeinen) Needed two separate concrete type instantiations for generic Contains function

// @ preserves p > 0
// @ preserves acc(slice, p)
// @ ensures res == goblib.GhostContainsResult(slice, v)
func ContainsVerificationResult(slice []consts.VerificationResult, v consts.VerificationResult /*@, ghost p perm @*/) (res bool) {
	// @ invariant acc(slice, p)
	// @ invariant forall j int :: 0 <= j && j < i && j < len(slice) ==> slice[j] != v
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true
		}
	}
	return false
}

// @ preserves p > 0
// @ preserves acc(slice, p)
// @ ensures res == goblib.GhostContainsString(slice, v)
func ContainsString(slice []string, v string /*@, ghost p perm @*/) (res bool) {
	// @ invariant acc(slice, p)
	// @ invariant forall j int :: 0 <= j && j < i && j < len(slice) ==> slice[j] != v
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true
		}
	}
	return false
}
