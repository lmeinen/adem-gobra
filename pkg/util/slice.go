// +gobra
package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
)

// FIXME: (lmeinen) Needed two separate concrete type instantiations for generic Contains function - maybe introduce a union type to ensure we only verify one function body?

// @ preserves p > 0
// @ preserves acc(slice, p)
// @ ensures res == goblib.GhostContainsResult(slice, v)
func ContainsVerificationResult(slice []consts.VerificationResult, v consts.VerificationResult /*@, ghost p perm @*/) (res bool) {
	//@ invariant acc(slice, p)
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true
		}
	}
	return false
}

// @ preserves p > 0
// @ preserves acc(slice, p)
// @ ensures res ==> 0 <= idx && idx < len(slice) && slice[idx] == v
func ContainsString(slice []string, v string /*@, ghost p perm @*/) (res bool /*@, ghost idx int @*/) {
	// @ invariant acc(slice, p)
	for _, elem := range slice /*@ with i @*/ {
		if elem == v {
			return true //@ with: i
		}
	}
	return false //@ with: 0 - 1
}
