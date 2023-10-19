// +gobra

package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
)

// @ preserves pSlice > 0 && pSliceElem > 0
// @ preserves acc(slice, pSlice)
// @ preserves forall k int ::  0 <= k && k < len(slice) ==> acc(&slice[k], pSliceElem)
// @ ensures res ==> 0 <= idx && idx < len(slice) && slice[idx] == v
func ContainsVerificationResult(slice []consts.VerificationResult, v consts.VerificationResult /*@, ghost pSlice, pSliceElem perm @*/) (res bool /*@, ghost idx int @*/) {
	//@ invariant acc(slice, pSlice)
	for i, elem := range slice {
		{
			noop(i) // needed to avoid Go compiler error due to unused variable i
			if elem == v {
				return true //@ with: i
			}
		}
	}
	return false //@ with: 0 - 1
}

// @ preserves pSlice > 0 && pSliceElem > 0
// @ preserves acc(slice, pSlice)
// @ preserves forall k int ::  0 <= k && k < len(slice) ==> acc(&slice[k], pSliceElem)
// @ ensures res ==> 0 <= idx && idx < len(slice) && slice[idx] == v
func ContainsString(slice []string, v string /*@, ghost pSlice, pSliceElem perm @*/) (res bool /*@, ghost idx int @*/) {
	// @ invariant acc(slice, pSlice)
	for i, elem := range slice {
		{
			noop(i) // needed to avoid Go compiler error due to unused variable i
			if elem == v {
				return true //@ with: i
			}
		}
	}
	return false //@ with: 0 - 1
}

func noop(_ int) {
	// noop
}
