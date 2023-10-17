// +gobra
// ##(--onlyFilesWithHeader)
package util

// @ requires pSlice > 0 && pSliceElem > 0
// @ requires isComparable(v)
// @ requires forall k int ::  0 <= k && k < len(slice) ==> acc(&slice[k], pSliceElem)
// @ requires forall k int ::  0 <= k && k < len(slice) ==> isComparable(slice[k]) && typeOf(slice[k]) == typeOf(v)
// @ preserves acc(slice, pSlice)
// @ ensures forall k int ::  0 <= k && k < len(slice) ==> acc(&slice[k], pSliceElem)
// @ ensures res ==> 0 <= idx && idx < len(slice) && slice[idx] == v
func Contains(slice []interface{}, v interface{} /*@, ghost pSlice, pSliceElem perm @*/) (res bool /*@, ghost idx int @*/) {
	//@ invariant acc(slice, pSlice)
	for i, elem := range slice {
		{
			if elem == v {
				return true //@ with: i
			}
		}
	}
	return false //@ with: 0 - 1
}
