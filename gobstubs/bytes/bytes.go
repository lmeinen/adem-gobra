// +gobra
package bytes

// Equal reports whether a and b
// are the same length and contain the same bytes.
// A nil argument is equivalent to an empty slice.
// @ requires forall i int :: 0 <= i && i < len(a) ==> acc(&a[i], _)
// @ requires forall i int :: 0 <= i && i < len(b) ==> acc(&b[i], _)
// @ decreases
// @ pure
func Equal(a, b []byte) bool {
	// Neither cmd/compile nor gccgo allocates for these string conversions.
	return string(a) == string(b)
}

// Trim returns a subslice of s by slicing off all leading and
// trailing UTF-8-encoded code points contained in cutset.
// @ preserves forall i int :: 0 <= i && i < len(s) ==> acc(&s[i], _)
// @ ensures forall i int :: 0 <= i && i < len(res) ==> acc(&res[i], _)
func Trim(s []byte, cutset string) (res []byte)
