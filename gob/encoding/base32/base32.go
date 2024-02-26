// +gobra
// ##(--onlyFilesWithHeader)
package base32

// @ import "strings"

// An Encoding is a radix 32 encoding/decoding scheme, defined by a
// 32-character alphabet. The most common is the "base32" encoding
// introduced for SASL GSSAPI and standardized in RFC 4648.
// The alternate "base32hex" encoding is used in DNSSEC.
type Encoding int

/*
We replace the var StdEncoding = NewEncoding(EncodingStd) with the below
to capture the intuition that StdEncoding is meant to be a constant value.
As the struct's fields are never directly accessed and Go doesn't support
const structs, we set the Encoding type to be an int.
*/
const StdEncoding Encoding = 0

// EncodeToString returns the base32 encoding of src.
// @ preserves forall i int :: 0 <= i && i < len(src) ==> acc(&src[i])
// @ ensures len(r) == EncodedLen(len(src))
// @ ensures len(strings.TrimRight(r, "=")) >= len(r) - 6 // See RFC 4648
func (enc Encoding) EncodeToString(src []byte) (r string)

// EncodedLen returns the length in bytes of the base32 encoding
// of an input buffer of length n.
// @ ghost
// @ requires n >= 0
// @ decreases _
// @ pure
func EncodedLen(n int) int {
	return (n + 4) / 5 * 8
}
