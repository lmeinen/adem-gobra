// +gobra
// ##(--onlyFilesWithHeader)
package base64

// An Encoding is a radix 64 encoding/decoding scheme, defined by a
// 64-character alphabet. The most common encoding is the "base64"
// encoding defined in RFC 4648 and used in MIME (RFC 2045) and PEM
// (RFC 1421).  RFC 4648 also defines an alternate encoding, which is
// the standard encoding with - and _ substituted for + and /.
type Encoding int

/*
We replace the var StdEncoding = NewEncoding(EncodingStd) with the below
to capture the intuition that StdEncoding is meant to be a constant value.
As the struct's fields are never directly accessed and Go doesn't support
const structs, we set the Encoding type to be an int.
*/
const StdEncoding Encoding = 0

// DecodedLen returns the maximum length in bytes of the decoded data
// corresponding to n bytes of base64-encoded data.
// @ ensures n >= 0 ==> res >= 0
// @ pure
func (enc Encoding) DecodedLen(n int) (res int)

// Decode decodes src using the encoding enc. It writes at most
// DecodedLen(len(src)) bytes to dst and returns the number of bytes
// written. If src contains invalid base64 data, it will return the
// number of bytes successfully written and CorruptInputError.
// New line characters (\r and \n) are ignored.
// @ preserves forall i int :: 0 <= i && i < len(dst) ==> acc(&dst[i])
// @ preserves forall i int :: 0 <= i && i < len(src) ==> acc(&src[i])
// @ ensures 0 <= n && n <= len(dst)
// @ ensures err.ErrorMem()
func (enc Encoding) Decode(dst, src []byte) (n int, err error)
