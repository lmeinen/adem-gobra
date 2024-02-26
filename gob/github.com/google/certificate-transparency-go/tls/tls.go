// +gobra
// ##(--onlyFilesWithHeader)
package tls

// Enum is an unsigned integer.
type Enum uint64

// DigitallySigned gives information about a signature, including the algorithm used
// and the signature value.  Defined in RFC 5246 s4.7.
type DigitallySigned struct {
	Algorithm SignatureAndHashAlgorithm
	Signature []byte `tls:"minlen:0,maxlen:65535"`
}

// SignatureAndHashAlgorithm gives information about the algorithms used for a
// signature.  Defined in RFC 5246 s7.4.1.4.1.
type SignatureAndHashAlgorithm struct {
	Hash      HashAlgorithm      `tls:"maxval:255"`
	Signature SignatureAlgorithm `tls:"maxval:255"`
}

// HashAlgorithm enum from RFC 5246 s7.4.1.4.1.
type HashAlgorithm Enum

// SignatureAlgorithm enum from RFC 5246 s7.4.1.4.1.
type SignatureAlgorithm Enum

type Parseable interface {
	// @ pred Mem()
}

// Unmarshal parses the TLS-encoded data in b and uses the reflect package to
// fill in an arbitrary value pointed at by val.  Because Unmarshal uses the
// reflect package, the structs being written to must use exported fields
// (upper case names).
// @ requires acc(b)
// @ ensures val.Mem()
func Unmarshal(b []byte, val Parseable) ([]byte, error)
