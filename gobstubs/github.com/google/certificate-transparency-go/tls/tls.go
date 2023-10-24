// +gobra

// Package tls implements functionality for dealing with TLS-encoded data,
// as defined in RFC 5246.  This includes parsing and generation of TLS-encoded
// data, together with utility functions for dealing with the DigitallySigned
// TLS type.
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

// Unmarshal parses the TLS-encoded data in b and uses the reflect package to
// fill in an arbitrary value pointed at by val.  Because Unmarshal uses the
// reflect package, the structs being written to must use exported fields
// (upper case names).
//
// The mappings between TLS types and Go types is as follows; some fields
// must have tags (to indicate their encoded size).
//
//	TLS		Go		Required Tags
//	opaque		byte / uint8
//	uint8		byte / uint8
//	uint16		uint16
//	uint24		tls.Uint24
//	uint32		uint32
//	uint64		uint64
//	enum		tls.Enum	size:S or maxval:N
//	Type<N,M>	[]Type		minlen:N,maxlen:M
//	opaque[N]	[N]byte / [N]uint8
//	uint8[N]	[N]byte / [N]uint8
//	struct { }	struct { }
//	select(T) {
//	 case e1: Type	*T		selector:Field,val:e1
//	}
//
// TLS variants (RFC 5246 s4.6.1) are only supported when the value of the
// associated enumeration type is available earlier in the same enclosing
// struct, and each possible variant is marked with a selector tag (to
// indicate which field selects the variants) and a val tag (to indicate
// what value of the selector picks this particular field).
//
// For example, a TLS structure:
//
//	enum { e1(1), e2(2) } EnumType;
//	struct {
//	   EnumType sel;
//	   select(sel) {
//	      case e1: uint16
//	      case e2: uint32
//	   } data;
//	} VariantItem;
//
// would have a corresponding Go type:
//
//	type VariantItem struct {
//	   Sel    tls.Enum  `tls:"maxval:2"`
//	   Data16 *uint16   `tls:"selector:Sel,val:1"`
//	   Data32 *uint32   `tls:"selector:Sel,val:2"`
//	 }
//
// TLS fixed-length vectors of types other than opaque or uint8 are not supported.
//
// For TLS variable-length vectors that are themselves used in other vectors,
// create a single-field structure to represent the inner type. For example, for:
//
//	opaque InnerType<1..65535>;
//	struct {
//	  InnerType inners<1,65535>;
//	} Something;
//
// convert to:
//
//	type InnerType struct {
//	   Val    []byte       `tls:"minlen:1,maxlen:65535"`
//	}
//	type Something struct {
//	   Inners []InnerType  `tls:"minlen:1,maxlen:65535"`
//	}
//
// If the encoded value does not fit in the Go type, Unmarshal returns a parse error.
func Unmarshal(b []byte, val interface{}) ([]byte, error)
