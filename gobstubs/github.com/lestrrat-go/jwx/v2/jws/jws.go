// +gobra
// ##(--onlyFilesWithHeader)
package jws

import (
	"context"

	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
)

// KeySink is a data storage where `jws.KeyProvider` objects should
// send their keys to.
type KeySink interface {
	Key(jwa.SignatureAlgorithm, interface{})
}

// KeyProvider is responsible for providing key(s) to sign or verify a payload.
// Multiple `jws.KeyProvider`s can be passed to `jws.Verify()` or `jws.Sign()`
type KeyProvider interface {
	// @ pred Mem()

	// @ requires Mem() && c != nil && sink != nil && acc(sig, _) && acc(m, _)
	FetchKeys(c context.Context, sink KeySink, sig *Signature, m *Message) error
}

// Headers describe a standard Header set.
type Headers interface {
	// pred Mem()

	// preserves p > 0 && acc(Mem(), p)
	Algorithm() jwa.SignatureAlgorithm

	// preserves p > 0 && acc(Mem(), p)
	ContentType() string

	// preserves p > 0 && acc(Mem(), p)
	// ensures acc(res.Mem(), _)
	// @ ensures res != nil
	JWK() (res jwk.Key)

	// preserves p > 0 && acc(Mem(), p)
	KeyID() string
}

type DecodeCtx interface {
	CollectRaw() bool
}

// ReadFileOption is a type of `Option` that can be passed to `jwe.Parse`
type ParseOption interface {
	// --- (lmeinen) replaces embedded option.Interface interface ---

	// Ident returns the "indentity" of this option, a unique identifier that
	// can be used to differentiate between options
	Ident() interface{}

	// Value returns the corresponding value.
	Value() interface{}
	// ---------------------------------------------------------------

	readFileOption()
}

type Signature struct {
	dc        DecodeCtx
	headers   Headers // Unprotected Headers
	protected Headers // Protected Headers
	signature []byte  // Signature
	detached  bool
}

type Message struct {
	dc         DecodeCtx
	payload    []byte
	signatures []*Signature
	b64        bool // true if payload should be base64 encoded
}

// @ ensures h != nil
func (s Signature) ProtectedHeaders() (h Headers)

// Payload returns the decoded payload
// @ ensures acc(r)
func (m Message) Payload() (r []byte)

// @ requires p > 0
// @ requires acc(m.signatures, p)
// @ requires forall i int :: 0 <= i && i < len(m.signatures) ==> acc(m.signatures[i], p)
// @ ensures acc(s, p)
// @ ensures forall i int :: 0 <= i && i < len(s) ==> acc(s[i], p)
// @ ensures len(m.signatures) == old(len(m.signatures))
// @ ensures len(s) == len(m.signatures)
// @ ensures forall i int :: 0 <= i && i < len(s) ==> old(m.signatures[i]) == s[i]
func (m Message) Signatures( /*@ ghost p perm @*/ ) (s []*Signature) {
	return m.signatures
}

// Parse parses contents from the given source and creates a jws.Message
// struct. The input can be in either compact or full JSON serialization.
//
// Parse() currently does not take any options, but the API accepts it
// in anticipation of future addition.
// TODO: (lmeinen) Valid assumption w.r.t. len of msg.signatures? Check library implementation.
// @ ensures err == nil ==> (
// @ 	acc(msg) &&
// @ 	acc(msg.payload) &&
// @ 	acc(msg.signatures) &&
// @ 	len(msg.signatures) > 0 &&
// @ 	forall i int :: 0 <= i && i < len(msg.signatures) ==> acc(msg.signatures[i]))
func Parse(src []byte, _ ...ParseOption) (msg *Message, err error)
