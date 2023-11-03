// +gobra
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
	FetchKeys(context.Context, KeySink, *Signature, *Message) error
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

func (s Signature) ProtectedHeaders() Headers

// Payload returns the decoded payload
func (m Message) Payload() []byte

func (m Message) Signatures() []*Signature

// Parse parses contents from the given source and creates a jws.Message
// struct. The input can be in either compact or full JSON serialization.
//
// Parse() currently does not take any options, but the API accepts it
// in anticipation of future addition.
func Parse(src []byte, _ ...ParseOption) (*Message, error)
