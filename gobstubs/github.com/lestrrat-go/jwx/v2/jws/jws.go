// +gobra
package jws

import (
	"context"

	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
)

// KeyProvider is responsible for providing key(s) to sign or verify a payload.
// Multiple `jws.KeyProvider`s can be passed to `jws.Verify()` or `jws.Sign()`
//
// `jws.Sign()` can only accept static key providers via `jws.WithKey()`,
// while `jws.Verify()` can accept `jws.WithKey()`, `jws.WithKeySet()`,
// `jws.WithVerifyAuto()`, and `jws.WithKeyProvider()`.
//
// Understanding how this works is crucial to learn how this package works.
//
// `jws.Sign()` is straightforward: signatures are created for each
// provided key.
//
// `jws.Verify()` is a bit more involved, because there are cases you
// will want to compute/deduce/guess the keys that you would like to
// use for verification.
//
// The first thing that `jws.Verify()` does is to collect the
// KeyProviders from the option list that the user provided (presented in pseudocode):
//
//	keyProviders := filterKeyProviders(options)
//
// Then, remember that a JWS message may contain multiple signatures in the
// message. For each signature, we call on the KeyProviders to give us
// the key(s) to use on this signature:
//
//	for sig in msg.Signatures {
//	  for kp in keyProviders {
//	    kp.FetcKeys(ctx, sink, sig, msg)
//	    ...
//	  }
//	}
//
// The `sink` argument passed to the KeyProvider is a temporary storage
// for the keys (either a jwk.Key or a "raw" key). The `KeyProvider`
// is responsible for sending keys into the `sink`.
//
// When called, the `KeyProvider` created by `jws.WithKey()` sends the same key,
// `jws.WithKeySet()` sends keys that matches a particular `kid` and `alg`,
// `jws.WithVerifyAuto()` fetchs a JWK from the `jku` URL,
// and finally `jws.WithKeyProvider()` allows you to execute arbitrary
// logic to provide keys. If you are providing a custom `KeyProvider`,
// you should execute the necessary checks or retrieval of keys, and
// then send the key(s) to the sink:
//
//	sink.Key(alg, key)
//
// These keys are then retrieved and tried for each signature, until
// a match is found:
//
//	keys := sink.Keys()
//	for key in keys {
//	  if givenSignature == makeSignatre(key, payload, ...)) {
//	    return OK
//	  }
//	}
type KeyProvider interface {
	FetchKeys(context.Context, KeySink, *Signature, *Message) error
}

// Headers describe a standard Header set.
type Headers interface {
	Algorithm() jwa.SignatureAlgorithm
	ContentType() string
	JWK() jwk.Key
	KeyID() string
}

type DecodeCtx interface {
	CollectRaw() bool
}

// KeySink is a data storage where `jws.KeyProvider` objects should
// send their keys to.
type KeySink interface {
	Key(jwa.SignatureAlgorithm, interface{})
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

// Payload returns the decoded payload
func (m Message) Payload() []byte

func (s Signature) ProtectedHeaders() Headers

func (m Message) Signatures() []*Signature

// Parse parses contents from the given source and creates a jws.Message
// struct. The input can be in either compact or full JSON serialization.
//
// Parse() currently does not take any options, but the API accepts it
// in anticipation of future addition.
func Parse(src []byte, _ ...ParseOption) (*Message, error)
