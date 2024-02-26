// +gobra
// ##(--onlyFilesWithHeader)
package jws

import (
	"context"

	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "lib"
	// @ "iospec"
	// @ "fact"
	// @ "term"
	// @ "place"
)

// The `sink` argument passed to the KeyProvider is a temporary storage
// for the keys (either a jwk.Key or a "raw" key). The `KeyProvider`
// is responsible for sending keys into the `sink`.

// KeySink is a data storage where `jws.KeyProvider` objects should
// send their keys to.
type KeySink interface {
	// @ requires acc(k.Mem(), _)
	Key(_ jwa.SignatureAlgorithm, k jwk.Key)
}

// KeyProvider is responsible for providing key(s) to sign or verify a payload.
// Multiple `jws.KeyProvider`s can be passed to `jws.Verify()` or `jws.Sign()`
type KeyProvider interface {
	// @ pred Mem()

	// @ requires Mem() && c != nil && sink != nil && acc(sig, _) && acc(m, _)
	// @ requires place.token(p) && iospec.P_TokenVerifier(p, rid, s) &&
	// @ 	fact.Setup_TokenVerifier(rid) in s && fact.PermitTokenVerificationIn_TokenVerifier(rid, tokenT) in s &&
	// @ 	m.AbsMsg() == lib.gamma(tokenT)
	FetchKeys(c context.Context, sink KeySink, sig *Signature, m *Message /*@, ghost p place.Place, ghost rid term.Term, ghost s mset[fact.Fact], ghost tokenT term.Term @*/) error
}

// Headers describe a standard Header set.
type Headers interface {

	// @ decreases _
	// @ pure
	Algorithm() jwa.SignatureAlgorithm

	// @ decreases _
	// @ pure
	ContentType() string

	// @ ensures res != nil && res.Mem()
	JWK() (res jwk.Key)

	// @ decreases _
	// @ pure
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
	protected Headers // Protected Headers
}

type Message struct {
	payload    []byte
	signatures []*Signature
}

// TODO: (lmeinen) Add proper preconditions

// @ trusted
// @ ensures h != nil && h === s.protected
func (s Signature) ProtectedHeaders() (h Headers) {
	return s.protected
}

// Payload returns the decoded payload
// @ trusted
// @ ensures acc(r, _) && lib.AbsBytes(r) == m.AbsMsg()
// @ ensures r === m.payload
func (m Message) Payload() (r []byte) {
	return m.payload
}

// @ trusted
// @ ensures acc(s, _) &&
// @ 	forall i int :: { s[i] } 0 <= i && i < len(s) ==> acc(s[i], _)
// @ ensures s === m.signatures
func (m Message) Signatures() (s []*Signature) {
	return m.signatures
}

/*@
ghost
pure
decreases _
func (m Message) AbsMsg() (ghost b lib.Bytes)
@*/

// Parse parses contents from the given source and creates a jws.Message
// struct. The input can be in either compact or full JSON serialization.
//
// Parse() currently does not take any options, but the API accepts it
// in anticipation of future addition.
// TODO: (lmeinen) Valid assumption w.r.t. len of msg.signatures? Check library implementation.
// @ requires acc(src, _)
// @ requires forall i int :: 0 <= i && i < len(options) ==> acc(&options[i] ,_) && options[i] != nil
// @ ensures err == nil ==> acc(msg)
func Parse(src []byte, options ...ParseOption) (msg *Message, err error)
