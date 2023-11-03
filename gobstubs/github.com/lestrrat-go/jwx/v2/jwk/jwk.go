// +gobra
package jwk

import (
	"context"
	"github.com/lestrrat-go/iter/arrayiter"
	"github.com/lestrrat-go/jwx/v2/jwa"
)

// NewSet creates and empty `jwk.Set` object
// @ ensures s != nil
func NewSet() (s Set)

// ParseOption is a type of Option that can be passed to `jwk.Parse()`
type ParseOption interface {
	// --- (lmeinen) replaces embedded option.Interface interface ---

	// Ident returns the "indentity" of this option, a unique identifier that
	// can be used to differentiate between options
	Ident() interface{}

	// Value returns the corresponding value.
	Value() interface{}
	// ---------------------------------------------------------------

	fetchOption()
	registerOption()
	readFileOption()
}

// Set represents JWKS object, a collection of jwk.Key objects.
type Set interface {
	// pred Mem()

	// AddKey adds the specified key. If the key already exists in the set,
	// an error is returned.
	// preserves Mem() && acc(k.Mem(), _)
	AddKey(k Key) error

	// Keys creates an iterator to iterate through all keys in the set.
	// preserves acc(Mem(), _)
	// @ ensures res != nil
	Keys(context.Context) (res KeyIterator)

	// LookupKeyID returns the first key matching the given key id.
	// The second return value is false if there are no keys matching the key id.
	// preserves acc(Mem(), _)
	// @ ensures b ==> k != nil
	LookupKeyID(string) (k Key, b bool)
}

type KeyIterator = arrayiter.Iterator

const (
	KeyTypeKey                = "kty"
	KeyUsageKey               = "use"
	KeyOpsKey                 = "key_ops"
	AlgorithmKey              = "alg"
	KeyIDKey                  = "kid"
	X509URLKey                = "x5u"
	X509CertChainKey          = "x5c"
	X509CertThumbprintKey     = "x5t"
	X509CertThumbprintS256Key = "x5t#S256"
)

// Key defines the minimal interface for each of the
// key types.
type Key interface {
	// pred Mem()

	// Set sets the value of a single field. Note that certain fields,
	// notably "kty", cannot be altered, but will not return an error
	// preserves Mem()
	Set(string, interface{}) error

	// Remove removes the field associated with the specified key.
	// preserves Mem()
	Remove(string) error

	// PublicKey creates the corresponding PublicKey type for this object.
	// All fields are copied onto the new public key, except for those that are not allowed.
	// preserves acc(Mem(), _)
	PublicKey() (Key, error)

	// Algorithm returns `alg` of a JWK
	// preserves acc(Mem(), _)
	Algorithm() jwa.KeyAlgorithm

	// KeyID returns `kid` of a JWK
	// preserves acc(Mem(), _)
	KeyID() string
}

// ParseKey parses a single key JWK. Unlike `jwk.Parse` this method will
// report failure if you attempt to pass a JWK set. Only use this function
// when you know that the data is a single JWK.
// @ requires acc(data)
// @ ensures err != nil ==> k != nil
func ParseKey(data []byte, options ...ParseOption) (k Key, err error)
