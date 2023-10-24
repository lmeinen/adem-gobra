// +gobra
package jwk

import (
	"context"
	"github.com/lestrrat-go/iter/arrayiter"
	"github.com/lestrrat-go/jwx/v2/jwa"
)

// NewSet creates and empty `jwk.Set` object
func NewSet() Set

// ParseOption is a type of Option that can be passed to `jwk.Parse()`
// ParseOption also implmentsthe `ReadFileOption` and `CacheOption`,
// and thus safely be passed to `jwk.ReadFile` and `(*jwk.Cache).Configure()`
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
//
// Sets can be safely converted to and from JSON using the standard
// `"encoding/json".Marshal` and `"encoding/json".Unmarshal`. However,
// if you do not know if the payload contains a single JWK or a JWK set,
// consider using `jwk.Parse()` to always get a `jwk.Set` out of it.
//
// Since v1.2.12, JWK sets with private parameters can be parsed as well.
// Such private parameters can be accessed via the `Field()` method.
// If a resource contains a single JWK instead of a JWK set, private parameters
// are stored in _both_ the resulting `jwk.Set` object and the `jwk.Key` object .
//
//nolint:interfacebloat
type Set interface {
	// AddKey adds the specified key. If the key already exists in the set,
	// an error is returned.
	AddKey(Key) error

	// Keys creates an iterator to iterate through all keys in the set.
	Keys(context.Context) KeyIterator

	// LookupKeyID returns the first key matching the given key id.
	// The second return value is false if there are no keys matching the key id.
	// The set *may* contain multiple keys with the same key id. If you
	// need all of them, use `Iterate()`
	LookupKeyID(string) (Key, bool)
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
// key types. Their use and implementation differ significantly
// between each key types, so you should use type assertions
// to perform more specific tasks with each key
type Key interface {
	// Set sets the value of a single field. Note that certain fields,
	// notably "kty", cannot be altered, but will not return an error
	//
	// This method, which takes an `interface{}`, exists because
	// these objects can contain extra _arbitrary_ fields that users can
	// specify, and there is no way of knowing what type they could be
	Set(string, interface{}) error

	// Remove removes the field associated with the specified key.
	// There is no way to remove the `kty` (key type). You will ALWAYS be left with one field in a jwk.Key.
	Remove(string) error

	// PublicKey creates the corresponding PublicKey type for this object.
	// All fields are copied onto the new public key, except for those that are not allowed.
	//
	// If the key is already a public key, it returns a new copy minus the disallowed fields as above.
	PublicKey() (Key, error)

	// Algorithm returns `alg` of a JWK

	// Algorithm returns the value of the `alg` field
	//
	// This field may contain either `jwk.SignatureAlgorithm` or `jwk.KeyEncryptionAlgorithm`.
	// This is why there exists a `jwa.KeyAlgorithm` type that encompases both types.
	Algorithm() jwa.KeyAlgorithm
	// KeyID returns `kid` of a JWK
	KeyID() string
}

// ParseKey parses a single key JWK. Unlike `jwk.Parse` this method will
// report failure if you attempt to pass a JWK set. Only use this function
// when you know that the data is a single JWK.
//
// Given a WithPEM(true) option, this function assumes that the given input
// is PEM encoded ASN.1 DER format key.
//
// Note that a successful parsing of any type of key does NOT necessarily
// guarantee a valid key. For example, no checks against expiration dates
// are performed for certificate expiration, no checks against missing
// parameters are performed, etc.
// @ preserves forall i int :: 0 <= i && i < len(data) ==> acc(&data[i], _)
func ParseKey(data []byte, options ...ParseOption) (Key, error)
