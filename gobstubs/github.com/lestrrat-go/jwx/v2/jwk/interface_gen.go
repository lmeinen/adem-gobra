// +gobra

package jwk

import (
	"github.com/lestrrat-go/jwx/v2/jwa"
)

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
