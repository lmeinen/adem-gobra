// +gobra
package jwt

import (
	"context"
	"time"

	"github.com/lestrrat-go/jwx/v2/jws"
)

// FIXME: (lmeinen) Had to rename the Token type to JwtToken due to inexplicable Gobra 'duplicate identifier Token'
// 		errors - This will result in the project no longer running normally.

// JwtToken represents a generic JWT token.
type JwtToken interface {
	// pred Mem()

	// Expiration returns the value for "exp" field of the token
	// preserves acc(Mem(), _)
	Expiration() time.Time

	// IssuedAt returns the value for "iat" field of the token
	// preserves acc(Mem(), _)
	IssuedAt() time.Time

	// Issuer returns the value for "iss" field of the token
	// preserves acc(Mem(), _)
	Issuer() string

	// NotBefore returns the value for "nbf" field of the token
	// preserves acc(Mem(), _)
	NotBefore() time.Time

	// Subject returns the value for "sub" field of the token
	// preserves acc(Mem(), _)
	Subject() string

	// Get returns the value of the corresponding field in the token, such as
	// `nbf`, `exp`, `iat`, and other user-defined fields. If the field does not
	// exist in the token, the second return value will be `false`
	// preserves p > 0 && acc(Mem(), p)
	Get(key string) (res interface{}, _ bool)
}

type ValidationError interface {
	// (lmeinen) Gobra doesn't appear to support embedding: needed to replace embedded error interface with builtin error interface
	// @ pred ErrorMem()

	// @ ghost
	// @ requires acc(ErrorMem(), _)
	// @ decreases
	// @ pure
	IsDuplicableMem() bool

	// @ ghost
	// @ preserves ErrorMem()
	// @ ensures   IsDuplicableMem() ==> ErrorMem()
	// @ decreases
	Duplicate()

	// @ preserves ErrorMem()
	// @ decreases
	Error() string

	isValidationError()
	Unwrap() error
}

// ParseOption describes an Option that can be passed to `jwt.Parse()`.
type ParseOption interface {
	// --- (lmeinen) replaces embedded option.Interface interface ---

	// Ident returns the "indentity" of this option, a unique identifier that
	// can be used to differentiate between options
	Ident() interface{}

	// Value returns the corresponding value.
	Value() interface{}
	// ---------------------------------------------------------------

	parseOption()
	readFileOption()
}

// ValidateOption describes an Option that can be passed to Validate().
type ValidateOption interface {
	// --- (lmeinen) replaces embedded option.Interface interface ---

	// Ident returns the "indentity" of this option, a unique identifier that
	// can be used to differentiate between options
	Ident() interface{}

	// Value returns the corresponding value.
	Value() interface{}
	// ---------------------------------------------------------------

	parseOption()
	readFileOption()
	validateOption()
}

// Validator describes interface to validate a Token.
type Validator interface {
	// Validate should return an error if a required conditions is not met.
	Validate(c context.Context, t JwtToken) ValidationError
}

func NewValidationError(err error) ValidationError

// RegisterCustomField allows users to specify that a private field
// be decoded as an instance of the specified type. This option has
// a global effect.
func RegisterCustomField(name string, object interface{})

// ErrInvalidIssuer returns the immutable error used when `iss` claim
// is not satisfied
//
// The return value should only be used for comparison using `errors.Is()`
func ErrInvalidIssuer() ValidationError

// Validate makes sure that the essential claims stand.
//
// See the various `WithXXX` functions for optional parameters
// that can control the behavior of this method.
func Validate(t JwtToken, options ...ValidateOption) error

// WithValidator validates the token with the given Validator.
func WithValidator(v Validator) ValidateOption

// Parse parses the JWT token payload and creates a new `jwt.Token` object.
// The token must be encoded in either JSON format or compact format.
// TODO: Use type constraints set in claims.go init function to return type guarantees
func Parse(s []byte, options ...ParseOption) (JwtToken, error)

// WithKeyProvider allows users to specify an object to provide keys to
// sign/verify tokens using arbitrary code.
func WithKeyProvider(v jws.KeyProvider) ParseOption

// WithVerify is passed to `Parse()` method to denote that the
// signature verification should be performed after a successful
// deserialization of the incoming payload.
func WithVerify(v bool) ParseOption
