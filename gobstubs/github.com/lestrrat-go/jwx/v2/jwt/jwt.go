// +gobra
package jwt

import (
	"context"
	"time"

	"github.com/lestrrat-go/jwx/v2/jws"
)

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

func NewValidationError(err error) ValidationError

// FIXME: (lmeinen) Had to rename the Token type to JwtToken due to inexplicable Gobra 'duplicate identifier Token'
// 		errors - This will result in the project no longer running normally.

// JwtToken represents a generic JWT token.
// which are type-aware (to an extent). Other claims may be accessed via the `Get`/`Set`
// methods but their types are not taken into consideration at all. If you have non-standard
// claims that you must frequently access, consider creating accessors functions
// like the following
//
// func SetFoo(tok jwt.JwtToken) error
// func GetFoo(tok jwt.JwtToken) (*Customtyp, error)
//
// Embedding jwt.JwtToken into another struct is not recommended, because
// jwt.JwtToken needs to handle private claims, and this really does not
// work well when it is embedded in other structure
type JwtToken interface {

	// Expiration returns the value for "exp" field of the token
	Expiration() time.Time

	// IssuedAt returns the value for "iat" field of the token
	IssuedAt() time.Time

	// Issuer returns the value for "iss" field of the token
	Issuer() string

	// NotBefore returns the value for "nbf" field of the token
	NotBefore() time.Time

	// Subject returns the value for "sub" field of the token
	Subject() string

	// Get returns the value of the corresponding field in the token, such as
	// `nbf`, `exp`, `iat`, and other user-defined fields. If the field does not
	// exist in the token, the second return value will be `false`
	//
	// If you need to access fields like `alg`, `kid`, `jku`, etc, you need
	// to access the corresponding fields in the JWS/JWE message. For this,
	// you will need to access them by directly parsing the payload using
	// `jws.Parse` and `jwe.Parse`
	Get(string) (interface{}, bool)
}

// ValidateOption describes an Option that can be passed to Validate().
// ValidateOption also implements ParseOption, therefore it may be
// safely passed to `Parse()` (and thus `jwt.ReadFile()`)
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

// ParseOption describes an Option that can be passed to `jwt.Parse()`.
// ParseOption also implements ReadFileOption, therefore it may be
// safely pass them to `jwt.ReadFile()`
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

// Validator describes interface to validate a Token.
type Validator interface {
	// Validate should return an error if a required conditions is not met.
	Validate(c context.Context, t JwtToken) ValidationError
}

// ValidatorFunc is a type of Validator that does not have any
// state, that is implemented as a function
// type ValidatorFunc func(context.Context, JwtToken) ValidationError
// func (vf ValidatorFunc) Validate(ctx context.Context, tok JwtToken) ValidationError

// FIXME: (lmeinen) This is the only way I could find to deal with Gobra's limited support for function types
func ValidatorFunc(f func(context.Context, JwtToken) ValidationError) Validator

// RegisterCustomField allows users to specify that a private field
// be decoded as an instance of the specified type. This option has
// a global effect.
//
// For example, suppose you have a custom field `x-birthday`, which
// you want to represent as a string formatted in RFC3339 in JSON,
// but want it back as `time.Time`.
//
// In that case you would register a custom field as follows
//
//	jwt.RegisterCustomField(`x-birthday`, timeT)
//
// Then `token.Get("x-birthday")` will still return an `interface{}`,
// but you can convert its type to `time.Time`
//
//	bdayif, _ := token.Get(`x-birthday`)
//	bday := bdayif.(time.Time)
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
//
// For example, in order to validate tokens that are only valid during August, you would write
//
//	validator := jwt.ValidatorFunc(func(_ context.Context, t jwt.Token) error {
//		if time.Now().Month() != 8 {
//			return fmt.Errorf(`tokens are only valid during August!`)
//		}
//		return nil
//	})
//	err := jwt.Validate(token, jwt.WithValidator(validator))
func WithValidator(v Validator) ValidateOption

// WithKeyProvider allows users to specify an object to provide keys to
// sign/verify tokens using arbitrary code. Please read the documentation
// for `jws.KeyProvider` in the `jws` package for details on how this works.
func WithKeyProvider(v jws.KeyProvider) ParseOption

// Parse parses the JWT token payload and creates a new `jwt.Token` object.
// The token must be encoded in either JSON format or compact format.
//
// This function can only work with either raw JWT (JSON) and JWS (Compact or JSON).
// If you need JWE support on top of it, you will need to rollout your
// own workaround.
//
// If the token is signed and you want to verify the payload matches the signature,
// you must pass the jwt.WithKey(alg, key) or jwt.WithKeySet(jwk.Set) option.
// If you do not specify these parameters, no verification will be performed.
//
// During verification, if the JWS headers specify a key ID (`kid`), the
// key used for verification must match the specified ID. If you are somehow
// using a key without a `kid` (which is highly unlikely if you are working
// with a JWT from a well know provider), you can workaround this by modifying
// the `jwk.Key` and setting the `kid` header.
//
// If you also want to assert the validity of the JWT itself (i.e. expiration
// and such), use the `Validate()` function on the returned token, or pass the
// `WithValidate(true)` option. Validate options can also be passed to
// `Parse`
//
// This function takes both ParseOption and ValidateOption types:
// ParseOptions control the parsing behavior, and ValidateOptions are
// passed to `Validate()` when `jwt.WithValidate` is specified.
func Parse(s []byte, options ...ParseOption) (JwtToken, error)

// WithVerify is passed to `Parse()` method to denote that the
// signature verification should be performed after a successful
// deserialization of the incoming payload.
//
// This option is enabled by default.
//
// If you do not provide any verification key sources, `jwt.Parse()`
// would return an error.
//
// If you would like to only parse the JWT payload and not verify it,
// you must use `jwt.WithVerify(false)` or use `jwt.ParseInsecure()`
func WithVerify(v bool) ParseOption
