// +gobra
// ##(--onlyFilesWithHeader)
// @ initEnsures acc(&Custom) && acc(Custom) && Custom.IsEmpty()
package jwt

import (
	"context"
	"time"

	"github.com/lestrrat-go/jwx/v2/jws"
)

type Fields map[string]JwtClaim

var Custom /*@@@*/ Fields = NewMapping()

// @ ensures acc(f) && f.IsEmpty()
// @ decreases _
func NewMapping() (f Fields)

// @ ghost
// @ requires acc(f, _)
// @ ensures res ==> len(f) == 0
// @ decreases _
// @ pure
func (f Fields) IsEmpty() (res bool) {
	return len(f) == 0
}

/*@
pred Matches(f Fields) {
	acc(&Custom, _) &&
	acc(Custom, _) &&
	acc(f, _) &&
	domain(Custom) == domain(f) &&
	forall k string :: k in domain(Custom) ==> typeOf(Custom[k]) == typeOf(f[k])
}

pred BoolMem(_ bool) { true }
(bool) implements JwtClaim { pred Mem := BoolMem }

pred StringMem(_ string) { true }
(string) implements JwtClaim { pred Mem := StringMem }

pred IsValid(_ JwtToken) { true }

@*/

// @ ghost
// @ requires p > 0 && acc(f, p)
// @ ensures p > 0 && acc(f, p)
// @ ensures acc(r, _)
// @ ensures domain(f) == domain(r) &&
// @ 	forall k string :: k in domain(f) ==> f[k] === r[k]
// @ decreases _
func (f Fields) Copy( /*@ ghost p perm @*/ ) (r Fields)

// FIXME: (lmeinen) Had to rename the Token type to JwtToken due to inexplicable Gobra 'duplicate identifier Token'
// 		errors - This will result in the project no longer running normally.

type JwtClaim interface {
	// @ pred Mem()
}

// JwtToken represents a generic JWT token.
type JwtToken interface {

	// @ pred Mem()

	// Expiration returns the value for "exp" field of the token
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	Expiration() time.Time

	// IssuedAt returns the value for "iat" field of the token
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	IssuedAt() time.Time

	// Issuer returns the value for "iss" field of the token
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	Issuer() string

	// NotBefore returns the value for "nbf" field of the token
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	NotBefore() time.Time

	// Subject returns the value for "sub" field of the token
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	Subject() string

	// @ ghost
	// @ requires acc(Mem(), _)
	// @ decreases _
	// @ pure
	Contains(key string) bool

	// @ ghost
	// @ requires acc(Mem(), _)
	// @ requires acc(&Custom, _) && acc(Custom, _)
	// @ ensures Contains(key) ==> claim != nil
	// @ ensures Contains(key) && key in domain(Custom) ==> (
	// @		typeOf(claim) == typeOf(Custom[key]) &&
	// @ 		typeOf(claim) == type[JwtClaim])
	// @ decreases _
	// @ pure
	PureGet(key string) (claim any)

	// Get returns the value of the corresponding field in the token, such as
	// `nbf`, `exp`, `iat`, and other user-defined fields. If the field does not
	// exist in the token, the second return value will be `false`
	// TODO: (lmeinen) Though not strictly required for this project, we could add standard registered claims here, too
	// @ requires acc(Mem(), _)
	// @ requires acc(&Custom, _) && acc(Custom, _)
	// @ ensures acc(Mem(), _)
	// @ ensures acc(&Custom, _) && acc(Custom, _)
	// @ ensures Contains(key) == old(Contains(key))
	// @ ensures Contains(key) == ok
	// @ ensures claim === PureGet(key)
	Get(key string) (claim any, ok bool)
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
	// @ decreases _
	// @ pure
	Ident() any

	// Value returns the corresponding value.
	// @ decreases _
	// @ pure
	Value() any
	// ---------------------------------------------------------------

	parseOption()
	readFileOption()
	validateOption()
}

// Validator describes interface to validate a Token.
type Validator interface {
	// @ pred Mem()
	// @ pred Constraints(JwtToken)

	// Validate should return an error if a required conditions is not met.
	// @ preserves acc(Mem(), _) && acc(t.Mem(), _)
	// @ requires t != nil
	// @ ensures err == nil ==> Constraints(t)
	Validate(c context.Context, t JwtToken) (err ValidationError)
}

// @ ensures e != nil
// @ decreases
func NewValidationError(err error) (e ValidationError)

// RegisterCustomField allows users to specify that a private field
// be decoded as an instance of the specified type. This option has
// a global effect.
// @ requires acc(&Custom) && acc(Custom) && acc(fields, _)
// @ requires domain(fields) == domain(Custom) &&
// @ 	forall k string :: k in domain(fields) ==> fields[k] === Custom[k]
// @ ensures acc(&Custom) && acc(Custom) && acc(fields, _)
// @ ensures (forall k string :: k in domain(fields) ==> k in domain(Custom)) &&
// @ 	(forall k string :: k in domain(Custom) && k != name ==> k in domain(fields) && Custom[k] === fields[k])
// @ ensures name in domain(Custom) && Custom[name] === object
// @ decreases _
func RegisterCustomField(name string, object JwtClaim /*@, ghost fields Fields @*/)

// ErrInvalidIssuer returns the immutable error used when `iss` claim
// is not satisfied
//
// The return value should only be used for comparison using `errors.Is()`
func ErrInvalidIssuer() ValidationError

// Validate makes sure that the essential claims stand.
//
// See the various `WithXXX` functions for optional parameters
// that can control the behavior of this method.
// @ requires forall i int :: 0 <= i && i < len(options) ==> acc(&options[i]) && options[i] != nil
// @ ensures forall i int :: 0 <= i && i < len(options) ==> acc(&options[i]) && options[i] != nil && old(options)[i] === options[i]
// @ ensures e == nil  && len(options) == 0 ==> IsValid(t)
// @ ensures e == nil && forall i int :: 0 <= i && i < len(options) &&
// @ 	typeOf(options[i].Ident()) == type[identValidator] &&
// @ 	typeOf(options[i].Value()) == type[Validator] ==> (
// @ 		options[i].Value().(Validator).Constraints(t))
func Validate(t JwtToken, options ...ValidateOption) (e error)

type identValidator struct{}

// WithValidator validates the token with the given Validator.
// @ preserves acc(v.Mem(), _)
// @ ensures o != nil && typeOf(o.Ident()) == type[identValidator] && o.Value() === v && typeOf(o.Value()) == type[Validator]
func WithValidator(v Validator) (o ValidateOption)

// Parse parses the JWT token payload and creates a new `jwt.Token` object.
// The token must be encoded in either JSON format or compact format.
// @ preserves acc(&Custom, _) && acc(Custom, _)
// @ ensures err == nil ==> t != nil && t.Mem()
func Parse(s []byte, options ...ParseOption) (t JwtToken, err error)

// WithKeyProvider allows users to specify an object to provide keys to
// sign/verify tokens using arbitrary code.
// @ requires v.Mem()
func WithKeyProvider(v jws.KeyProvider) ParseOption

// WithVerify is passed to `Parse()` method to denote that the
// signature verification should be performed after a successful
// deserialization of the incoming payload.
func WithVerify(v bool) ParseOption
