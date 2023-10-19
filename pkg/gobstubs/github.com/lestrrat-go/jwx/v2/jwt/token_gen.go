// +gobra
// ##(--onlyFilesWithHeader)
package jwt

import (
	"time"
)

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
