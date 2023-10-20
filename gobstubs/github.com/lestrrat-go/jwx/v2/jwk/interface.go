// +gobra

package jwk

import (
	"context"
	"github.com/lestrrat-go/iter/arrayiter"
)

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
}

type KeyIterator = arrayiter.Iterator
