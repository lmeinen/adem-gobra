// +gobra
// ##(--onlyFilesWithHeader)

// sample entrypoint file
// @ initEnsures vfy.PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem() &&
// @ 	acc(&jwt.Custom, 1/2) &&
// @ 	acc(jwt.Custom, 1/2) &&
// @ 	tokens.CustomFields(jwt.Custom)
package main

import (
	"math/rand"

	// @ importRequires vfy.PkgMem()
	"github.com/adem-wg/adem-proto/pkg/vfy"

	// @ importRequires ident.PkgMem()
	// @ "github.com/adem-wg/adem-proto/pkg/ident"

	// @ importRequires roots.PkgMem()
	// @ "github.com/adem-wg/adem-proto/pkg/roots"

	// @ importRequires tokens.PkgMem() &&
	// @ 	acc(&jwt.Custom, 1/2) &&
	// @ 	acc(jwt.Custom, 1/2) &&
	// @ 	tokens.CustomFields(jwt.Custom)
	// @ "github.com/adem-wg/adem-proto/pkg/tokens"

	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "github.com/lestrrat-go/jwx/v2/jwt"
	// @ "place"
)

// @ requires vfy.PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem() &&
// @ 	acc(&jwt.Custom, 1/2) &&
// @ 	acc(jwt.Custom, 1/2) &&
// @ 	tokens.CustomFields(jwt.Custom)
func main() {
	// @ ghost t := place.Place.place(0)
	// fold place.token(t)
	vfy.VerifyTokens(rand.Uint64(), [][]byte{}, jwk.NewSet() /*@, t @*/)
}
