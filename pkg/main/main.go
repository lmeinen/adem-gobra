// +gobra
// ##(--onlyFilesWithHeader)

// sample entrypoint file
// @ initEnsures vfy.PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem() &&
// @ 	acc(&jwt.Custom, 1/2) &&
// @ 	acc(jwt.Custom, 1/2) &&
// @ 	tokens.CustomFields(jwt.Custom)
package main

import (
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
)

// @ requires vfy.PkgMem() && ident.PkgMem() && roots.PkgMem() && tokens.PkgMem() &&
// @ 	acc(&jwt.Custom, 1/2) &&
// @ 	acc(jwt.Custom, 1/2) &&
// @ 	tokens.CustomFields(jwt.Custom)
func main() {
	vfy.VerifyTokens([][]byte{}, jwk.NewSet())
}
