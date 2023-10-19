// +gobra
// ##(--onlyFilesWithHeader)
package jws

import (
	"github.com/lestrrat-go/jwx/v2/jwa"
)

// Headers describe a standard Header set.
type Headers interface {
	Algorithm() jwa.SignatureAlgorithm
	ContentType() string
}
