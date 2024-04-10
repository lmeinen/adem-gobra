// +gobra
// ##(--onlyFilesWithHeader)
package consts

/*@
import (
	"claim"
	"fact"
	"place"
	"iospec"
	"term"
	"pub"
	"fresh"
)
@*/

type CTY string

const EmblemCty CTY = "adem-emb"
const EndorsementCty CTY = "adem-end"

type Version string

const V1 Version = "v1"

const UDP string = "udp"
const DNS string = "dns"
const TLS string = "tls"

const Protective string = "protective"
const Indicative string = "indicative"

// (lmeinen) --- moved from vfy.go to allow concrete type instantiation of ContainsVerificationResult in slice.go ---
type VerificationResult byte

// @ trusted
func (vr VerificationResult) String( /*@ ghost p place.Place, ghost s mset[fact.Fact], ghost rid, t, ai, oi term.Term @*/ ) (r string /*@, ghost p0 place.Place @*/) {
	switch vr {
	case UNSIGNED:
		return "UNSIGNED"
	case INVALID:
		return "INVALID"
	case SIGNED:
		return "SIGNED"
	case ORGANIZATIONAL:
		return "ORGANIZATIONAL"
	case ENDORSED:
		return "ENDORSED"
	case SIGNED_TRUSTED:
		return "SIGNED_TRUSTED"
	case ORGANIZATIONAL_TRUSTED:
		return "ORGANIZATIONAL_TRUSTED"
	case ENDORSED_TRUSTED:
		return "ENDORSED_TRUSTED"
	default:
		return ""
	}
}

const UNSIGNED VerificationResult = 0
const INVALID VerificationResult = 1
const SIGNED VerificationResult = 2
const SIGNED_TRUSTED VerificationResult = 3
const ORGANIZATIONAL VerificationResult = 4
const ORGANIZATIONAL_TRUSTED VerificationResult = 5
const ENDORSED VerificationResult = 6
const ENDORSED_TRUSTED VerificationResult = 7

// ------------------------------------------------------------------------------------------------------------------
