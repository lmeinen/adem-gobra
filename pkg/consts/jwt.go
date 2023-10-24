// +gobra
package consts

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

func (vr VerificationResult) String() string {
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
const ORGANIZATIONAL VerificationResult = 3
const ENDORSED VerificationResult = 4
const SIGNED_TRUSTED VerificationResult = 5
const ORGANIZATIONAL_TRUSTED VerificationResult = 6
const ENDORSED_TRUSTED VerificationResult = 7

// ------------------------------------------------------------------------------------------------------------------
