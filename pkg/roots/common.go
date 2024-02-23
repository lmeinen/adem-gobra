// +gobra
// ##(--onlyFilesWithHeader)
package roots

import (
	"errors"
	"log"
	"math/rand"

	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "fact"
	// @ "fresh"
	// @ "iospec"
	// @ "place"
	// @ "term"
)

var ErrNoLogConfig = errors.New("no log claim")

type VerificationResult struct {
	LogURL string
	LogID  string
	Ok     bool
}

// Verify that the given key was correctly committed to the Certificate
// Transparency infrastructure for the given issuer.
// @ preserves acc(PkgMem(), _)
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves key != nil && key.Mem()
// @ requires acc(logs) &&
// @ 	forall i int :: 0 <= i && i < len(logs) ==> acc(logs[i]) && acc(logs[i].Hash.Raw)
// @ ensures acc(r) &&
// @ 	forall i int :: 0 <= i && i < len(r) ==> acc(r[i]) && (r[i].Ok ==> iss != "")
// @ ensures len(r) == len(logs)
func VerifyBindingCerts(iss string, key jwk.Key, logs []*tokens.LogConfig) (r []*VerificationResult) {
	// FIXME: (lmeinen) Gobra doesn't support slices of structs - refactored to pointers
	verified := []*VerificationResult{}
	// @ invariant acc(PkgMem(), _)
	// @ invariant key.Mem()
	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(logs, _)
	// @ invariant forall i int :: 0 <= i && i < len(logs) ==> acc(logs[i]) && acc(logs[i].Hash.Raw)
	// @ invariant acc(verified) &&
	// @ 	forall i int :: { verified[i] } 0 <= i && i < len(verified) ==> acc(verified[i]) && (verified[i].Ok ==> iss != "")
	// @ invariant (0 <= i0 && i0 <= len(logs) ==> len(verified) == i0)
	for _, logConfig := range logs /*@ with i0 @*/ {
		result := &VerificationResult{LogID: logConfig.Id}
		if logConfig.Ver != "v1" {
			log.Printf("log %s illegal version", logConfig.Id)
			result.Ok = false
		} else if cl, err := GetLogClient(logConfig.Id); err != nil {
			log.Print("could not get log client")
			result.Ok = false
		} else {
			result.LogURL = cl.BaseURI()

			err := VerifyBinding(cl, logConfig.Hash.Raw, iss, key)
			if err != nil {
				log.Printf("not verify binding: %s", err)
			}
			result.Ok = err == nil
		}
		verified = append( /*@ perm(1/2), @*/ verified, result)
	}
	return verified
}
