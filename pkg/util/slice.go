// +gobra
package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
)

// FIXME: (lmeinen) Needed two separate concrete type instantiations for generic Contains function - maybe introduce a union type to ensure we only verify one function body?

func ContainsVerificationResult(slice []consts.VerificationResult, v consts.VerificationResult) (res bool) {
	for _, elem := range slice {
		{
			if elem == v {
				return true
			}
		}
	}
	return false
}

func ContainsString(slice []string, v string) (res bool) {
	for _, elem := range slice {
		{
			if elem == v {
				return true
			}
		}
	}
	return false
}
