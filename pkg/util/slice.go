// +gobra

package util

import (
	"github.com/adem-wg/adem-proto/pkg/consts"
)

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
