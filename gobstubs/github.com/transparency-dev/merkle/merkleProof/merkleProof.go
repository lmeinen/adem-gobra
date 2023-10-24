// +gobra
package merkleProof

import (
	"github.com/transparency-dev/merkle"
)

func VerifyInclusion(hasher merkle.LogHasher, index, size uint64, leafHash []byte, merkleProof [][]byte, root []byte) error
