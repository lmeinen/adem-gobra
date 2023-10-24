// +gobra
package merkleProof

// FIXME: (lmeinen) Had to rename this package from proof to merkleProof due to reserved Gobra keywords

import (
	"github.com/transparency-dev/merkle"
)

func VerifyInclusion(hasher merkle.LogHasher, index, size uint64, leafHash []byte, merkleProof [][]byte, root []byte) error
