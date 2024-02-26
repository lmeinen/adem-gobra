// +gobra
// ##(--onlyFilesWithHeader)
package merkleProof

// FIXME: (lmeinen) Had to rename this package from proof to merkleProof due to reserved Gobra keywords

import (
	"github.com/transparency-dev/merkle"
)

// @ preserves acc(leafHash)
// @ preserves acc(merkleProof) && forall i int :: { merkleProof[i] } 0 <= i && i < len(merkleProof) ==> acc(merkleProof[i])
// @ preserves acc(root)
func VerifyInclusion(hasher merkle.LogHasher, index, size uint64, leafHash []byte, merkleProof [][]byte, root []byte) error
