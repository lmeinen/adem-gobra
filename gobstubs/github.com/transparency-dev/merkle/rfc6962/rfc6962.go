// +gobra
package rfc6962

import (
	"crypto"
	_ "crypto/sha256" // SHA256 is the default algorithm.
)

// DefaultHasher is a SHA256 based LogHasher.
var DefaultHasher = New(crypto.SHA256)

// Hasher implements the RFC6962 tree hashing algorithm.
type Hasher struct {
	hash uint
}

// New creates a new Hashers.LogHasher on the passed in hash function.
// @ decreases
func New(h crypto.Hash) *Hasher

// EmptyRoot returns a special case for an empty tree.
func (t *Hasher) EmptyRoot() []byte

// HashLeaf returns the Merkle tree leaf hash of the data passed in through leaf.
// The data in leaf is prefixed by the LeafHashPrefix.
func (t *Hasher) HashLeaf(leaf []byte) []byte

// HashChildren returns the inner Merkle tree node hash of the two child nodes l and r.
// The hashed structure is NodeHashPrefix||l||r.
func (t *Hasher) HashChildren(l, r []byte) []byte

// (lmeinen) placeholder function
func (t *Hasher) Size() int
