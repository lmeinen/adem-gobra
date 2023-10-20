// +gobra

// Package merkle provides Merkle tree interfaces and implementation.
package merkle

// LogHasher provides the hash functions needed to compute dense merkle trees.
type LogHasher interface {
	// EmptyRoot supports returning a special case for the root of an empty tree.
	EmptyRoot() []byte
	// HashLeaf computes the hash of a leaf that exists.
	HashLeaf(leaf []byte) []byte
	// HashChildren computes interior nodes.
	HashChildren(l, r []byte) []byte
	// Size returns the number of bytes the Hash* functions will return.
	Size() int
}
