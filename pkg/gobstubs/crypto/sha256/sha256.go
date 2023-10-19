// +gobra

// Package sha256 implements the SHA224 and SHA256 hash algorithms as defined
// in FIPS 180-4.
package sha256

// The size of a SHA256 checksum in bytes.
const Size = 32

// Sum256 returns the SHA256 checksum of the data.
// @ preserves forall i int :: 0 <= i && i < len(data) ==> acc(&data[i])
func Sum256(data []byte) [Size]byte
