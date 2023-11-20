// +gobra
// ##(--onlyFilesWithHeader)
package sha256

// The size of a SHA256 checksum in bytes.
const Size = 32

// Sum256 returns the SHA256 checksum of the data.
// @ requires acc(data)
func Sum256(data []byte) [Size]byte
