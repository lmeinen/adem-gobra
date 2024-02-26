// +gobra
// ##(--onlyFilesWithHeader)
package jsoncanonicalizer

// @ requires acc(jsonData)
// @ ensures acc(result)
func Transform(jsonData []byte) (result []byte, e error)
