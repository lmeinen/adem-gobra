// +gobra
// ##(--onlyFilesWithHeader)
package jsoncanonicalizer

// @ preserves forall i int :: 0 <= i && i < len(jsonData) ==> acc(&jsonData[i])
// @ ensures forall i int :: 0 <= i && i < len(result) ==> acc(&result[i])
// @ ensures e != nil ==> e.ErrorMem()
func Transform(jsonData []byte) (result []byte, e error)
