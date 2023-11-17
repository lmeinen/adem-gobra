// +gobra
package json

// Unmarshal parses the JSON-encoded data and stores the result
// in the value pointed to by v. If v is nil or not a pointer,
// Unmarshal returns an InvalidUnmarshalError.
// @ preserves acc(data)
// @ preserves Mem()
func Unmarshal(data []byte, v any /*@, ghost Mem pred()@*/) (err error)

// Marshal returns the JSON encoding of v.
// @ ensures err == nil ==> acc(res)
func Marshal(v any) (res []byte, err error)
