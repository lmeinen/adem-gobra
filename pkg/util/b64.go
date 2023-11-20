// +gobra
// ##(--onlyFilesWithHeader)
package util

import (
	"encoding/base64"
)

// B64Dec decodes a base64-encoded string (represented as byte array) into a
// byte array.
// @ preserves acc(src)
// @ ensures acc(res)
func B64Dec(src []byte) (res []byte, err error) {
	dst := make([]byte, base64.StdEncoding.DecodedLen(len(src)))
	n, err := base64.StdEncoding.Decode(dst, src)
	if err != nil {
		return nil, err
	} else {
		res := dst[:n]
		return res, nil
	}
}
