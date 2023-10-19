// +gobra

package util

import (
	"encoding/base64"
	//@ p "predicates"
)

// B64Dec decodes a base64-encoded string (represented as byte array) into a
// byte array.
// @ preserves p.BytesMem(src)
// @ ensures err == nil ==> p.BytesMem(res)
func B64Dec(src []byte) (res []byte, err error) {
	dst := make([]byte, base64.StdEncoding.DecodedLen(len(src)))
	//@ fold p.BytesMem(dst)
	n, err := base64.StdEncoding.Decode(dst, src)
	//@ unfold p.BytesMem(dst)
	if err != nil {
		return nil, err
	} else {
		res := dst[:n]
		//@ fold p.BytesMem(res)
		return res, nil
	}
}
