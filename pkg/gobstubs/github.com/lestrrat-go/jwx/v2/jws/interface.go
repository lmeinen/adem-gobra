// +gobra

package jws

type DecodeCtx interface {
	CollectRaw() bool
}

type Signature struct {
	dc        DecodeCtx
	headers   Headers // Unprotected Headers
	protected Headers // Protected Headers
	signature []byte  // Signature
	detached  bool
}
