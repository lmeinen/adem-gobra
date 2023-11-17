// +gobra
package io

// ReadCloser is the interface that groups the basic Read and Close methods.
type ReadCloser interface {
	Read(p []byte) (n int, err error)
	Close() error
}

// Reader is the interface that wraps the basic Read method.
type Reader interface {
	Read(p []byte) (n int, err error)
}

// ReadAll reads from r until an error or EOF and returns the data it read.
// @ ensures acc(bs)
func ReadAll(r Reader) (bs []byte, err error)
