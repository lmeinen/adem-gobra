// +gobra
// ##(--onlyFilesWithHeader)
package arrayiter

import (
	"context"
)

// Pair represents a single pair of key and value from a array
type Pair struct {
	Index int
	Value interface{}
}

// Iterator iterates through keys and values of a array
type Iterator interface {
	Next(context.Context) bool
	Pair() *Pair
}
