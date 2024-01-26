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

	// @ ghost
	// @ pure PredSeq() (ghost seq[pred(any)])

	// @ ghost
	// @ ensures r >= 0
	// @ pure Index() (r int)

	// @ ensures r == (len(PredSeq()) > 0)
	// @ ensures old(PredSeq()) == PredSeq()
	// @ ensures old(Index()) == Index()
	Next(context.Context) (r bool)

	// @ requires len(PredSeq()) > 0
	// @ ensures Index() == old(Index()) + 1
	// @ ensures PredSeq() == old(PredSeq())[1:]
	// @ ensures res != nil && acc(res, _)
	// @ ensures res.Index == old(Index())
	// @ ensures old(PredSeq())[0](res.Value)
	Pair() (res *Pair)
}
