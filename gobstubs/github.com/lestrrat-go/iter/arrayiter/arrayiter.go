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

	// @ pred IterMem()

	// @ ghost
	// @ requires acc(IterMem(), _)
	// @ decreases _
	// @ pure GetIterSeq() (ghost seq[any])

	// @ ghost
	// @ requires acc(IterMem(), _)
	// @ ensures 0 <= r
	// @ decreases _
	// @ pure Index() (r int)

	// @ preserves IterMem()
	// @ ensures GetIterSeq() == old(GetIterSeq())
	// @ ensures Index() == old(Index()) + 1
	// @ ensures r ==> (Index() < len(GetIterSeq()))
	Next(context.Context) (r bool)

	// @ requires p > 0 && acc(IterMem(), p)
	// @ requires Index() < len(GetIterSeq())
	// @ ensures acc(IterMem(), old(p))
	// @ ensures Index() == old(Index())
	// @ ensures GetIterSeq() == old(GetIterSeq())
	// @ ensures res != nil && acc(res, _)
	// @ ensures res.Index == Index()
	// @ ensures res.Value === GetIterSeq()[Index()]
	Pair( /*@ ghost p perm @*/ ) (res *Pair)
}

// @ requires iter != nil && iter.IterMem()
// @ ensures true
func BadSpec(iter Iterator) {
	if iter.Next(context.TODO()) {
		// @ assert iter.Index() < len(iter.GetIterSeq())
	}
	if iter.Next(context.TODO()) {
		// @ assert iter.Index() < len(iter.GetIterSeq())
	}
	r := iter.Next(context.TODO())
	// @ invariant iter.IterMem()
	// @ invariant r ==> iter.Index() < len(iter.GetIterSeq())
	for r {
		iter.Pair( /*@ perm(1/2) @*/ )
		r = iter.Next(context.TODO())
	}
}
