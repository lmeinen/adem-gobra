// +gobra
package util

import jwk "github.com/lestrrat-go/jwx/v2/jwk"

// An interface to implement promises that can be created and fullfilled later.
type Promise interface {
	// @ pred Mem()

	// Fullfil the promise. [Get] will unblock (when called already) or succeed
	// (when called later).
	Fulfill(jwk.Key)
	// Cancel a promise. Subsequent calls to [Get] will return T's null value.
	Reject()
	// Return the value of the promise. Will only return the result the promise
	// was fullfilled with exactly once. Afterwards, it will return the null
	// value. Call will block on unfullfilled promise.
	Get() (res jwk.Key)
}

type promise struct {
	ch chan jwk.Key
}

// Create a new promise.
// @ trusted
// @ ensures res != nil && isComparable(res)
func NewPromise() (res Promise) {
	newProm /*@@@*/ := promise{ch: make(chan jwk.Key, 1)}
	return &newProm
}

// @ trusted
func (p *promise) Fulfill(val jwk.Key) {
	p.ch <- val
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)

}

// @ trusted
func (p *promise) Reject() {
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)
}

// @ trusted
func (p *promise) Get() (res jwk.Key) {
	e := <-p.ch
	return e
}

// @ ensures res != nil && isComparable(res)
func Fullfilled(val jwk.Key) (res Promise) {
	p := NewPromise()
	p.Fulfill(val)
	return p
}

// @ ensures res != nil && isComparable(res)
func Rejected() (res Promise) {
	p := NewPromise()
	p.Reject()
	return p
}

/*@
pred (p *promise) Mem() {
	acc(p)
}

ghost
requires p1.Mem()
requires p2.Mem()
ensures unfolding p1.Mem() in unfolding p2.Mem() in p1 != p2
pure func Neq(p1 *promise, p2 *promise) bool {
	return true
}

(*promise) implements Promise
@*/
