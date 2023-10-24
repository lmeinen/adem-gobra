// +gobra
package util

import jwk "github.com/lestrrat-go/jwx/v2/jwk"

// An interface to implement promises that can be created and fullfilled later.
type Promise interface {
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
func NewPromise() (res Promise) {
	newProm /*@@@*/ := promise{ch: make(chan jwk.Key, 1)}
	return &newProm
}

func (p *promise) Fulfill(val jwk.Key) {
	p.ch <- val
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)

}

func (p *promise) Reject() {
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)
}

func (p *promise) Get() (res jwk.Key) {
	e := <-p.ch
	return e
}

func Fullfilled(val jwk.Key) (res Promise) {
	p := NewPromise()
	p.Fulfill(val)
	return p
}

func Rejected() (res Promise) {
	p := NewPromise()
	p.Reject()
	return p
}
