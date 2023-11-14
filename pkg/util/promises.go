// +gobra
package util

import jwk "github.com/lestrrat-go/jwx/v2/jwk"

// An interface to implement promises that can be created and fullfilled later.
type Promise interface {
	// @ pred ProducerToken()
	// @ pred ConsumerToken()

	// Fullfil the promise. [Get] will unblock (when called already) or succeed
	// (when called later).
	// @ requires ProducerToken()
	Fulfill(jwk.Key)

	// Cancel a promise. Subsequent calls to [Get] will return T's null value.
	// @ requires ProducerToken()
	Reject()

	// Return the value of the promise. Will only return the result the promise
	// was fullfilled with exactly once. Afterwards, it will return the null
	// value. Call will block on unfullfilled promise.
	// @ requires ConsumerToken()
	Get() (res jwk.Key)
}

type promise struct {
	ch chan jwk.Key
}

// Create a new promise.
// @ ensures res != nil && isComparable(res) && res.ProducerToken() && res.ConsumerToken()
func NewPromise() (res Promise) {
	newProm /*@@@*/ := promise{ch: make(chan jwk.Key, 1)}
	// @ newProm.ch.Init(SendInv!<_!>, PredTrue!<!>)
	// @ newProm.ch.CreateDebt(1, 2, PredTrue!<!>)
	// @ fold newProm.ProducerToken()
	// @ fold newProm.ConsumerToken()
	return &newProm
}

// @ requires p.ProducerToken()
func (p *promise) Fulfill(val jwk.Key) {
	// @ unfold p.ProducerToken()
	// @ fold SendInv!<_!>(val)
	p.ch <- val
	// @ fold PredTrue!<!>()
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)

}

// @ requires p.ProducerToken()
func (p *promise) Reject() {
	// @ unfold p.ProducerToken()
	// @ fold PredTrue!<!>()
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)
}

// @ requires p.ConsumerToken()
// @ ensures res != nil ==> true
func (p *promise) Get() (res jwk.Key) {
	// @ unfold p.ConsumerToken()
	// @ fold PredTrue!<!>()
	e := <-p.ch
	// @ ghost { if e != nil { unfold SendInv!<_!>(e) } }
	return e
}

// @ ensures res != nil && isComparable(res) && res.ConsumerToken()
func Fullfilled(val jwk.Key) (res Promise) {
	p := NewPromise()
	p.Fulfill(val)
	return p
}

// @ ensures res != nil && isComparable(res) && res.ConsumerToken()
func Rejected() (res Promise) {
	p := NewPromise()
	p.Reject()
	return p
}

/*@

pred SendInv(val jwk.Key) {
	true
}

pred (p *promise) ProducerToken() {
	acc(p, 1/2) &&
		acc(p.ch.SendChannel(), 1/2) &&
		p.ch.ClosureDebt(PredTrue!<!>, 1, 2) &&
		p.ch.SendGivenPerm() == SendInv!<_!> &&
		p.ch.SendGotPerm() == PredTrue!<!>
}

pred (p *promise) ConsumerToken() {
	acc(p, 1/2) &&
		p.ch.RecvChannel() &&
		p.ch.Token(PredTrue!<!>) &&
		p.ch.RecvGivenPerm() == PredTrue!<!> &&
		p.ch.RecvGotPerm() == SendInv!<_!>
}

(*promise) implements Promise

@*/
