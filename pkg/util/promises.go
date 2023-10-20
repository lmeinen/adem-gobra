// +gobra

package util

import jwk "github.com/lestrrat-go/jwx/v2/jwk"

type Promise interface {
	Fulfill(jwk.Key)

	Reject()

	Get() (res jwk.Key)
}

type promise struct {
	ch    chan jwk.Key
	state int // Gobra doesn't yet support ghost struct members
}

// Create a new promise.

func NewPromise() (res Promise) {
	newProm /*@@@*/ := promise{ch: make(chan jwk.Key, 1), state: 0}
	// @ newProm.ch.Init(SendInvariant!<_!>, PredTrue!<!>)
	// @ newProm.ch.CreateDebt(1, 2, PredTrue!<!>)
	return &newProm
}

func (p *promise) Fulfill(val jwk.Key) {
	// @ fold SendInvariant!<_!>(val)
	p.ch <- val
	// @ fold PredTrue!<!>()
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)
	p.state = 1

}

func (p *promise) Reject() {
	// @ fold PredTrue!<!>()
	close(p.ch /*@, 1, 2, PredTrue!<!> @*/)
	p.state = 2
}

func (p *promise) Get() (res jwk.Key) {
	// @ fold PredTrue!<!>()
	e := <-p.ch
	p.state = 3
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

/*@
pred SendInvariant(val jwk.Key) {
  true
}
@*/
