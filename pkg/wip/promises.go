// -gobra

package wip

import jwk "github.com/lestrrat-go/jwx/v2/jwk"

/*@
type PromiseState adt {
	US{} // 0 Unfulfilled State
	FS{} // 1 Fulfilled State
	RS{} // 2 Rejected State
	GS{} // 3 Gotten State
}
@*/

type Promise interface {
	// @ pred mem()

	// @ requires mem() && GetState() == US{}
	// @ ensures mem() && GetState() == FS{}
	Fulfill(jwk.Key)

	// @ requires mem() && GetState() == US{}
	// @ ensures mem() && GetState() == RS{}
	Reject()

	// @ requires mem()
	// @ ensures mem() && GetState() == GS{}
	Get() (res jwk.Key)

	/*@
	  ghost
	  requires mem()
	  pure GetState() (PromiseState)
	  @*/
}

type promise struct {
	ch    chan jwk.Key
	state int // -gobra doesn't yet support ghost struct members
}

// Create a new promise.
// @ ensures res != nil && res.mem() && res.GetState() == US{}
func NewPromise() (res Promise) {
	newProm := promise{ch: make(chan jwk.Key, 1), state: 0} // @ addressable: newProm
	// @ newProm.ch.Init(SendInvariant!<_!>, PredTrue!<!>)
	// @ newProm.ch.CreateDebt(1, 2, PredTrue!<!>)
	// @ fold newProm.mem()
	return &newProm
}

// @ requires p.mem() && p.GetState() == US{}
// @ ensures p.mem() && p.GetState() == FS{}
func (p *promise) Fulfill(val jwk.Key) {
	// @ unfold p.mem()
	// @ fold SendInvariant!<_!>(val)
	p.ch <- val
	// @ fold PredTrue!<!>()
	close(p.ch) /*@ with: 1, 2, PredTrue!<!> @*/
	p.state = 1
	// @ fold p.mem()
}

// @ requires p.mem() && p.GetState() == US { }
// @ ensures p.mem() && p.GetState() == RS { }
func (p *promise) Reject() {
	// @ unfold p.mem()
	// @ fold PredTrue!<!>()
	close(p.ch) /*@ with: 1, 2, PredTrue!<!> @*/
	p.state = 2
	// @ fold p.mem()
}

// @ requires p.mem()
// @ ensures p.mem() && p.GetState() == GS { }
func (p *promise) Get() (res jwk.Key) {
	// @ unfold p.mem()
	// @ fold PredTrue!<!>()
	e := <-p.ch
	p.state = 3
	// @ fold p.mem()
	return e
}

// @ ensures res != nil && res.mem() && res.GetState() == FS { }
func Fullfilled(val jwk.Key) (res Promise) {
	p := NewPromise()
	p.Fulfill(val)
	return p
}

// @ ensures res != nil && res.mem() && res.GetState() == RS { }
func Rejected() (res Promise) {
	p := NewPromise()
	p.Reject()
	return p
}

/*@
ghost
requires p.mem()
pure func (p *promise) GetState() (PromiseState) {
  return unfolding p.mem() in match p.state {
    case 0: US{}
    case 1: FS{}
    case 2: RS{}
    case 3: GS{}
  }
}
@*/

/*@
pred (p *promise) mem() {
	acc(p) && 0 <= p.state && p.state <= 3 &&
	p.ch.RecvChannel() && p.ch.Token(PredTrue!<!>) &&
	p.ch.RecvGivenPerm() == PredTrue!<!> &&
	(p.state == 0 ==> acc(p.ch.SendChannel(), 1 / 2) &&
		p.ch.ClosureDebt(PredTrue!<!>, 1, 2) &&
		p.ch.SendGivenPerm() == SendInvariant!<_!>) && // not closed
	(p.state == 1 || p.state == 2 ==> p.ch.Closed()) && // closed
	// Note that we can't make any guarantees on the state of p.ch at the end of a Get call
	(p.state == 3 ==> true)
}
@*/

/*@
pred SendInvariant(val jwk.Key) {
  true
}
@*/

/*@
*promise implements Promise
@*/
