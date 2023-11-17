// +gobra
package vfy

import (
	"context"
	"errors"
	"log"
	"sync"

	"github.com/adem-wg/adem-proto/pkg/roots"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/adem-wg/adem-proto/pkg/util"
	// @ "github.com/adem-wg/adem-proto/pkg/goblib"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

var ErrNoKeyFound = errors.New("no key found")
var ErrRootKeyUnbound = errors.New("root key not properly committed")
var ErrAlgsDiffer = errors.New("jws alg and verification key alg are different")

// A struct that implements the [jwt.KeyProvider] interface.
type keyManager struct {
	// Lock for map access
	lock sync.Mutex
	// Wait group that will be done once all verification threads obtained a
	// promise for their verification key.
	init sync.WaitGroup
	// Maps KIDs to keys. Only contains verified keys.
	keys map[string]jwk.Key
	// Promises waiting for keys.
	listeners map[string][]util.Promise
}

// TODO: (lmeinen) Add auxiliary datastructure to allow proving properties about promise graph (!)
// TODO: (lmeinen) Basic memory verification
// TODO: (lmeinen) Investigate necessity of adding a proper wg token - can maybe be used to make claims of type "method m2 is only called after m1"
// TODO: (lmeinen) Find way to make claims about waiting number of threads - would allow proving termination of main thread

// Creates a new key manager to verify [numThreads]-many tokens asynchronously.
// @ requires numThreads > 0
// @ ensures res.lock.LockP() &&
// @ 	res.lock.LockInv() == LockInv!<res!>
// @ ensures res.init.WaitGroupP() &&
// @ 	res.init.WaitMode() &&
// @ 	acc(res.init.UnitDebt(WaitInv!<!>), perm(numThreads)) &&
// @ 	res.init.Token(WaitInv!<!>)
func NewKeyManager(numThreads int) (res *keyManager) {
	var km /*@@@*/ keyManager

	// @ km.init.Init()
	km.init.Add(numThreads /*@, 1/2, PredTrue!<!> @*/)
	/*@
	ghost {
		invariant 0 <= i && i <= numThreads
		invariant acc(km.init.WaitGroupP(), 1/2) && !km.init.WaitMode()
		invariant acc(km.init.UnitDebt(PredTrue!<!>), numThreads - i)
		invariant acc(km.init.UnitDebt(WaitInv!<!>), perm(i)) && acc(km.init.Token(WaitInv!<!>), perm(i))
		for i := 0; i < numThreads; i++ {
			km.init.GenerateTokenAndDebt(WaitInv!<!>)
		}
		km.init.Start(1/2, WaitInv!<!>)
		km.init.SetWaitMode(1/2, 1/2)
	}
	@*/

	km.keys = make(map[string]jwk.Key)
	km.listeners = make(map[string][]util.Promise)

	/*@
	ghost var pLock = &km.lock
	fold LockInv!<&km!>()
	pLock.SetInv(LockInv!<&km!>)
	@*/

	return &km
}

// Wait until all verification threads obtained a promise for their verification
// key.
// @ requires km.init.WaitGroupP()
// @ requires km.init.WaitMode()
// @ ensures km.init.WaitGroupP()
func (km *keyManager) waitForInit() {
	km.init.Wait( /*@ 1/2, seq[pred()]{ } @*/ )
}

// Cancel any further verification.
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) killListeners() {
	km.lock.Lock()
	defer km.lock.Unlock()
	// @ unfold LockInv!<km!>()
	// @ ghost defer fold LockInv!<km!>()

	l := km.listeners

	// @ invariant acc(l)
	// @ invariant forall key string :: key in domain(l) && !(key in visited) ==> (
	// @ 	acc(l[key]) &&
	// @ 	let llist, _ := l[key] in forall i int :: 0 <= i && i < len(llist) ==> PromiseInv(llist[i], key, i))
	for k, listeners := range l /*@ with visited @*/ {
		// @ invariant acc(listeners, 1/2)
		// @ invariant forall i int :: 0 <= i && i0 <= i && i < len(listeners) ==> PromiseInv(listeners[i], k, i)
		for _, promise := range listeners /*@ with i0 @*/ {
			// @ unfold PromiseInv(promise, k, i0)
			promise.Reject()
		}

		// FIXME: (lmeinen) Don't have access to km.listeners here --> delete all after completion of loop
		// doDelete(km.listeners, k)
	}

	km.listeners = make(map[string][]util.Promise)
}

// How many blocked threads are there that wait for a key promise to be resolved?
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ ensures 0 <= res
func (km *keyManager) waiting() (res int) {
	km.lock.Lock()
	defer km.lock.Unlock()
	// @ unfold LockInv!<km!>()
	// @ ghost defer fold LockInv!<km!>()

	sum := 0
	// FIXME: (lmeinen) for whatever reason, there seems to be no configuration of loop invariants that allows ranging over km.listeners
	l := km.listeners
	// @ invariant acc(l)
	// @ invariant forall key string :: key in domain(l) ==> (
	// @ 	acc(l[key]) &&
	// @ 	let llist, _ := l[key] in forall i int :: 0 <= i && i < len(llist) ==> PromiseInv(llist[i], key, i))
	// @ invariant 0 <= sum
	for _, listeners := range l /*@ with visited @*/ {
		sum += len(listeners)
	}

	return sum
}

// Store a verified key and notify listeners waiting for that key.
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ requires k != nil
func (km *keyManager) put(k jwk.Key) bool {
	km.lock.Lock()
	defer km.lock.Unlock()
	// @ unfold LockInv!<km!>()
	// @ ghost defer fold LockInv!<km!>()

	kid, err := tokens.GetKID(k)
	if err != nil {
		return false
	} else if fp, err := tokens.CalcKID(k); err != nil {
		// We set and calculate the KID ID to be consistent with key hashing later
		// down the line.
		return false
	} else if err := k.Set("kid", fp); err != nil {
		return false
	}

	_, ok := km.keys[kid]
	if ok {
		return false
	}

	km.keys[kid] = k
	// FIXME: (lmeinen) added ok flag here; add as bug commit
	promises, ok := km.listeners[kid]
	if !ok {
		return false
	}

	// @ invariant acc(promises, 1/2)
	// @ invariant forall i int :: 0 <= i && i0 <= i && i < len(promises) ==> PromiseInv(promises[i], kid, i)
	for _, promise := range promises /*@ with i0 @*/ {
		// @ unfold PromiseInv(promise, kid, i0)
		if promise != nil {
			promise.Fulfill(k)
		}
	}

	doDelete(km.listeners, kid)

	return true
}

// // Get a key based on its [kid]. Returns a promise that may already be resolved.
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ ensures p != nil && p.ConsumerToken()
func (km *keyManager) getKey(kid string) (p util.Promise) {
	km.lock.Lock()
	defer km.lock.Unlock()
	// @ unfold LockInv!<km!>()
	// @ ghost defer fold LockInv!<km!>()

	c := util.NewPromise()
	k, ok := km.keys[kid]
	if ok {
		c.Fulfill(k)
	} else {
		listenersForKid := km.listeners[kid]
		// @ fold PromiseInv(c, kid, len(listenersForKid))
		km.listeners[kid] = append( /*@ perm(1/2), @*/ listenersForKid, c)
	}
	return c
}

// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(sig, _)
// @ ensures p != nil && p.ConsumerToken()
func (km *keyManager) getVerificationKey(sig *jws.Signature) (p util.Promise) {
	if headerKID := sig.ProtectedHeaders().KeyID(); headerKID != "" {
		return km.getKey(headerKID)
	} else if sig.ProtectedHeaders().JWK().KeyID() != "" {
		return km.getKey(sig.ProtectedHeaders().JWK().KeyID())
	} else {
		return util.Rejected()
	}
}

// Implements the [jwt.KeyManager] interface. If the token includes a root key,
// the root key commitment will be verified, and when this succeeds, the root
// key will be used for verification. All other keys will register a listener
// and wait for their verification key to be verified externally.
// @ requires km.Mem() && ctx != nil && sink != nil && acc(sig, _) && acc(m, _)
func (km *keyManager) FetchKeys(ctx context.Context, sink jws.KeySink, sig *jws.Signature, m *jws.Message) error {
	// @ unfold km.Mem()
	var promise util.Promise
	var err error
	if t, e := jwt.Parse(m.Payload(), jwt.WithVerify(false)); e != nil {
		log.Printf("could not decode payload: %s", e)
		err = e
	} else if logs, ok := t.Get("log"); ok {
		headerKey := sig.ProtectedHeaders().JWK()
		// @ assume typeOf(logs) == type[[]*tokens.LogConfig]
		logsCast := logs.([]*tokens.LogConfig)
		// @ inhale acc(logsCast) &&
		// @ 	forall i int :: 0 <= i && i < len(logsCast) ==> acc(logsCast[i]) && acc(logsCast[i].Hash.Raw)
		results := roots.VerifyBindingCerts(t.Issuer(), headerKey, logsCast)
		// @ invariant acc(results) && forall i int :: 0 <= i && i < len(results) ==> acc(results[i])
		for _, r := range results {
			if !r.Ok {
				log.Printf("could not verify root key commitment for log ID %s", r.LogID)
				err = ErrRootKeyUnbound
				break
			}
		}
		if err == nil {
			km.put(headerKey)
		}
	}

	promise = km.getVerificationKey(sig)
	// @ fold WaitInv!<!>()
	// @ km.init.PayDebt(WaitInv!<!>)
	km.init.Done()
	if err != nil {
		log.Printf("err: %s", err)
		return err
	}

	verificationKey := promise.Get()
	if verificationKey == nil {
		return ErrNoKeyFound
	}

	if verificationKey.Algorithm() != sig.ProtectedHeaders().Algorithm() {
		return ErrAlgsDiffer
	}

	sink.Key(jwa.SignatureAlgorithm(verificationKey.Algorithm().String()), verificationKey)
	return nil
}

// @ trusted
// @ requires acc(listeners)
// @ requires forall k string :: k in listeners && k != key ==> (
// @ 	acc(listeners[k]) &&
// @ 	let llist, _ := listeners[k] in forall i int :: { llist[i] } 0 <= i && i < len(llist) ==> PromiseInv(llist[i], k, i))
// @ ensures acc(listeners)
// @ ensures len(old(listeners)) - 1 <= len(listeners) && len(listeners) <= len(old(listeners))
// @ ensures forall k string :: k in listeners ==> (
// @ 	k != key &&
// @ 	k in old(listeners) &&
// @ 	acc(listeners[k]) &&
// @ 	let llist, _ := listeners[k] in forall i int :: 0 <= i && i < len(llist) ==> PromiseInv(llist[i], k, i))
func doDelete(listeners map[string][]util.Promise, key string) {
	// FIXME: (lmeinen) delete expression not supported in Gobra
	delete(listeners, key)
}

/*@
pred WaitInv() {
	true
}

pred PromiseInv(p util.Promise, ghost k string, ghost i int) {
	p != nil && p.ProducerToken()
}

pred LockInv(km *keyManager) {
	acc(&km.keys) &&
	acc(km.keys) &&
	acc(&km.listeners) &&
	acc(km.listeners) &&
	(forall k string :: k in domain(km.listeners) ==> (
		acc(km.listeners[k]) &&
		let llist, _ := km.listeners[k] in forall i int :: 0 <= i && i < len(llist) ==> PromiseInv(llist[i], k, i)))
}

// required to capture preconditions in jwt.KeyProvider interface
pred (km *keyManager) Mem() {
	km.init.UnitDebt(WaitInv!<!>) &&
	acc(km.lock.LockP(), _) &&
	km.lock.LockInv() == LockInv!<km!> &&
	acc(roots.RootsMem(), _)
}

ghost
trusted
requires acc(s)
ensures forall i int :: 0 <= i && i < len(s) ==> s[i] in r
ensures forall k string :: k in r ==> exists i int :: 0 <= i && i < len(s) && s[i] == k
pure func toSet(s []string) (r set[string]) {
	return (len(s) == 0 ? set[string]{} :
                        toSet(s[:len(s)-1]) union set[string]{s[len(s) - 1]})
}

(*keyManager) implements jws.KeyProvider
@*/
