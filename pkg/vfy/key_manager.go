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

// Creates a new key manager to verify [numThreads]-many tokens asynchronously.
// @ trusted
// @ requires numThreads > 0
// @ ensures res.lock.LockP() &&
// @ 	res.lock.LockInv() == LockInv!<res!>
// @ ensures res.init.WaitGroupP() &&
// @ 	res.init.WaitMode() &&
// @ 	acc(res.init.UnitDebt(WaitInv!<!>), numThreads/1) &&
// @ 	res.init.Token(WaitInv!<!>)
func NewKeyManager(numThreads int) (res *keyManager) {
	var km /*@@@*/ keyManager
	// @ km.init.Init()
	km.init.Add(numThreads /*@, 1/2, PredTrue!<!> @*/)
	/*@
	invariant acc(km.init.WaitGroupP(), 1/2) && !km.init.WaitMode()
	invariant acc(km.init.UnitDebt(PredTrue!<!>), numThreads - i)
	invariant acc(km.init.UnitDebt(WaitInv!<!>), i/1) && acc(km.init.Token(WaitInv!<!>), i/1)
	for i := 0; i < numThreads; i++ {
		km.init.GenerateTokenAndDebt(WaitInv!<!>)
	}
	km.init.Start(1/2, WaitInv!<!>)
	km.init.SetWaitMode(1/2, 1/2)
	@*/

	km.keys = make(map[string]jwk.Key)
	km.listeners = make(map[string][]util.Promise)
	return &km
}

// Wait until all verification threads obtained a promise for their verification
// key.
// @ trusted
// @ requires acc(km.init.WaitGroupP(), 1/2)
// @ requires km.init.WaitMode()
// @ preserves acc(km.init.WaitGroupP(), 1/2)
func (km *keyManager) waitForInit() {
	// TODO: (lmeinen) come up with sensible functional properties
	km.init.Wait( /*@ 1/2, seq[pred()]{ } @*/ )
}

// Cancel any further verification.
// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) killListeners() {
	km.lock.Lock()
	defer km.lock.Unlock()

	for k, listeners := range km.listeners {
		for _, promise := range listeners {
			promise.Reject()
		}
		doDelete(km.listeners, k)
	}
}

// How many blocked threads are there that wait for a key promise to be resolved?
// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) waiting() (res int) {
	km.lock.Lock()
	defer km.lock.Unlock()

	sum := 0
	for _, listeners := range km.listeners {
		sum += len(listeners)
	}
	return sum
}

// Store a verified key and notify listeners waiting for that key.
// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) put(k jwk.Key) bool {
	km.lock.Lock()
	defer km.lock.Unlock()

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
	promises := km.listeners[kid]
	if len(promises) == 0 {
		return false
	}

	for _, promise := range promises {
		if promise != nil {
			promise.Fulfill(k)
		}
	}
	doDelete(km.listeners, kid)
	return true
}

// Get a key based on its [kid]. Returns a promise that may already be resolved.
// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) getKey(kid string) util.Promise {
	km.lock.Lock()
	defer km.lock.Unlock()

	c := util.NewPromise()
	k, ok := km.keys[kid]
	if ok {
		c.Fulfill(k)
	} else {
		listenersForKid := km.listeners[kid]
		km.listeners[kid] = append( /*@ perm(1/2), @*/ listenersForKid, c)
	}
	return c
}

// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(sig, _)
func (km *keyManager) getVerificationKey(sig *jws.Signature) util.Promise {
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
// @ trusted
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
func (km *keyManager) FetchKeys(ctx context.Context, sink jws.KeySink, sig *jws.Signature, m *jws.Message) error {
	var promise util.Promise
	var err error
	if t, e := jwt.Parse(m.Payload(), jwt.WithVerify(false)); e != nil {
		log.Printf("could not decode payload: %s", e)
		err = e
	} else if logs, ok := t.Get("log" /*@, 1/2 @*/); ok {
		headerKey := sig.ProtectedHeaders().JWK()
		for _, r := range roots.VerifyBindingCerts(t.Issuer(), headerKey, logs.([]*tokens.LogConfig)) {
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
	// @ fold PredTrue!<!>()
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
// @ preserves acc(listeners)
func doDelete(listeners map[string][]util.Promise, k string) {
	// FIXME: (lmeinen) delete expression not supported in Gobra
	delete(listeners, k)
}

/*@
pred WaitInv() {
	true
}
@*/

/*@
pred LockInv(km *keyManager) {
	acc(&km.keys) && acc(&km.listeners)
}
@*/
