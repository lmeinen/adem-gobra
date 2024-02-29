// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"context"
	"errors"
	"log"
	"sync"

	"github.com/adem-wg/adem-proto/pkg/roots"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/adem-wg/adem-proto/pkg/util"

	// @ "lib"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
	//@ "fact"
	//@ "place"
	//@ "iospec"
	//@ "term"
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
	// @ invariant forall key string :: key in domain(l) && !(key in visited) ==> ListInv(l[key], key)
	for k, listeners := range l /*@ with visited @*/ {
		noop(k)
		// @ unfold ListInv(listeners, k)
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
	// @ invariant forall key string :: key in domain(l) ==> ListInv(l[key], key)
	// @ invariant 0 <= sum
	for k, listeners := range l /*@ with visited @*/ {
		sum += /*@ unfolding ListInv(listeners, k) in @*/ len(listeners)
	}

	return sum
}

// Store a verified key and notify listeners waiting for that key.
// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(tokens.PkgMem(), _)
// @ requires k != nil && k.Mem()
// @ ensures k === old(k) && acc(k.Mem(), _)
func (km *keyManager) put(k jwk.Key) bool {
	km.lock.Lock()
	defer km.lock.Unlock()
	// @ unfold LockInv!<km!>()
	// @ ghost defer fold LockInv!<km!>()

	kid, err := tokens.GetKID(k /*@, some(perm(1/2)) @*/)
	if err != nil {
		return false
	} else if fp, err := tokens.CalcKID(k /*@, some(perm(1/2)) @*/); err != nil {
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
	// @ ghost defer fold KeyMem(k, kid)
	// FIXME: (lmeinen) added ok flag here; add as bug commit
	promises, ok := km.listeners[kid]
	if !ok {
		return false
	}

	// @ unfold ListInv(promises, kid)

	// @ invariant acc(k.Mem(), _)
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
		// @ unfold KeyMem(k, kid)
		c.Fulfill(k)
		// @ fold KeyMem(k, kid)
	} else {
		listenersForKid := km.listeners[kid]
		// @ ghost { if kid in domain(km.listeners) { unfold ListInv(listenersForKid, kid) } }
		// @ fold PromiseInv(c, kid, len(listenersForKid))
		km.listeners[kid] = append( /*@ perm(1/2), @*/ listenersForKid, c)
		// @ fold ListInv(km.listeners[kid], kid)
	}
	return c
}

// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(sig, _)
// @ ensures p != nil && p.ConsumerToken()
func (km *keyManager) getVerificationKey(sig *jws.Signature) (p util.Promise) {
	if headerKID := sig.ProtectedHeaders().KeyID(); headerKID != "" {
		return km.getKey(headerKID)
	} else if sig.ProtectedHeaders().JWK().KeyID( /*@ some(perm(1/2)) @*/ ) != "" {
		return km.getKey(sig.ProtectedHeaders().JWK().KeyID( /*@ some(perm(1/2)) @*/ ))
	} else {
		return util.Rejected()
	}
}

// Implements the [jwt.KeyManager] interface. If the token includes a root key,
// the root key commitment will be verified, and when this succeeds, the root
// key will be used for verification. All other keys will register a listener
// and wait for their verification key to be verified externally.
// @ requires km.Mem() && ctx != nil && sink != nil && acc(sig, _) && acc(m, _)
// @ requires lib.TokenVerifierInitState(p, rid, s, tokenT)
// @ requires m.AbsMsg() == lib.gamma(tokenT)
func (km *keyManager) FetchKeys(ctx context.Context, sink jws.KeySink, sig *jws.Signature, m *jws.Message /*@, ghost p place.Place, ghost rid term.Term, ghost s mset[fact.Fact], ghost tokenT term.Term @*/) (e error /*@, ghost p1 place.Place, ghost s1 mset[fact.Fact] @*/) {
	// @ unfold km.Mem()

	// TODO: (lmeinen) Return IOspec from function
	// TODO: (lmeinen) Add IOSpec operations for CT log requests
	// TODO: (lmeinen) How do we express that multiple parts together are abstracted to be tokenT? Do we maybe already add information here that tokenT consists of multiple parts? <key, token, sig>
	// TODO: (lmeinen) Maybe wrap all of this in a predicate so it's easier to recognize that this makes sense

	var promise util.Promise
	var err error
	if t /*@, p1, s1 @*/, e := jwt.Parse(m.Payload() /*@, p, rid, s, tokenT @*/, jwt.WithVerify(false)); e != nil {
		log.Printf("could not decode payload: %s", e)
		err = e
		// @ assert err != nil
	} else if logs, ok := t.Get("log"); ok {
		headerKey := sig.ProtectedHeaders().JWK()
		// @ unfold jwt.FieldMem(t.Values())
		// @ unfold tokens.LogMem(logs.([]*tokens.LogConfig))
		casted := logs.([]*tokens.LogConfig)
		err = verifyLog(t, headerKey, casted /*@, p, rid @*/)
		if err == nil && len(casted) > 0 {
			km.put(headerKey)
		}
	}
	promise = km.getVerificationKey(sig)
	// @ fold WaitInv!<!>()
	// @ km.init.PayDebt(WaitInv!<!>)
	km.init.Done()
	if err != nil {
		log.Printf("err: %s", err)
		return err /*@, p, s @*/
	}

	verificationKey := promise.Get()
	if verificationKey == nil {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrNoKeyFound /*@, p, s @*/
	}

	if verificationKey.Algorithm( /*@ none[perm] @*/ ) != sig.ProtectedHeaders().Algorithm() {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrAlgsDiffer /*@, p, s @*/
	}

	sink.Key(jwa.SignatureAlgorithm(verificationKey.Algorithm( /*@ none[perm] @*/ ).String()), verificationKey)
	return nil /*@, p, s @*/
}

// @ trusted
// @ preserves acc(PkgMem(), _) && acc(roots.PkgMem(), _) && acc(tokens.PkgMem(), _)
// @ preserves acc(t.Mem(), _) && t != nil
// @ preserves headerKey != nil && headerKey.Mem()
// @ requires acc(casted) &&
// @ 	forall i int :: 0 <= i && i < len(casted) ==> acc(casted[i]) && acc(casted[i].Hash.Raw)
func verifyLog(t jwt.Token, headerKey jwk.Key, casted []*tokens.LogConfig /*@, ghost p place.Place, ghost rid term.Term @*/) (e error) {
	var err error
	results := roots.VerifyBindingCerts(t.Issuer(), headerKey, casted)
	// @ invariant acc(PkgMem(), _)
	// @ invariant acc(t.Mem(), _)
	// @ invariant acc(results) && forall i int :: 0 <= i && i < len(results) ==> acc(results[i]) && (results[i].Ok ==> t.Issuer() != "")
	// @ invariant (err == nil) == (forall i int :: 0 <= i && i < i0 && i < len(results) ==> results[i].Ok)
	for _, r := range results /*@ with i0 @*/ {
		if !r.Ok {
			log.Printf("could not verify root key commitment for log ID %s", r.LogID)
			err = /*@ unfolding acc(PkgMem(), _) in @*/ ErrRootKeyUnbound
			break
		}
	}
	return err
}

// @ trusted
// @ requires acc(listeners)
// @ requires forall k string :: k in listeners && k != key ==> ListInv(listeners[k], k)
// @ ensures acc(listeners)
// @ ensures len(old(listeners)) - 1 <= len(listeners) && len(listeners) <= len(old(listeners))
// @ ensures forall k string :: k in listeners ==> (
// @ 	k != key &&
// @ 	k in old(listeners) &&
// @ 	ListInv(listeners[k], k))
func doDelete(listeners map[string][]util.Promise, key string) {
	// FIXME: (lmeinen) delete expression not supported in Gobra
	delete(listeners, key)
}

// @ trusted
func noop(_ string) {
	// avoids UnusedVar compiler errors
}

/*@
pred WaitInv() {
	true
}

pred PromiseInv(p util.Promise, ghost k string, ghost i int) {
	p != nil && p.ProducerToken()
}

pred KeyMem(k jwk.Key, kid string) {
	k != nil && acc(k.Mem(), _)
}

pred ListInv(l []util.Promise, k string) {
	acc(l) &&
	forall i int :: 0 <= i && i < len(l) ==> PromiseInv(l[i], k, i)
}

pred LockInv(km *keyManager) {
	acc(&km.keys) &&
	acc(km.keys) &&
	(forall k string :: k in km.keys ==> let jwkKey, _ := km.keys[k] in KeyMem(jwkKey, k)) &&
	acc(&km.listeners) &&
	acc(km.listeners) &&
	(forall k string :: k in domain(km.listeners) ==> ListInv(km.listeners[k], k))
}

// required to capture preconditions in jwt.KeyProvider interface
pred (km *keyManager) Mem() {
	km.init.UnitDebt(WaitInv!<!>) &&
	acc(km.lock.LockP(), _) &&
	km.lock.LockInv() == LockInv!<km!> &&
	acc(PkgMem(), _) &&
	acc(roots.PkgMem(), _) &&
	acc(tokens.PkgMem(), _) &&
	acc(&jwt.Custom, _) &&
 		acc(jwt.Custom, _) &&
 		tokens.CustomFields(jwt.Custom)
}

(*keyManager) implements jws.KeyProvider
@*/
