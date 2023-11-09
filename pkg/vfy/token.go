// +gobra
package vfy

import (
	"errors"

	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

type ADEMToken struct {
	VerificationKey jwk.Key
	Headers         jws.Headers
	Token           jwt.JwtToken
}

// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(sig, _)
// @ requires t != nil
// @ ensures err == nil ==> res.Mem()
// @ ensures err != nil ==> res == nil
func MkADEMToken(km *keyManager, sig *jws.Signature, t jwt.JwtToken) (res *ADEMToken, err error) {
	verifKey := km.getVerificationKey(sig).Get()
	if verifKey == nil {
		return nil, errors.New("no verification key")
	}
	token := &ADEMToken{verifKey, sig.ProtectedHeaders(), t}
	// @ fold token.Mem()
	return token, nil
}

/*@
pred (t *ADEMToken) Mem() {
	acc(t) &&
			t.VerificationKey != nil &&
			t.Headers != nil &&
			t.Token != nil
}

pred TokenList(ts []*ADEMToken) {
	acc(ts) &&
	(forall k int :: { ts[k] } 0 <= k && k < len(ts) ==> ts[k] != nil && ts[k].Mem()) &&
	(forall i, j int :: { ts[i], ts[j] } 0 <= i && i < j && j < len(ts) ==> ts[i] != ts[j])
}
@*/
