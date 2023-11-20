// +gobra
// ##(--onlyFilesWithHeader)
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
	Token           jwt.Token
}

// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(sig, _)
// @ requires t != nil
// @ ensures err == nil ==> res.Mem()
// @ ensures err != nil ==> res == nil
func MkADEMToken(km *keyManager, sig *jws.Signature, t jwt.Token) (res *ADEMToken, err error) {
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
	(forall i int :: { ts[i] } 0 <= i && i < len(ts) ==> ts[i] != nil && ts[i].Mem())
}
@*/
