// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"errors"

	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jws"
	"github.com/lestrrat-go/jwx/v2/jwt"
	// @ "github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "lib"
	// @ "term"
)

type ADEMToken struct {
	VerificationKey jwk.Key
	Headers         jws.Headers
	Token           jwt.Token
}

// @ preserves acc(km.lock.LockP(), _) && km.lock.LockInv() == LockInv!<km!>
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ requires acc(sig, _)
// @ requires t != nil && t.Mem() && jwt.FieldMem(t.Values())
// @ requires t.Abs() == lib.gamma(tokenT)
// @ ensures err == nil ==> res != nil && ValidToken(res) && Abs(res) == lib.gamma(tokenT)
// @ ensures err != nil ==> res == nil
func MkADEMToken(km *keyManager, sig *jws.Signature, t jwt.Token /*@, ghost tokenT term.Term @*/) (res *ADEMToken, err error) {
	verifKey := km.getVerificationKey(sig).Get()
	if verifKey == nil {
		return nil, errors.New("no verification key")
	}
	token := &ADEMToken{verifKey, sig.ProtectedHeaders(), t}
	// @ fold ValidToken(token)
	// @ inhale Abs(token) == lib.gamma(tokenT)
	return token, nil
}
