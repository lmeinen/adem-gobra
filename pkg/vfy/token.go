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
// @ ensures err == nil ==> res != nil && ValidToken(res)
// @ ensures err != nil ==> res == nil
func MkADEMToken(km *keyManager, sig *jws.Signature, t jwt.Token) (res *ADEMToken, err error) {
	verifKey := km.getVerificationKey(sig).Get()
	if verifKey == nil {
		return nil, errors.New("no verification key")
	}
	token := &ADEMToken{verifKey, sig.ProtectedHeaders(), t}
	// @ fold ValidToken(token)
	return token, nil
}

/*@
pred ValidToken(t *ADEMToken) {
	acc(t) &&
	t.VerificationKey != nil &&
		acc(t.VerificationKey.Mem(), _) &&
	t.Headers != nil &&
	t.Token != nil
}

pred Endorsement(t *ADEMToken) {
	acc(ValidToken(t), 1/2) &&
	acc(t, 1/2) &&
	t.Token != nil &&
		jwt.IsValid(t.Token) &&
		acc(&jwt.Custom, _) && acc(jwt.Custom, _) &&
		t.Token.Contains("end") &&
		typeOf(t.Token.PureGet("end")) == type[bool]
}

pred Emblem(t *ADEMToken) {
	acc(ValidToken(t), 1/2) &&
	acc(t, 1/2) &&
	t.Token != nil &&
		jwt.IsValid(t.Token) &&
		acc(&jwt.Custom, _) && acc(jwt.Custom, _) &&
		t.Token.Contains("ass")
}

// predicate wrapper to ensure injectivity of t
pred TokenListElem(_ int, t *ADEMToken) {
	t != nil && ValidToken(t)
}

pred EndListElem(_ int, t *ADEMToken) {
	t != nil && Endorsement(t)
}

pred TokenList(ts []*ADEMToken) {
	acc(ts) &&
	forall i int :: { ts[i] } 0 <= i && i < len(ts) ==> TokenListElem(i, ts[i])
}

pred EndorsementList(ts []*ADEMToken) {
	acc(ts) &&
	forall i int :: { ts[i] } 0 <= i && i < len(ts) ==> EndListElem(i, ts[i])
}

@*/
