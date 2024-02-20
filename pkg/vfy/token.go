// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"errors"

	// @ "github.com/adem-wg/adem-proto/pkg/consts"
	// @ "github.com/adem-wg/adem-proto/pkg/ident"
	// @ "github.com/adem-wg/adem-proto/pkg/tokens"
	// @ . "github.com/adem-wg/adem-proto/pkg/goblib"

	// @ "github.com/lestrrat-go/jwx/v2/jwa"
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

ghost
trusted
requires acc(rawToken, _)
decreases _
pure func AbsBytes(rawToken []byte) (res Bytes)

ghost
requires acc(ValidToken(t), _)
requires unfolding acc(ValidToken(t), _) in t.Token.Contains("ass")
requires acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
pure func Abs(t *ADEMToken) Bytes {
	// (1) note the PureGet call, it is a consequence of Gobra's limitation that a pure function cannot have multiple return values - as a consequence AbsAI can't require any permissions, either
	return unfolding acc(ValidToken(t), _) in
		let ai := t.Token.PureGet("ass") in
		t.Headers.ContentType() == string(consts.EmblemCty) ?
			// emblem
			(t.Headers.Algorithm() == jwa.NoSignature ?
				// unsigned
				tuple2B(stringB("emblem"), ident.AbsAI(ai.([]*ident.AI))) :
				// signed
				stringB("invalid")) :
			// endorsement
			stringB("endorsement")
}

@*/

// TODO: Reformulate this as a predicate which can be used to obtain term format constraints needed to unfold iospec
/*
func termConstraints(t *ADEMToken, endorsedBy map[string]*ADEMToken) {
	if t.Headers.ContentType() == string(consts.EmblemCty) {
		// is emblem
		E, ok := t.Token.Get("ass")
		//  assert ok
		if t.Headers.Algorithm() == jwa.NoSignature {
			// is unsigned emblem
			//  assert Abs(t) == <'emblem', E>
		} else if oi := t.Token.Issuer(); oi == "" {
			// is anon emblem
			//  assert Abs(t) == <t.VerificationKey.KeyID(), <'emblem', E>, term.sign(t.Token, term.pk(???))>
		} else {
			// is organizational emblem
			//  assert Abs(t) == <t.VerificationKey.KeyID(), oi, <'emblem', E, oi>, term.sign(t.Token, term.pk(???))>
		}
	} else {
		// is endorsement
		endKey, ok := t.Token.Get("end")
		//  assert ok
		if oi := t.Token.Issuer(); oi == "" {
			// is anon endorsement
			// assert Abs(t) == <t.VerificationKey.KeyID(), <'end', endKey>,  term.sign(t.Token, term.pk(???))>
		} else if end := endorsedBy[t.VerificationKey.KeyID()]; end == nil || end.Token.Issuer() != oi {
			// is root endorsement
			//  assert Abs(t) == <t.VerificationKey.KeyID(), oi, <'root_end', t.Token.Subject(), endKey>,  term.sign(t.Token, term.pk(???))>
		} else {
			// is internal endorsement
			//  assert oi == t.Token.Subject()
			//  assert Abs(t) == <t.VerificationKey.KeyID(), oi, <'end', oi, endKey>,  term.sign(t.Token, term.pk(???))>

		}

	}
}
*/
