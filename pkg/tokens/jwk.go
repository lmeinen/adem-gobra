// +gobra
// ##(--onlyFilesWithHeader)
package tokens

import (
	"context"
	"crypto/sha256"
	"encoding/base32"
	"encoding/json"
	"errors"
	"strings"

	"github.com/cyberphone/json-canonicalization/go/src/webpki.org/jsoncanonicalizer"
	"github.com/lestrrat-go/jwx/v2/jwa"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

var ErrNoEndorsedKey = errors.New("no endorsed key present")
var ErrAlgMissing = errors.New("input key misses algorithm")

// Get the KID of a key endorsed in an emblem. If the endorsed key has no KID,
// it will be calculated.
// @ trusted
// @ preserves acc(PkgMem(), _) && acc(t.Mem(), _) && acc(jwt.FieldMem(t.Values()), 1/4)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
// @ requires t != nil
// @ ensures err == nil ==> kid != "" && t.Contains("key") && kid == t.PureKeyID()
func GetEndorsedKID(t jwt.Token) (kid string, err error) {
	jwKey, ok := t.Get("key")
	if !ok {
		return "",
			/*@ unfolding acc(PkgMem(), _) in @*/ ErrNoEndorsedKey
	} else {
		// @ unfold acc(jwt.FieldMem(t.Values()), 1/4)
		// @ unfold acc(KeyMem(jwKey.(EmbeddedKey)), 1/4)
		if kid, err := GetKID(jwKey.(EmbeddedKey).Key /*@, some(perm(1/4)) @*/); err != nil {
			// @ fold acc(KeyMem(jwKey.(EmbeddedKey)), 1/4)
			// @ fold acc(jwt.FieldMem(t.Values()), 1/4)
			return "", err
		} else {
			// @ fold acc(KeyMem(jwKey.(EmbeddedKey)), 1/4)
			// @ fold acc(jwt.FieldMem(t.Values()), 1/4)
			return kid, nil
		}
	}
}

// Get a key's KID. If it has no KID, it will be calculated.
// @ preserves acc(PkgMem(), _)
// @ preserves p == none[perm] ? acc(key.Mem(), _) : (get(p) > 0 && acc(key.Mem(), get(p)))
// @ requires key != nil
// @ ensures err == nil ==> kid != ""
func GetKID(key jwk.Key /*@, ghost p option[perm] @*/) (kid string, err error) {
	if key.KeyID( /*@ p @*/ ) != "" {
		return key.KeyID( /*@ p @*/ ), nil
	}

	return CalcKID(key /*@, p @*/)
}

// Calculate a key's KID by hashing it using a canonical JSON representation and
// SHA256. This function will drop any private-key parameters.
// @ preserves acc(PkgMem(), _)
// @ preserves p == none[perm] ? acc(key.Mem(), _) : (get(p) > 0 && acc(key.Mem(), get(p)))
// @ requires key != nil
// @ ensures err == nil ==> kid != ""
func CalcKID(key jwk.Key /*@, ghost p option[perm] @*/) (kid string, err error) {
	if pk, err := key.PublicKey( /*@ p @*/ ); err != nil {
		return "", err
	} else if key.Algorithm( /*@ p @*/ ) == nil || key.Algorithm( /*@ p @*/ ).String() == "" {
		return "",
			/*@ unfolding acc(PkgMem(), _) in @*/ ErrAlgMissing
	} else if err := pk.Set("alg", key.Algorithm( /*@ p @*/ )); err != nil {
		return "", err
	} else if err := pk.Remove("kid"); err != nil {
		return "", err
	} else if jsonKey, err := json.Marshal(pk); err != nil {
		return "", err
	} else if canonical, err := jsoncanonicalizer.Transform(jsonKey); err != nil {
		return "", err
	} else {
		h /*@@@*/ := sha256.Sum256(canonical)
		b32 := base32.StdEncoding.EncodeToString(h[:])
		// TODO: (lmeinen) Can we drop this assumption?
		// @ assume forall s string :: (len(s) == 0 ==> s == "") && (s == "" ==> len(s) == 0)
		return strings.ToLower(strings.TrimRight(b32, "=")), nil
	}
}

// Set a key's KID if not already present.
// @ preserves acc(PkgMem(), _)
// @ preserves key != nil && key.Mem()
func SetKID(key jwk.Key, force bool) error {
	var kid string
	var err error
	if force {
		kid, err = CalcKID(key /*@, some(perm(1/2)) @*/)
	} else {
		kid, err = GetKID(key /*@, some(perm(1/2)) @*/)
	}

	if err != nil {
		return err
	} else {
		return key.Set("kid", kid)
	}
}

// Calculate and set the KID of every key in the given set. Will override old
// KIDs.
// @ preserves acc(PkgMem(), _)
// @ requires jwkSet != nil && jwkSet.Mem() && jwk.KeySeq(jwkSet.Elems())
// @ requires acc(alg, _)
// @ ensures e == nil ==> r != nil && r.Mem() && jwk.KeySeq(r.Elems())
func SetKIDs(jwkSet jwk.Set, alg *jwa.SignatureAlgorithm) (r jwk.Set, e error) {
	withKIDs := jwk.NewSet()
	ctx := context.TODO()
	iter := jwkSet.Keys(ctx /*@, perm(1/2) @*/)
	// @ unfold jwk.KeySeq(jwkSet.Elems())

	iterNext := iter.Next(ctx)

	// @ invariant acc(PkgMem(), _)
	// @ invariant acc(jwkSet.Mem(), 1/2)
	// @ invariant withKIDs != nil && withKIDs.Mem() &&
	// @ 	forall i int :: { withKIDs.Elems()[i] } 0 <= i && i < len(withKIDs.Elems()) ==> withKIDs.Elems()[i].Mem()
	// @ invariant iter.IterMem() &&
	// @ 	(iterNext ==> iter.Index() < len(iter.GetIterSeq())) &&
	// @ 	jwkSet.Elems() == iter.GetIterSeq() &&
	// @ 	(forall i int :: { iter.GetIterSeq()[i] } 0 <= i && i < len(iter.GetIterSeq()) ==> iter.GetIterSeq()[i].(jwk.Key).Mem())
	// @ decreases len(iter.GetIterSeq()) - iter.Index()
	for iterNext {
		v := iter.Pair( /*@ perm(1/2) @*/ ).Value
		if pk, err := v.(jwk.Key).PublicKey( /*@ some(perm(1/2)) @*/ ); err != nil {
			return nil, err
		} else {
			if pk.Algorithm( /*@ some(perm(1/2)) @*/ ).String() == "" {
				if err := pk.Set("alg", alg); err != nil {
					return nil, err
				}
			}
			if err := SetKID(pk, true); err != nil {
				return nil, err
			}
			// @ assert pk.Mem()
			withKIDs.AddKey(pk)
		}
		iterNext = iter.Next(ctx)
	}
	// @ fold jwk.KeySeq(withKIDs.Elems())

	return withKIDs, nil
}
