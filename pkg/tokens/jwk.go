// +gobra
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
// @ preserves acc(PkgMem(), _)
// @ requires t != nil
// @ ensures err == nil ==> kid != ""
func GetEndorsedKID(t jwt.Token) (kid string, err error) {
	jwKey, ok := t.Get("key")
	// @ assume typeOf(jwKey) == type[EmbeddedKey] && jwKey.(EmbeddedKey).Key != nil
	if !ok {
		return "",
			/*@ unfolding acc(PkgMem(), _) in @*/ ErrNoEndorsedKey
	} else if kid, err := GetKID(jwKey.(EmbeddedKey).Key); err != nil {
		return "", err
	} else {
		return kid, nil
	}
}

// Get a key's KID. If it has no KID, it will be calculated.
// @ preserves acc(PkgMem(), _)
// @ requires key != nil
// @ ensures err == nil ==> kid != ""
func GetKID(key jwk.Key) (kid string, err error) {
	if key.KeyID() != "" {
		return key.KeyID(), nil
	}

	return CalcKID(key)
}

// Calculate a key's KID by hashing it using a canonical JSON representation and
// SHA256. This function will drop any private-key parameters.
// @ preserves acc(PkgMem(), _)
// @ requires key != nil
// @ ensures err == nil ==> kid != ""
func CalcKID(key jwk.Key) (kid string, err error) {
	if pk, err := key.PublicKey(); err != nil {
		return "", err
	} else if key.Algorithm() == nil || key.Algorithm().String() == "" {
		return "",
			/*@ unfolding acc(PkgMem(), _) in @*/ ErrAlgMissing
	} else if err := pk.Set("alg", key.Algorithm()); err != nil {
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
		// @ assume forall s string :: (len(s) == 0 ==> s == "") && (s == "" ==> len(s) == 0)
		return strings.ToLower(strings.TrimRight(b32, "=")), nil
	}
}

// Set a key's KID if not already present.
// @ preserves acc(PkgMem(), _)
// @ requires key != nil
func SetKID(key jwk.Key, force bool) error {
	var kid string
	var err error
	if force {
		kid, err = CalcKID(key)
	} else {
		kid, err = GetKID(key)
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
// @ requires jwkSet != nil
// @ requires acc(alg, _)
func SetKIDs(jwkSet jwk.Set, alg *jwa.SignatureAlgorithm) (jwk.Set, error) {
	withKIDs := jwk.NewSet()
	ctx := context.TODO()
	iter := jwkSet.Keys(ctx)
	// @ invariant acc(PkgMem(), _)
	for iter.Next(ctx) {
		v := iter.Pair().Value
		// @ assume typeOf(v) == type[jwk.Key]
		k := v.(jwk.Key)
		if pk, err := k.PublicKey(); err != nil {
			return nil, err
		} else {
			if pk.Algorithm().String() == "" {
				if err := pk.Set("alg", alg); err != nil {
					return nil, err
				}
			}
			if err := SetKID(pk, true); err != nil {
				return nil, err
			}
			withKIDs.AddKey(pk)
		}
	}
	return withKIDs, nil
}
