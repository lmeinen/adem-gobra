package tokens

import (
	"crypto/sha256"
	"encoding/base32"
	"encoding/json"
	"errors"
	"strings"

	"github.com/cyberphone/json-canonicalization/go/src/webpki.org/jsoncanonicalizer"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/lestrrat-go/jwx/v2/jwt"
)

var ErrNoEndorsedKey = errors.New("no endorsed key present")
var ErrAlgMissing = errors.New("input key misses algorithm")

// Get the KID of a key endorsed in an emblem. If the endorsed key has no KID,
// it will be calculated.
func GetEndorsedKID(t jwt.Token) (string, error) {
	if jwKey, ok := t.Get("key"); !ok {
		return "", ErrNoEndorsedKey
	} else if kid, err := GetKID(jwKey.(EmbeddedKey).Key); err != nil {
		return "", err
	} else {
		return kid, nil
	}
}

// Get a key's KID. If it has no KID, it will be calculated.
func GetKID(key jwk.Key) (string, error) {
	if key.KeyID() != "" {
		return key.KeyID(), nil
	}

	return CalcKID(key)
}

// Calculate a key's KID by hashing it using a canonical JSON representation and
// SHA256. This function will drop any private-key parameters.
func CalcKID(key jwk.Key) (string, error) {
	if pk, err := key.PublicKey(); err != nil {
		return "", err
	} else if key.Algorithm() == nil || key.Algorithm().String() == "" {
		return "", ErrAlgMissing
	} else if err := pk.Set("alg", key.Algorithm()); err != nil {
		return "", err
	} else if err := pk.Remove("kid"); err != nil {
		return "", err
	} else if jsonKey, err := json.Marshal(pk); err != nil {
		return "", err
	} else if canonical, err := jsoncanonicalizer.Transform(jsonKey); err != nil {
		return "", err
	} else {
		h := sha256.Sum256(canonical)
		b32 := base32.StdEncoding.EncodeToString(h[:])
		return strings.ToLower(strings.TrimRight(b32, "=")), nil
	}
}

// Set a key's KID if not already present.
func SetKID(key jwk.Key) error {
	if kid, err := GetKID(key); err != nil {
		return err
	} else {
		return key.Set("kid", kid)
	}
}
