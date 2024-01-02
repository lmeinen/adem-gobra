// +gobra
// ##(--onlyFilesWithHeader)
// @ initEnsures PkgMem() &&
// @ 	acc(&jwt.Custom, 1/2) &&
// @ 	acc(jwt.Custom, 1/2) &&
// @ 	CustomFields(jwt.Custom)
package tokens

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"net/url"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/ident"
	"github.com/adem-wg/adem-proto/pkg/util"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ importRequires acc(&jwt.Custom) && acc(jwt.Custom) && jwt.Custom.IsEmpty()
	"github.com/lestrrat-go/jwx/v2/jwt"
)

// Register JWT fields of emblems for easier parsing.
func init() {

	jwt.RegisterCustomField("log", []*LogConfig{} /*@, jwt.Custom.Copy(1/2) @*/)
	jwt.RegisterCustomField("key", EmbeddedKey{} /*@, jwt.Custom.Copy(1/2) @*/)
	jwt.RegisterCustomField("ass", []*ident.AI{} /*@, jwt.Custom.Copy(1/2) @*/)
	jwt.RegisterCustomField("emb", EmblemConstraints{} /*@, jwt.Custom.Copy(1/2) @*/)
	jwt.RegisterCustomField("ver", "" /*@, jwt.Custom.Copy(1/2) @*/)

	// TODO: (lmeinen) Gobra doesn't handle init order properly yet - really these assumptions should already hold
	// @ assume ErrAssetConstraint != nil &&
	// @ 	ErrPrpConstraint != nil &&
	// @ 	ErrDstConstraint != nil &&
	// @ 	ErrWndConstraint != nil &&
	// @ 	ErrIllegalConst != nil &&
	// @ 	ErrIllegalVersion != nil &&
	// @ 	ErrIllegalType != nil &&
	// @ 	ErrAssMissing != nil &&
	// @ 	ErrEndMissing != nil &&
	// @ 	ErrNoEndorsedKey != nil &&
	// @ 	ErrAlgMissing != nil
	// @ fold PkgMem()
}

var ErrIllegalConst error = errors.New("json element is illegal constant")

type PurposeMask byte

// FIXME: (lmeinen) Gobra throws a NumberFormatException for the below binary literals
// const Protective PurposeMask = 0b0000_0001
const Protective PurposeMask = 0x01

// const Indicative PurposeMask = 0b0000_0010
const Indicative PurposeMask = 0x02

// @ preserves acc(pm)
// @ preserves acc(PkgMem(), _)
// @ requires acc(bs)
func (pm *PurposeMask) UnmarshalJSON(bs []byte) error {
	var prps /*@@@*/ []string
	var mask PurposeMask
	if err := unmarshalStringSlice(bs, &prps); err != nil {
		return err
	} else {
		// @ invariant acc(prps)
		for _, prp := range prps {
			switch prp {
			case consts.Protective:
				mask |= Protective
			case consts.Indicative:
				mask |= Indicative
			default:
				return /*@ unfolding acc(PkgMem(), _) in @*/ ErrIllegalConst
			}
		}
	}
	*pm = mask
	return nil
}

// @ trusted
// @ preserves acc(bs)
// @ preserves acc(s) && acc(*s)
// @ ensures s != nil ==> *s === old(*s)
func unmarshalStringSlice(bs []byte, s *[]string) error {
	return json.Unmarshal(bs, s)
}

// @ preserves acc(pm)
// @ preserves acc(PkgMem(), _)
// @ ensures err == nil ==> acc(bs)
func (pm *PurposeMask) MarshalJSON() (bs []byte, err error) {
	var purposes []string
	if *pm&Protective != 0 {
		purposes = append( /*@perm(1/2), @*/ purposes, consts.Protective)
	}
	if *pm&Indicative != 0 {
		purposes = append( /*@perm(1/2), @*/ purposes, consts.Indicative)
	}
	return json.Marshal(purposes)
}

type ChannelMask byte

// FIXME: (lmeinen) Gobra throws a NumberFormatException for the below binary literals
// const DNS ChannelMask = 0b0000_0001
const DNS ChannelMask = 0x01

// const TLS ChannelMask = 0b0000_0010
const TLS ChannelMask = 0x02

// const UDP ChannelMask = 0b0000_0100
const UDP ChannelMask = 0x04

// @ preserves acc(cm)
// @ preserves acc(PkgMem(), _)
// @ requires acc(bs)
func (cm *ChannelMask) UnmarshalJSON(bs []byte) error {
	var dsts /*@@@*/ []string
	var mask ChannelMask
	if err := unmarshalStringSlice(bs, &dsts); err != nil {
		return err
	} else {
		// @ invariant acc(dsts)
		for _, dst := range dsts {
			switch dst {
			case consts.DNS:
				mask |= DNS
			case consts.TLS:
				mask |= TLS
			case consts.UDP:
				mask |= UDP
			default:
				return /*@ unfolding acc(PkgMem(), _) in @*/ ErrIllegalConst
			}
		}
	}
	*cm = mask
	return nil
}

// @ preserves acc(cm)
// @ preserves acc(PkgMem(), _)
// @ ensures err == nil ==> acc(bs)
func (cm *ChannelMask) MarshalJSON() (bs []byte, err error) {
	var dsts []string
	if *cm&DNS != 0 {
		dsts = append( /*@ perm(1/2), @*/ dsts, consts.DNS)
	}
	if *cm&TLS != 0 {
		dsts = append( /*@ perm(1/2), @*/ dsts, consts.TLS)
	}
	if *cm&UDP != 0 {
		dsts = append( /*@ perm(1/2), @*/ dsts, consts.UDP)
	}
	return json.Marshal(dsts)
}

type EmblemConstraints struct {
	Purpose      *PurposeMask `json:"prp,omitempty"`
	Distribution *ChannelMask `json:"dst,omitempty"`
	Assets       []*ident.AI  `json:"ass,omitempty"`
	Window       *int         `json:"wnd,omitempty"`
}

// Struct that represents an identifying log binding.
type LogConfig struct {
	Ver  string   `json:"ver"`
	Id   string   `json:"id"`
	Hash LeafHash `json:"hash"`
}

// Wrapper type for easier JSON unmarshalling of base64-encoded JSON strings of
// leaf hashes.
type LeafHash struct {
	B64 string
	Raw []byte
}

// Attempt to parse a JSON value as string that contains a base64-encoded leaf
// hash.
// @ preserves acc(h)
// @ preserves acc(PkgMem(), _)
// @ requires acc(bs)
func (h *LeafHash) UnmarshalJSON(bs []byte) (err error) {
	trimmed := bytes.Trim(bs, `"`)
	if raw, e := util.B64Dec(trimmed); e != nil {
		err = e
	} else {
		h.B64 = string(trimmed)
		h.Raw = raw
	}
	return
}

// @ preserves acc(h)
// @ preserves acc(PkgMem(), _)
// @ ensures err == nil ==> acc(bs)
func (h *LeafHash) MarshalJSON() (bs []byte, err error) {
	return json.Marshal(h.B64)
}

// Wrapper type to parse "key" field as [jwk.Key].
type EmbeddedKey struct {
	Key jwk.Key
}

// Attempt to parse a JSON value as string that contains a single JWK in JSON
// encoding.
// @ preserves acc(ek)
// @ preserves acc(PkgMem(), _)
// @ requires acc(bs)
func (ek *EmbeddedKey) UnmarshalJSON(bs []byte) (err error) {
	trimmed := bytes.Trim(bs, `"`)
	if k, e := jwk.ParseKey(trimmed); e != nil {
		err = e
	} else {
		ek.Key = k
	}
	return
}

var ErrIllegalVersion = jwt.NewValidationError(errors.New("illegal version"))
var ErrIllegalType = jwt.NewValidationError(errors.New("illegal claim type"))
var ErrAssMissing = jwt.NewValidationError(errors.New("emblems require ass claim"))
var ErrEndMissing = jwt.NewValidationError(errors.New("endorsements require end claim"))

// FIXME: (lmeinen) This function was originally inlined: Gobra doesn't appear to fully support function types
type EmblemValidatorS struct{}

// Validation function for emblem tokens.
// @ preserves acc(v.Mem(), _)
// @ requires t != nil
// @ ensures err == nil ==> v.Constraints(t)
func (v EmblemValidatorS) Validate(_ context.Context, t jwt.Token) (err jwt.ValidationError) {
	// @ unfold acc(v.Mem(), _)
	// @ ghost defer fold acc(v.Mem(), _)

	if err := validateCommon(t); err != nil {
		return err
	}

	if _, ok := t.Get("ass"); !ok {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrAssMissing
	}

	// @ fold v.Constraints(t)

	return nil
}

var EmblemValidator = EmblemValidatorS{}

// FIXME: (lmeinen) This function was originally inlined: Gobra doesn't appear to fully support function types
type EndorsementValidatorS struct{}

// Validation function for endorsement tokens.
// @ preserves acc(v.Mem(), _)
// @ requires t != nil
// @ ensures err == nil ==> v.Constraints(t)
func (v EndorsementValidatorS) Validate(_ context.Context, t jwt.Token) (err jwt.ValidationError) {
	// @ unfold acc(v.Mem(), _)
	// @ ghost defer fold acc(v.Mem(), _)

	if err := validateCommon(t); err != nil {
		return err
	}

	end, ok := t.Get("end")
	if ok {
		_, check := end.(bool)
		if !check {
			return /*@ unfolding acc(PkgMem(), _) in @*/ ErrIllegalType
		}
	} else {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrEndMissing
	}

	// @ fold v.Constraints(t)

	return nil
}

var EndorsementValidator = EndorsementValidatorS{}

// Validate that an OI has the form https://DOMAINNAME.
func validateOI(oi string) error {
	if oi == "" {
		return nil
	}

	url, err := url.Parse(oi)
	if err != nil {
		return errors.New("could not parse OI")
	}
	if url.Scheme != "https" || url.Host == "" || url.Opaque != "" || url.User != nil || url.RawPath != "" || url.RawQuery != "" || url.RawFragment != "" {
		return errors.New("illegal OI")
	}
	return nil
}

// Validate claims shared by emblems and endorsements.
// @ preserves acc(PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
// @ requires t != nil
// @ ensures err == nil ==> CommonConstraints(t)
func validateCommon(t jwt.Token) (err jwt.ValidationError) {
	if err := jwt.Validate(t); err != nil {
		return jwt.NewValidationError(err)
	}
	ver, ok := t.Get(`ver`)
	if !ok || ver.(string) != string(consts.V1) {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrIllegalVersion
	}

	if validateOI(t.Issuer()) != nil {
		return jwt.ErrInvalidIssuer()
	}

	// @ fold CommonConstraints(t)

	return nil
}

/*@

(EndorsementValidatorS) implements jwt.Validator
(EmblemValidatorS) implements jwt.Validator

pred (EndorsementValidatorS) Mem() {
	PkgMem() &&
	acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
}

pred (EmblemValidatorS) Mem() {
	PkgMem() &&
	acc(&jwt.Custom, _) && acc(jwt.Custom, _) && CustomFields(jwt.Custom)
}

pred CommonConstraints(t jwt.Token) {
	acc(&jwt.Custom, _) && acc(jwt.Custom, _) &&
	t != nil &&
	jwt.IsValid(t) &&
	t.Contains("ver") &&
	t.PureGet("ver") != string(consts.V1)
}

pred (EmblemValidatorS) Constraints(t jwt.Token) {
	t != nil &&
	t.Contains("ass") &&
	CommonConstraints(t)
}

pred (EndorsementValidatorS) Constraints(t jwt.Token) {
	t != nil &&
	acc(&jwt.Custom, _) && acc(jwt.Custom, _) &&
	t.Contains("end") &&
	typeOf(t.PureGet("end")) == type[bool] &&
	CommonConstraints(t)
}

pred LogMem(log []*LogConfig) {
	acc(log) &&
		forall i int :: 0 <= i && i < len(log) ==> acc(log[i]) && acc(log[i].Hash.Raw)
}

([]*LogConfig) implements jwt.JwtClaim {
	pred Mem := LogMem
}

pred KeyMem(key EmbeddedKey) {
	key.Key.Mem()
}

(EmbeddedKey) implements jwt.JwtClaim {
	pred Mem := KeyMem
}

pred AssMem(ass []*ident.AI) {
	acc(ass) &&
	forall i int :: 0 <= i && i < len(ass) ==> ass[i].Mem()
}

([]*ident.AI) implements jwt.JwtClaim {
	pred Mem := AssMem
}

pred EmbMem(emb EmblemConstraints) {
	acc(emb.Purpose) &&
	acc(emb.Distribution) &&
	acc(emb.Assets) &&
		forall i int :: 0 <= i && i < len(emb.Assets) ==> emb.Assets[i].Mem() &&
	acc(emb.Window)
}

(EmblemConstraints) implements jwt.JwtClaim {
	pred Mem := EmbMem
}

pred PkgMem() {
	ErrAssetConstraint != nil &&
	ErrPrpConstraint != nil &&
	ErrDstConstraint != nil &&
	ErrWndConstraint != nil &&
	ErrIllegalConst != nil &&
	ErrIllegalVersion != nil &&
	ErrIllegalType != nil &&
	ErrEndMissing != nil &&
	ErrAssMissing != nil &&
	ErrNoEndorsedKey != nil &&
	ErrAlgMissing != nil
}

ghost
requires acc(f, _)
pure func CustomFields(f jwt.Fields) bool {
	return (
		domain(f) == set[string] { "log", "key", "ass", "emb", "ver" } &&
		typeOf(f["log"]) == type[[]*LogConfig] &&
		typeOf(f["key"]) == type[EmbeddedKey] &&
		typeOf(f["ass"]) == type[[]*ident.AI] &&
		typeOf(f["emb"]) == type[EmblemConstraints] &&
		typeOf(f["ver"]) == type[string])
}

@*/
