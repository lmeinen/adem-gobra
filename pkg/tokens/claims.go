// +gobra

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
	"github.com/lestrrat-go/jwx/v2/jwt"
)

// Register JWT fields of emblems for easier parsing.
func init() {
	// TODO: (lmeinen) Implement parsing interface in jwt library
	// 	- type guarantees and mem permissions for Get method
	//	- type constraints for JSON parsing interface implementation
	jwt.RegisterCustomField("log", []*LogConfig{})
	jwt.RegisterCustomField("key", EmbeddedKey{})
	jwt.RegisterCustomField("ass", []*ident.AI{})
	jwt.RegisterCustomField("emb", EmblemConstraints{})
}

var ErrIllegalConst error = errors.New("json element is illegal constant")

type PurposeMask byte

type StringSlice []string

/*@
pred StringSliceMem(s []string) {
	acc(s)
}
@*/

// FIXME: (lmeinen) Gobra throws a NumberFormatException for the below binary literals
// const Protective PurposeMask = 0b0000_0001
const Protective PurposeMask = 0x01

// const Indicative PurposeMask = 0b0000_0010
const Indicative PurposeMask = 0x02

// @ preserves acc(pm)
// @ requires acc(bs)
func (pm *PurposeMask) UnmarshalJSON(bs []byte) error {
	var prps /*@@@*/ []string
	var mask PurposeMask
	// @ fold StringSliceMem!<prps!>()
	if err := json.Unmarshal(bs, &prps /*@, StringSliceMem!<prps!> @*/); err != nil {
		return err
	} else {
		// @ unfold StringSliceMem!<prps!>()
		// @ invariant acc(prps)
		for _, prp := range prps {
			switch prp {
			case consts.Protective:
				mask |= Protective
			case consts.Indicative:
				mask |= Indicative
			default:
				return ErrIllegalConst
			}
		}
	}
	*pm = mask
	return nil
}

// @ preserves acc(pm)
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
// @ requires acc(bs)
func (cm *ChannelMask) UnmarshalJSON(bs []byte) error {
	var dsts /*@@@*/ []string
	var mask ChannelMask
	// @ fold StringSliceMem!<dsts!>()
	if err := json.Unmarshal(bs, &dsts /*@, StringSliceMem!<dsts!> @*/); err != nil {
		return err
	} else {
		// @ unfold StringSliceMem!<dsts!>()
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
				return ErrIllegalConst
			}
		}
	}
	*cm = mask
	return nil
}

// @ preserves acc(cm)
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

// FIXME: (lmeinen) This function was originally inlined: Gobra doesn't appear to fully support function types
type EmblemValidatorS struct{}

// Validation function for emblem tokens.
// @ requires t != nil
func (EmblemValidatorS) Validate(_ context.Context, t jwt.Token) jwt.ValidationError {
	if err := validateCommon(t); err != nil {
		return err
	}

	if _, ok := t.Get("ass"); !ok {
		return ErrAssMissing
	}

	return nil
}

var EmblemValidator = EmblemValidatorS{}

// FIXME: (lmeinen) This function was originally inlined: Gobra doesn't appear to fully support function types
type EndorsementValidatorS struct{}

// Validation function for endorsement tokens.
// @ requires t != nil
func (EndorsementValidatorS) Validate(_ context.Context, t jwt.Token) jwt.ValidationError {
	if err := validateCommon(t); err != nil {
		return err
	}

	end, ok := t.Get("end")
	// @ assume ok ==> typeOf(end) == type[bool]
	if ok {
		_, check := end.(bool)
		if !check {
			return ErrIllegalType
		}
	}

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
// @ requires t != nil
func validateCommon(t jwt.Token) jwt.ValidationError {
	if err := jwt.Validate(t); err != nil {
		return jwt.NewValidationError(err)
	}
	ver, ok := t.Get(`ver`)
	// @ assume ok ==> typeOf(ver) == type[string]
	if !ok || ver.(string) != string(consts.V1) {
		return ErrIllegalVersion
	}

	if validateOI(t.Issuer()) != nil {
		return jwt.ErrInvalidIssuer()
	}

	return nil
}

/*@

(EndorsementValidatorS) implements jwt.Validator
(EmblemValidatorS) implements jwt.Validator

@*/
