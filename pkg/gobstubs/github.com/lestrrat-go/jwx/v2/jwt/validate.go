// +gobra

package jwt

import (
	"context"
)

type ValidationError interface {
	// (lmeinen) Gobra doesn't appear to support embedding: needed to replace embedded error interface with builtin error interface
	// @ pred ErrorMem()

	// @ ghost
	// @ requires acc(ErrorMem(), _)
	// @ decreases
	// @ pure
	IsDuplicableMem() bool

	// @ ghost
	// @ preserves ErrorMem()
	// @ ensures   IsDuplicableMem() ==> ErrorMem()
	// @ decreases
	Duplicate()

	// @ preserves ErrorMem()
	// @ decreases
	Error() string

	isValidationError()
	Unwrap() error
}

func NewValidationError(err error) ValidationError

// ValidatorFunc is a type of Validator that does not have any
// state, that is implemented as a function
type ValidatorFunc func(context.Context, JwtToken) ValidationError
