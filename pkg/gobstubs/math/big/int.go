// +gobra
// ##(--onlyFilesWithHeader)
package big

// An Int represents a signed multi-precision integer.
// The zero value for an Int represents the value 0.
//
// Operations always take pointer arguments (*Int) rather
// than Int values, and each unique Int value requires
// its own unique *Int pointer. To "copy" an Int value,
// an existing (or newly allocated) Int must be set to
// a new value using the Int.Set method; shallow copies
// of Ints are not supported and may lead to errors.
//
// Note that methods may leak the Int's value through timing side-channels.
// Because of this and because of the scope and complexity of the
// implementation, Int is not well-suited to implement cryptographic operations.
// The standard library avoids exposing non-trivial Int methods to
// attacker-controlled inputs and the determination of whether a bug in math/big
// is considered a security vulnerability might depend on the impact on the
// standard library.
type Int struct {
	neg bool // sign
	abs nat  // absolute value of the integer
}

// NewInt allocates and returns a new Int set to x.
// @ ensures acc(res)
func NewInt(x int64) (res *Int)

// SetBytes interprets buf as the bytes of a big-endian unsigned
// integer, sets z to that value, and returns z.
// @ preserves p > 0 && forall i int :: 0 <= i && i < len(buf) ==> acc(&buf[i], p)
// @ requires acc(z)
// @ ensures acc(res)
func (z *Int) SetBytes(buf []byte /*@, ghost p perm @*/) (res *Int)

// Int64 returns the int64 representation of x.
// If x cannot be represented in an int64, the result is undefined.
// @ requires acc(x, _)
func (x *Int) Int64() int64
