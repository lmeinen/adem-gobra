// +gobra
// ##(--onlyFilesWithHeader)
package context

import (
	"time"
)

// A Context carries a deadline, a cancellation signal, and other values across
// API boundaries.
type Context interface {
	// Deadline returns the time when work done on behalf of this context
	// should be canceled. Deadline returns ok==false when no deadline is
	// set. Successive calls to Deadline return the same results.
	Deadline() (deadline time.Time, ok bool)

	// Done returns a channel that's closed when work done on behalf of this
	// context should be canceled.
	Done() <-chan struct{}

	// If Done is not yet closed, Err returns nil.
	Err() error

	// Value returns the value associated with this context for key, or nil
	// if no value is associated with key.
	Value(key any) any
}

// An emptyCtx is never canceled, has no values, and has no deadline.
// It is the common base of backgroundCtx and todoCtx.
type emptyCtx struct{}

func (emptyCtx) Deadline() (deadline time.Time, ok bool) {
	return
}

func (emptyCtx) Done() <-chan struct{} {
	return nil
}

func (emptyCtx) Err() error {
	return nil
}

func (emptyCtx) Value(key any) any {
	return nil
}

type todoCtx struct{ emptyCtx }

// TODO returns a non-nil, empty [Context].
func TODO() (res Context)

// Background returns a non-nil, empty [Context].
func Background() Context

// A CancelFunc tells an operation to abandon its work.
// A CancelFunc does not wait for the work to stop.
// A CancelFunc may be called by multiple goroutines simultaneously.
// After the first call, subsequent calls to a CancelFunc do nothing.
// FIXME: (lmeinen) adapted from 'type CancelFunc func()' - which Gobra can't seem to deal with
func CancelFunc()

// WithTimeout returns WithDeadline(parent, time.Now().Add(timeout)).
// @ ensures cancel implements CancelFunc
func WithTimeout(parent Context, timeout time.Duration) (c Context, cancel func())
