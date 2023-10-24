// +gobra

package errors

// New returns an error that formats as the given text.
// Each call to New returns a distinct error value even if the text is identical.
// @ ensures err.ErrorMem()
func New(text string) (err error)
