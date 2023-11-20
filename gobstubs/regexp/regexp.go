// +gobra
// ##(--onlyFilesWithHeader)
package regexp

// Regexp is the representation of a compiled regular expression.
type Regexp struct {
	expr string // as passed to Compile

	// (lmeinen) kept opaque to keep library stub as shallow as possible
}

// MustCompile is like Compile but panics if the expression cannot be parsed.
// @ ensures acc(res)
// @ ensures res.expr == str
// @ decreases
func MustCompile(str string) (res *Regexp)

// FindStringSubmatch returns a slice of strings holding the text of the
// leftmost match of the regular expression in s and the matches, if any, of
// its subexpressions, as defined by the 'Submatch' description in the
// package comment.
// @ preserves acc(re)
// @ ensures acc(res)
// @ ensures forall i int :: 0 <= i && i < len(res) ==> len(res[i]) <= len(s)
func (re *Regexp) FindStringSubmatch(s string) (res []string)
