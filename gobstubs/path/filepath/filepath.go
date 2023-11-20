// +gobra
// ##(--onlyFilesWithHeader)
package filepath

// Glob returns the names of all files matching pattern or nil
// if there is no matching file.
// @ ensures acc(matches)
func Glob(pattern string) (matches []string, err error)
