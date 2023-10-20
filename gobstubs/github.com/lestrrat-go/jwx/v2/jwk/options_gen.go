// +gobra
package jwk

// ParseOption is a type of Option that can be passed to `jwk.Parse()`
// ParseOption also implmentsthe `ReadFileOption` and `CacheOption`,
// and thus safely be passed to `jwk.ReadFile` and `(*jwk.Cache).Configure()`
type ParseOption interface {
	// --- (lmeinen) replaces embedded option.Interface interface ---

	// Ident returns the "indentity" of this option, a unique identifier that
	// can be used to differentiate between options
	Ident() interface{}

	// Value returns the corresponding value.
	Value() interface{}
	// ---------------------------------------------------------------

	fetchOption()
	registerOption()
	readFileOption()
}
