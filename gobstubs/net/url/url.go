// +gobra
package url

// The Userinfo type is an immutable encapsulation of username and
// password details for a URL.
type Userinfo struct {
	username    string
	password    string
	passwordSet bool
}

// A URL represents a parsed URL (technically, a URI reference).
type URL struct {
	Scheme      string
	Opaque      string    // encoded opaque data
	User        *Userinfo // username and password information
	Host        string    // host or host:port
	Path        string    // path (relative paths may omit leading slash)
	RawPath     string    // encoded path hint (see EscapedPath method)
	OmitHost    bool      // do not emit empty host (authority)
	ForceQuery  bool      // append a query ('?') even if RawQuery is empty
	RawQuery    string    // encoded query values, without '?'
	Fragment    string    // fragment for references, without '#'
	RawFragment string    // encoded fragment hint (see EscapedFragment method)
}

// Parse parses a raw url into a URL structure.
// @ ensures acc(url)
func Parse(rawURL string) (url *URL, err error)

// Hostname returns u.Host, stripping any valid port number if present.
func (u *URL) Hostname() string
