// +gobra
package http

import (
	"io"
)

// Response represents the response from an HTTP request.
type Response struct {
	// Body represents the response body.
	Body io.ReadCloser
}

type Client int

// (lmeinen) use type alias int to capture intuition that DefaultClient is a const value
const DefaultClient = 0

// Get issues a GET to the specified URL. If the response is one of
// the following redirect codes, Get follows the redirect, up to a
// maximum of 10 redirects:
// @ ensures acc(resp) && resp.Body != nil
func Get(url string) (resp *Response, err error)
