// +gobra
package x509

import (
	"github.com/google/certificate-transparency-go/x509/pkix"
)

// A Certificate represents an X.509 certificate.
type Certificate struct {
	DNSNames []string
	Subject  pkix.Name

	// (lmeinen) fields that are never accessed are omitted for simplicity
}

// ParseTBSCertificate parses a single TBSCertificate from the given ASN.1 DER data.
// The parsed data is returned in a Certificate struct for ease of access.
func ParseTBSCertificate(asn1Data []byte) (*Certificate, error)

// ParseCertificate parses a single certificate from the given ASN.1 DER data.
// This function can return both a Certificate and an error (in which case the
// error will be of type NonFatalErrors).
func ParseCertificate(asn1Data []byte) (*Certificate, error)
