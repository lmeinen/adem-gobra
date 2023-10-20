// +gobra

// Package ct holds core types and utilities for Certificate Transparency.
package ct

import (
	"crypto/sha256"
	"github.com/google/certificate-transparency-go/tls"
)

// LogEntryType represents the LogEntryType enum from section 3.1:
//
//	enum { x509_entry(0), precert_entry(1), (65535) } LogEntryType;
type LogEntryType tls.Enum // tls:"maxval:65535"

// LogEntryType constants from section 3.1.
const (
	X509LogEntryType    LogEntryType = 0
	PrecertLogEntryType LogEntryType = 1
)

// ASN1Cert type for holding the raw DER bytes of an ASN.1 Certificate
// (section 3.1).
type ASN1Cert struct {
	Data []byte `tls:"minlen:1,maxlen:16777215"`
}

// PreCert represents a Precertificate (section 3.2).
type PreCert struct {
	IssuerKeyHash  [sha256.Size]byte
	TBSCertificate []byte `tls:"minlen:1,maxlen:16777215"` // DER-encoded TBSCertificate
}

// CertificateTimestamp is the collection of data that the signature in an
// SCT is over; see section 3.2.
type CertificateTimestamp struct {
	EntryType    LogEntryType `tls:"maxval:65535"`
	X509Entry    *ASN1Cert    `tls:"selector:EntryType,val:0"`
	PrecertEntry *PreCert     `tls:"selector:EntryType,val:1"`
}
