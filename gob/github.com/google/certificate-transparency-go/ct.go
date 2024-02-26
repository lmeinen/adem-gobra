// +gobra
// ##(--onlyFilesWithHeader)
package ct

import (
	"crypto/sha256"
	"github.com/google/certificate-transparency-go/tls"
)

// LogEntryType constants from section 3.1.
const (
	X509LogEntryType    LogEntryType = 0
	PrecertLogEntryType LogEntryType = 1
)

// LogEntryType represents the LogEntryType enum from section 3.1:
//
//	enum { x509_entry(0), precert_entry(1), (65535) } LogEntryType;
type LogEntryType tls.Enum // tls:"maxval:65535"

// Version represents the Version enum from section 3.2:
//
//	enum { v1(0), (255) } Version;
type Version tls.Enum // tls:"maxval:255"

// SHA256Hash represents the output from the SHA256 hash function.
type SHA256Hash [sha256.Size]byte

// DigitallySigned is a local alias for tls.DigitallySigned so that we can
// attach a MarshalJSON method.
type DigitallySigned tls.DigitallySigned

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

/*@
pred (certT *CertificateTimestamp) Mem() {
	acc(certT) &&
	acc(certT.X509Entry) &&
		acc(certT.X509Entry.Data) &&
	acc(certT.PrecertEntry) &&
		acc(certT.PrecertEntry.TBSCertificate)
}

(*CertificateTimestamp) implements tls.Parseable
@*/

// SignedTreeHead represents the structure returned by the get-sth CT method
// after base64 decoding; see sections 3.5 and 4.3.
type SignedTreeHead struct {
	Version           Version         `json:"sth_version"`         // The version of the protocol to which the STH conforms
	TreeSize          uint64          `json:"tree_size"`           // The number of entries in the new tree
	Timestamp         uint64          `json:"timestamp"`           // The time at which the STH was created
	SHA256RootHash    SHA256Hash      `json:"sha256_root_hash"`    // The root hash of the log's Merkle tree
	TreeHeadSignature DigitallySigned `json:"tree_head_signature"` // Log's signature over a TLS-encoded TreeHeadSignature
	LogID             SHA256Hash      `json:"log_id"`              // The SHA256 hash of the log's public key
}

// GetProofByHashResponse represents the JSON response to the get-proof-by-hash GET
// method from section 4.5.  (The corresponding GET request has parameters 'hash'
// and 'tree_size'.)
type GetProofByHashResponse struct {
	LeafIndex int64    `json:"leaf_index"` // The 0-based index of the end entity corresponding to the "hash" parameter.
	AuditPath [][]byte `json:"audit_path"` // An array of base64-encoded Merkle Tree nodes proving the inclusion of the chosen certificate.
}

// GetEntryAndProofResponse represents the JSON response to the get-entry-and-proof
// GET method from section 4.8. (The corresponding GET request has parameters 'leaf_index'
// and 'tree_size'.)
type GetEntryAndProofResponse struct {
	LeafInput []byte   `json:"leaf_input"` // the entry itself
	ExtraData []byte   `json:"extra_data"` // any chain provided when the entry was added to the log
	AuditPath [][]byte `json:"audit_path"` // the corresponding proof
}
