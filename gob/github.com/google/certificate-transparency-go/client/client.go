// +gobra
// ##(--onlyFilesWithHeader)
package client

import (
	"context"
	"net/http"

	ct "github.com/google/certificate-transparency-go"
	"github.com/google/certificate-transparency-go/jsonclient"
)

// LogClient represents a client for a given CT Log instance
type LogClient struct {
	// (lmeinen) struct embedding currently not supported by Gobra
	jsonClient *jsonclient.JSONClient
}

// New constructs a new LogClient instance.
// @ ensures err == nil ==> acc(lc) && acc(lc.jsonClient)
func New(uri string, hc http.Client, opts jsonclient.Options) (lc *LogClient, err error)

// BaseURI returns the base URI that the JSONClient makes queries to.
// @ preserves acc(c) && acc(c.jsonClient)
func (c *LogClient) BaseURI() string

// GetSTH retrieves the current STH from the log.
// Returns a populated SignedTreeHead, or a non-nil error (which may be of type
// RspError if a raw http.Response is available).
// @ preserves acc(c) && acc(c.jsonClient)
// @ ensures err == nil ==> acc(sth)
func (c *LogClient) GetSTH(ctx context.Context) (sth *ct.SignedTreeHead, err error)

// VerifySTHSignature checks the signature in sth, returning any error encountered or nil if verification is
// successful.
// @ preserves acc(c) && acc(c.jsonClient)
func (c *LogClient) VerifySTHSignature(sth ct.SignedTreeHead) error

// GetProofByHash returns an audit path for the hash of an SCT.
// @ preserves acc(c) && acc(c.jsonClient)
// @ preserves acc(hash)
// @ ensures err == nil ==> (
// @ 	acc(p) &&
// @ 	acc(p.AuditPath) &&
// @ 	forall i int :: { p.AuditPath[i] } 0 <= i && i < len(p.AuditPath) ==> acc(p.AuditPath[i]))
func (c *LogClient) GetProofByHash(ctx context.Context, hash []byte, treeSize uint64) (p *ct.GetProofByHashResponse, err error)

// GetEntryAndProof returns a log entry and audit path for the index of a leaf.
// @ preserves acc(c) && acc(c.jsonClient)
// @ ensures err == nil ==> (
// @ 	acc(r) &&
// @ 	acc(r.LeafInput) &&
// @ 	acc(r.ExtraData) &&
// @ 	acc(r.AuditPath) &&
// @ 	forall i int :: { r.AuditPath[i] } 0 <= i && i < len(r.AuditPath) ==> acc(r.AuditPath[i]))
func (c *LogClient) GetEntryAndProof(ctx context.Context, index, treeSize uint64) (r *ct.GetEntryAndProofResponse, err error)
