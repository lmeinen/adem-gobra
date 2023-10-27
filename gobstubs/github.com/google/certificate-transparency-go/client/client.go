// +gobra
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
func New(uri string, hc http.Client, opts jsonclient.Options) (*LogClient, error)

// BaseURI returns the base URI that the JSONClient makes queries to.
func (c *LogClient) BaseURI() string

// GetSTH retrieves the current STH from the log.
// Returns a populated SignedTreeHead, or a non-nil error (which may be of type
// RspError if a raw http.Response is available).
func (c *LogClient) GetSTH(ctx context.Context) (*ct.SignedTreeHead, error)

// VerifySTHSignature checks the signature in sth, returning any error encountered or nil if verification is
// successful.
func (c *LogClient) VerifySTHSignature(sth ct.SignedTreeHead) error

// GetProofByHash returns an audit path for the hash of an SCT.
func (c *LogClient) GetProofByHash(ctx context.Context, hash []byte, treeSize uint64) (*ct.GetProofByHashResponse, error)

// GetEntryAndProof returns a log entry and audit path for the index of a leaf.
func (c *LogClient) GetEntryAndProof(ctx context.Context, index, treeSize uint64) (*ct.GetEntryAndProofResponse, error)