// +gobra
// ##(--onlyFilesWithHeader)
package roots

/*
This file implements the checking of root key commitments for the Certificate
Transparency API in v1.
*/

import (
	"context"
	"errors"
	"fmt"
	"log"
	"net/url"
	"time"

	"github.com/adem-wg/adem-proto/pkg/tokens"
	"github.com/adem-wg/adem-proto/pkg/util"
	ct "github.com/google/certificate-transparency-go"
	"github.com/google/certificate-transparency-go/client"
	"github.com/google/certificate-transparency-go/tls"
	"github.com/google/certificate-transparency-go/x509"
	"github.com/lestrrat-go/jwx/v2/jwk"
	"github.com/transparency-dev/merkle/proof"
	"github.com/transparency-dev/merkle/rfc6962"
	// @ "fact"
	// @ "fresh"
	// @ "iospec"
	// @ "place"
	// @ "term"
)

var ErrIssNoHostName = errors.New("issuer has no hostname")
var ErrCertNotForIss = errors.New("certificate is not valid for issuer OI")
var ErrCertNotForKey = errors.New("certificate is not valid for key")
var ErrWrongEntryType = errors.New("do not recognize entry type")

// Verify that the rootKey is correctly bound to the issuer OI by the CT entry
// identified by hash. Queries will be made to the given CT client.
// @ preserves acc(PkgMem(), _)
// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(hash)
// @ preserves acc(cl) && acc(cl.jsonClient)
// @ preserves rootKey != nil && rootKey.Mem()
// @ ensures err == nil ==> issuer != ""
func VerifyBinding(cl *client.LogClient, hash []byte, issuer string, rootKey jwk.Key) (err error) {

	kid, err := tokens.CalcKID(rootKey /*@, some(perm(1/2)) @*/)
	if err != nil {
		log.Print("could not calculate KID")
		return err
	}
	issuerUrl, err := url.Parse(issuer)
	// TODO: How to put this into url lib stub?
	// @ assume err == nil ==> (issuerUrl.Hostname() == "") == (issuer == "")
	if err != nil {
		log.Print("could not parse issuer")
		return err
	} else if issuerUrl.Hostname() == "" {
		return /*@ unfolding acc(PkgMem(), _) in @*/ ErrIssNoHostName
	}

	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(time.Minute))
	// @ assert cancel implements context.CancelFunc
	defer cancel() /*@ as context.CancelFunc @*/

	if sth, err := cl.GetSTH(ctx); err != nil {
		log.Print("could not fetch STH")
		return err
	} else if err := cl.VerifySTHSignature(*sth); err != nil {
		log.Print("STH not valid")
		return err
	} else if respH, err := cl.GetProofByHash(ctx, hash, sth.TreeSize); err != nil {
		log.Print("could not fetch proof by hash")
		return err
	} else if respE, err := cl.GetEntryAndProof(ctx, uint64(respH.LeafIndex), sth.TreeSize); err != nil {
		log.Print("could not fetch entry")
		return err
	} else if err := proof.VerifyInclusion(rfc6962.DefaultHasher, uint64(respH.LeafIndex), sth.TreeSize, hash, respE.AuditPath, toSlice((sth.SHA256RootHash))); err != nil {
		log.Print("could not verify inclusion proof")
		return err
	} else {
		var certT /*@@@*/ ct.CertificateTimestamp
		if _, err := tls.Unmarshal(respE.LeafInput, &certT); err != nil {
			log.Print("could not parse certificate timestamp")
			return err
		} else {
			// @ unfold certT.Mem()
			var cert *x509.Certificate
			var err error
			if certT.EntryType == ct.PrecertLogEntryType {
				cert, err = x509.ParseTBSCertificate(certT.PrecertEntry.TBSCertificate)
			} else if certT.EntryType == ct.X509LogEntryType {
				cert, err = x509.ParseCertificate(certT.X509Entry.Data)
			} else {
				err = /*@ unfolding acc(PkgMem(), _) in @*/ ErrWrongEntryType
			}
			if err != nil {
				log.Print("could not parse certificate")
				return err
			} else {
				subjects := append( /*@ perm(1/2), @*/ cert.DNSNames, cert.Subject.CommonName)
				if !util.ContainsString(subjects, issuerUrl.Hostname()) {
					return /*@ unfolding acc(PkgMem(), _) in @*/ ErrCertNotForIss
				} else if !util.ContainsString(subjects, fmt.Sprintf("%s.adem-configuration.%s", kid, issuerUrl.Hostname())) {
					return /*@ unfolding acc(PkgMem(), _) in @*/ ErrCertNotForKey
				}
			}
		}
	}
	return nil
}

// @ ensures acc(r)
func toSlice(h [32]byte) (r []byte) {
	// FIXME: (lmeinen) leaving the array to slice cast as-is (sth.SHA256RootHash[:]) causes a ClassCastException in SliceEncoding
	// @ share h
	return h[:]
}
