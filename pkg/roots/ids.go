// +gobra
// ##(--onlyFilesWithHeader)
// @ initEnsures PkgMem()
package roots

import (
	"bytes"
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"sync"

	"github.com/adem-wg/adem-proto/pkg/util"
	"github.com/google/certificate-transparency-go/client"
	"github.com/google/certificate-transparency-go/jsonclient"
)

var ErrUnknownLog = errors.New("unknown log")

const log_list_google = "https://www.gstatic.com/ct/log_list/v3/log_list.json"
const log_list_apple = "https://valid.apple.com/ct/log_list/current_log_list.json"

// Map that stores Certificate Transparency log info associated to their IDs.
var ctLogs /*@@@*/ map[string]CTLog = make(map[string]CTLog)

// [ctLogs] access lock.
var logMapLock /*@@@*/ sync.Mutex = sync.Mutex{}

func init() {
	// @ fold LockInv!<&ctLogs!>()
	// @ logMapLock.SetInv(LockInv!<&ctLogs!>)

	// TODO: (lmeinen) Gobra doesn't handle init order properly yet - really these assumptions should already hold
	// @ assume ErrIssNoHostName != nil &&
	// @ 	ErrCertNotForIss != nil &&
	// @ 	ErrCertNotForKey != nil &&
	// @ 	ErrWrongEntryType != nil

	// @ fold PkgMem()
}

// @ preserves acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
// @ requires acc(rawJson)
func storeLogs(rawJson []byte) error {
	logMapLock.Lock()
	defer logMapLock.Unlock()
	// @ unfold LockInv!<&ctLogs!>()
	// @ defer fold LockInv!<&ctLogs!>()

	logs /*@@@*/ := KnownLogs{}
	// @ fold LogsMem!<&logs!>()
	err := json.Unmarshal(rawJson, &logs /*@, LogsMem!<&logs!> @*/)

	if err != nil {
		return err
	}

	// @ unfold LogsMem!<&logs!>()

	s := logs.Operators
	// @ invariant acc(&ctLogs) && acc(ctLogs)
	// @ invariant acc(s) &&
	// @ 	forall i int :: 0 <= i && i0 <= i && i < len(s) ==> acc(s[i].Logs)
	for _, operator := range s /*@ with i0 @*/ {
		ls := operator.Logs
		// @ invariant acc(&ctLogs) && acc(ctLogs)
		// @ invariant acc(ls)
		for _, l := range ls /*@ with j0 @*/ {
			ctLogs[l.Id] = l
		}
	}

	return nil
}

// Get the log client associate to a CT log ID.
// @ preserves acc(PkgMem(), _)
// @ ensures err == nil ==> acc(cl) && acc(cl.jsonClient)
func GetLogClient(id string) (cl *client.LogClient, err error) {
	// @ unfold acc(PkgMem(), _)
	// @ ghost defer fold acc(PkgMem(), _)
	logMapLock.Lock()
	defer logMapLock.Unlock()
	// @ unfold LockInv!<&ctLogs!>()
	// @ defer fold LockInv!<&ctLogs!>()
	log, ok := ctLogs[id]
	if !ok {
		return nil, ErrUnknownLog
	}

	return client.New(log.Url, http.DefaultClient, jsonclient.Options{PublicKeyDER: log.Key.raw})
}

// Partial JSON scheme of [log_list_google] and [log_list_apple].
type KnownLogs struct {
	Operators []Operator `json:"operators"`
}

type Operator struct {
	Logs []CTLog `json:"logs"`
}

type CTLog struct {
	Key LogKey `json:"key"`
	Id  string `json:"log_id"`
	Url string `json:"url"`
}

// Wrapper type for JSON unmarshalling of CT log public keys.
type LogKey struct {
	raw []byte
}

// Decodes a base64-encoded JSON string into a CT log public key.
// @ preserves acc(k) && acc(k.raw)
// @ requires acc(bs)
func (k *LogKey) UnmarshalJSON(bs []byte) (err error) {
	if raw, e := util.B64Dec(bytes.Trim(bs, `"`)); e != nil {
		err = e
	} else {
		k.raw = raw
	}
	return
}

// Load logs from a given log list.
// @ preserves acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
func fetchLogs(url string) error {
	resp, err := http.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return err
	}

	return storeLogs(body)
}

// Load logs known to Google.
// @ preserves acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
func FetchGoogleKnownLogs() error {
	return fetchLogs(log_list_google)
}

// Load logs known to Apple.
// @ preserves acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
func FetchAppleKnownLogs() error {
	return fetchLogs(log_list_apple)
}

// @ preserves acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
func ReadKnownLogs(pattern string) error {
	matches, err := filepath.Glob(pattern)
	if err != nil {
		return err
	}

	// @ invariant acc(logMapLock.LockP(), _) && logMapLock.LockInv() == LockInv!<&ctLogs!>
	// @ invariant acc(matches)
	for _, path := range matches {
		if bs, err := os.ReadFile(path); err != nil {
			return err
		} else if err := storeLogs(bs); err != nil {
			return err
		}
	}

	return nil
}

/*@

pred LockInv(ctLogs *map[string]CTLog) {
	acc(ctLogs) && acc(*ctLogs)
}

pred LogsMem(logs *KnownLogs) {
	acc(logs) &&
		acc(logs.Operators) &&
		forall i int :: 0 <= i && i < len(logs.Operators) ==> acc(logs.Operators[i].Logs)
}

pred PkgMem() {
	logMapLock.LockP() &&
	logMapLock.LockInv() == LockInv!<&ctLogs!> &&
	ErrUnknownLog != nil &&
	ErrIssNoHostName != nil &&
	ErrCertNotForIss != nil &&
	ErrCertNotForKey != nil &&
	ErrWrongEntryType != nil
}
@*/
