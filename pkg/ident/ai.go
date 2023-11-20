// +gobra
// ##(--onlyFilesWithHeader)
// @ initEnsures PkgMem()
package ident

import (
	"encoding/json"
	"errors"
	"fmt"
	"net"
	"regexp"
	"strconv"
	"strings"

	"github.com/adem-wg/adem-proto/pkg/util"
)

func init() {
	// @ fold PkgMem()
}

var ErrIllegalAI = errors.New("illegal asset identifier")
var ErrNoAddress = errors.New("no address component")
var ErrIllegalAddress = errors.New("illegal address component")
var ErrWildcard = errors.New("illegal usage of domain name wildcards")

type AI struct {
	domainName []string
	ipAddr     net.IP
	ipPrefix   *net.IPNet
	port       *uint16
}

// @ preserves acc(labels, 1/2)
func joinDomain(labels []string) string {
	if len(labels) == 1 && labels[0] == "*" {
		return ""
	} else if len(labels) > 1 && labels[0] == "*" {
		// @ assert let subslice := labels[1:] in
		// @ 	forall i int :: 0 <= i && i < len(subslice) ==> &subslice[i] == &labels[i + 1]
		return "." + strings.Join(labels[1:], ".")
	} else {
		return strings.Join(labels, ".")
	}
}

// @ preserves ai.Mem()
// @ preserves than.Mem()
func (ai *AI) MoreGeneral(than *AI) bool {
	// @ unfold ai.Mem()
	// @ ghost defer fold ai.Mem()
	// @ unfold than.Mem()
	// @ ghost defer fold than.Mem()

	if ai.port != nil && (ai.port != than.port || *ai.port != *than.port) {
		return false
	}

	if ai.domainName != nil {
		if len(than.domainName) == 0 {
			return false
		}

		aiJoined := joinDomain(ai.domainName)
		thanJoined := joinDomain(than.domainName)
		if ai.domainName[0] == "*" {
			// @ assert let subslice := ai.domainName[1:] in
			// @ 	forall i int :: 0 <= i && i < len(subslice) ==> &subslice[i] == &ai.domainName[i + 1]
			return thanJoined == joinDomain(ai.domainName[1:]) || strings.HasSuffix(thanJoined, aiJoined)
		} else {
			return thanJoined == aiJoined
		}
	} else if ai.ipAddr != nil {
		return ai.ipAddr.Equal(than.ipAddr)
	} else if ai.ipPrefix != nil {
		if than.ipAddr != nil {
			return ai.ipPrefix.Contains(than.ipAddr)
		} else if than.ipPrefix != nil {
			// TODO: Can something weird happen if than.IPPrefix.IP is actual shorter
			// than ai.IPPrefix but has matching leading bytes?
			return /*@ unfolding than.ipPrefix.Mem() in @*/ ai.ipPrefix.Contains(than.ipPrefix.IP)
		} else {
			return false
		}
	} else {
		panic("illegal state")
	}
}

// @ preserves ai.Mem()
// @ preserves PkgMem()
// @ requires acc(bs)
func (ai *AI) UnmarshalJSON(bs []byte) error {
	var str /*@@@*/ string
	// @ fold PredTrue!<!>()
	err := json.Unmarshal(bs, &str /*@, PredTrue!<!> @*/)
	// @ unfold PredTrue!<!>()
	if err != nil {
		return err
	} else if parsed, err := ParseAI(str); err != nil {
		return err
	} else {
		// @ unfold parsed.Mem()
		// @ unfold ai.Mem()
		ai.domainName = parsed.domainName
		ai.ipAddr = parsed.ipAddr
		ai.ipPrefix = parsed.ipPrefix
		ai.port = parsed.port
		// @ fold ai.Mem()
		return nil
	}
}

var portReg *regexp.Regexp = regexp.MustCompile(`:(\d+)$`)

/* (lmeinen) AIs follow the below syntax:
asset-identifier = address [ ":" port ]
address = domain-name | "[" IPv6 "]"
port = DIGIT+
*/
// @ preserves PkgMem()
// @ ensures err == nil ==> r.Mem()
func ParseAI(aiStr string) (r *AI, err error) {
	var addr, port string
	// @ unfold PkgMem()
	// @ ghost defer fold PkgMem()
	matches := portReg.FindStringSubmatch(aiStr)
	if len(matches) == 2 {
		addr = aiStr[:len(aiStr)-len(matches[0])]
		port = matches[1]
	} else {
		addr = aiStr
	}

	// TODO: (lmeinen) Can we drop this assumption?
	// @ assume forall s string :: s != "" ==> len(s) > 0
	if addr == "" {
		return nil, ErrIllegalAI
	}

	ai /*@@@*/ := AI{}
	if isIPv6(addr) {
		// must be IPv6
		var trimmed string
		if len(addr) > 1 {
			// avoid access of the form addr[1:0] if addr only consists of '['
			trimmed = addr[1 : len(addr)-1] // drop [...]
		} else {
			trimmed = ""
		}

		if ip := net.ParseIP(trimmed); ip != nil {
			ai.ipAddr = ip
		} else if _, net, err := net.ParseCIDR(trimmed); err == nil {
			ai.ipPrefix = net
		} else {
			return nil, ErrIllegalAddress
		}
	} else {
		// TODO: I should check labels for allowed characters of domain names
		// Only leftmost label may be wildcard
		if strings.Contains(addr[1:], "*") {
			return nil, ErrWildcard
		} else if labels := strings.Split(addr, "."); len(labels) <= 0 {
			// This should not be possible according to strings.Split docs
			panic("illegal state")
		} else if util.ContainsString(labels, "" /*@, perm(1/2) @*/) {
			// No empty labels allowed
			return nil, ErrIllegalAI
		} else if strings.Contains(labels[0], "*") && len(labels[0]) > 1 {
			// If leftmost label is wildcard, leftmost label may be the wildcard only
			return nil, ErrWildcard
		} else {
			ai.domainName = labels
		}
	}

	if port != "" {
		if p, err := strconv.ParseInt(port, 10, 16); err != nil {
			return nil, err
		} else {
			unsiged /*@@@*/ := uint16(p)
			ai.port = &unsiged
		}
	}

	// @ fold ai.Mem()
	return &ai, nil
}

// @ preserves ai.Mem()
func (ai *AI) String() string {
	// @ unfold ai.Mem()
	// @ ghost defer fold ai.Mem()

	var port string
	if ai.port != nil {
		port = fmt.Sprintf(":%d", *ai.port)
	}

	var addr string
	if ai.domainName != nil {
		addr = strings.Join(ai.domainName, ".")
	} else if ai.ipAddr != nil {
		addr = fmt.Sprintf("[%s]", ai.ipAddr.String())
	} else if ai.ipPrefix != nil {
		addr = fmt.Sprintf("[%s]", ai.ipPrefix.String())
	} else {
		panic("illegal state")
	}
	return addr + port
}

// @ preserves ai.Mem()
// @ preserves PkgMem()
// @ ensures err == nil ==> acc(bs)
func (ai *AI) MarshalJSON() (bs []byte, err error) {
	return json.Marshal(ai.String())
}

// @ trusted
// @ requires len(s) > 0
func isIPv6(s string) bool {
	// FIXME: (lmeinen) is there any way I can reduce this trusted function?
	// string indexing is currently not supported by Gobra
	return s[0] == '['
}

/*@
pred PkgMem() {
	acc(portReg) &&
		ErrIllegalAI != nil &&
		ErrNoAddress != nil &&
		ErrIllegalAddress != nil &&
		ErrWildcard != nil
}

pred (ai *AI) Mem() {
	acc(ai) &&
		(ai.domainName != nil || ai.ipAddr != nil || ai.ipPrefix != nil) &&
		(ai.domainName != nil ==> acc(ai.domainName) &&
			len(ai.domainName) > 0 &&
			forall i int :: 0 <= i && i < len(ai.domainName) ==> len(ai.domainName[i]) > 0) &&
		(ai.ipAddr != nil ==> ai.ipAddr.Mem()) &&
		(ai.ipPrefix != nil ==> ai.ipPrefix.Mem()) &&
		(ai.port != nil ==> acc(ai.port))

}
@*/
