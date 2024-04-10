// +gobra
// ##(--onlyFilesWithHeader)
package vfy

import (
	"log"

	"github.com/adem-wg/adem-proto/pkg/consts"
	"github.com/adem-wg/adem-proto/pkg/tokens"
	// @ "github.com/adem-wg/adem-proto/pkg/ident"
	// @ . "lib"
	"github.com/lestrrat-go/jwx/v2/jwk"
	// @ "github.com/lestrrat-go/jwx/v2/jwa"
	// @ "github.com/lestrrat-go/jwx/v2/jwt"
	//@ "claim"
	//@ "fact"
	//@ "place"
	//@ "iospec"
	//@ "term"
	//@ "pub"
	//@ "fresh"
)

// @ preserves acc(tokens.PkgMem(), _)
// @ preserves acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
// @ preserves trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
// @ preserves ValidToken(emblem) && Emblem(emblem)
// @ preserves TokenList(endorsements)
// @ preserves unfolding TokenList(endorsements) in
// @ 	forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
// @ 		unfolding TokenListElem(i, endorsements[i]) in
// @ 		Endorsement(endorsements[i]))
// @ preserves unfolding TokenList(endorsements) in
// @ 	0 <= rootIdx && rootIdx < len(endorsements) &&
// @ 	endorsements[rootIdx] == root
// @ ensures acc(endorsedResults)
// @ ensures len(endorsedResults) <= 2 &&
// @ 	(forall i int :: { endorsedResults[i] } 0 <= i && i < len(endorsedResults) ==> endorsedResults[i] in seq[consts.VerificationResult] { consts.INVALID, consts.ENDORSED, consts.ENDORSED_TRUSTED }) &&
// @ 	(forall i, j int :: { endorsedResults[i] } 0 <= i && i < j && j < len(endorsedResults) ==> endorsedResults[i] != endorsedResults[j]) &&
// @ 	((exists i int :: { endorsedResults[i] } 0 <= i && i < len(endorsedResults) && endorsedResults[i] == consts.INVALID) ==> len(endorsedResults) == 1)
// @ ensures acc(endorsedBy)
func verifyEndorsed(emblem *ADEMToken, root *ADEMToken, endorsements []*ADEMToken, trustedKeys jwk.Set /*@, ghost rootIdx int, ghost p place.Place, ghost rid term.Term, ghost s mset[fact.Fact], ghost ai, oi term.Term, ghost terms seq[term.Term], ghost rootKey term.Term @*/) (
	endorsedResults []consts.VerificationResult, endorsedBy []string /*@, ghost p0 place.Place, ghost s0 mset[fact.Fact], ghost authTs seq[term.Term] @*/) {

	issuers := []string{}
	trustedFound := false
	existsEndorsement := false

	// @ unfold TokenList(endorsements)
	// @ ghost defer fold TokenList(endorsements)

	// @ ghost authTs := seq[term.Term] {}

	// @ invariant acc(tokens.PkgMem(), _)
	// @ invariant acc(&jwt.Custom, _) && acc(jwt.Custom, _) && tokens.CustomFields(jwt.Custom)
	// @ invariant trustedKeys != nil && trustedKeys.Mem() && acc(jwk.KeySeq(trustedKeys.Elems()), _)
	// @ invariant ValidToken(emblem) && Emblem(emblem)
	// @ invariant acc(endorsements)
	// @ invariant forall i int :: { TokenListElem(i, endorsements[i]) } 0 <= i && i < len(endorsements) ==> TokenListElem(i, endorsements[i])
	// @ invariant forall i int :: { endorsements[i] } 0 <= i && i < len(endorsements) ==> (
	// @ 	unfolding TokenListElem(i, endorsements[i]) in
	// @ 	Endorsement(endorsements[i]))
	// @ invariant 0 <= rootIdx && rootIdx < len(endorsements) &&
	// @ 	endorsements[rootIdx] == root
	// @ invariant issuers != nil && acc(issuers)
	for _, endorsement := range endorsements /*@ with i0 @*/ {
		// @ unfold acc(TokenListElem(i0, endorsements[i0]), 1/2)
		// @ unfold acc(ValidToken(endorsement), 1/2)

		// @ unfold acc(TokenListElem(rootIdx, root), 1/2)
		// @ unfold acc(ValidToken(root), 1/2)

		// @ unfold acc(ValidToken(emblem), 1/2)

		if endorsedKID, err := tokens.GetEndorsedKID(endorsement.Token); err != nil {
			log.Printf("could not not get endorsed kid: %s", err)
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if root.Token.Issuer() != endorsement.Token.Subject() {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if endorsement.Token.Issuer() == "" {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if end, _ := endorsement.Token.Get("end"); !end.(bool) {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if _, logged := endorsement.Token.Get("log"); !logged {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if root.VerificationKey.KeyID( /*@ none[perm] @*/ ) != endorsedKID {
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			continue
		} else if err := tokens.VerifyConstraints(emblem.Token, endorsement.Token); err != nil {
			log.Printf("emblem does not comply with endorsement constraints: %s", err)
			x := []consts.VerificationResult{consts.INVALID}
			// @ fold acc(ValidToken(emblem), 1/2)
			// @ fold acc(ValidToken(root), 1/2)
			// @ fold acc(TokenListElem(rootIdx, root), 1/2)
			// @ fold acc(ValidToken(endorsements[i0]), 1/2)
			// @ fold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			// @ assert len(x) == 1
			return x, nil /*@, p, s, seq[term.Term] { } @*/
		} else {
			/*@
			fold acc(ValidToken(emblem), 1/2)
			fold acc(ValidToken(root), 1/2)
			fold acc(TokenListElem(rootIdx, root), 1/2)
			unfold acc(TokenListElem(i0, endorsements[i0]), 1/2)
			fold acc(ValidToken(endorsement), 1/2)
			@*/

			existsEndorsement = true
			// @ unfold acc(ValidToken(endorsement), 1/2)
			issuers = append( /*@ perm(1/2), @*/ issuers, endorsement.Token.Issuer())
			_, ok := trustedKeys.LookupKeyID(endorsement.VerificationKey.KeyID( /*@ none[perm] @*/ ) /*@, perm(1/2) @*/)
			// @ fold acc(ValidToken(endorsement), 1/2)
			trustedFound = trustedFound || ok

			// @ fold TokenListElem(i0, endorsements[i0])
		}
	}

	if existsEndorsement {
		results := []consts.VerificationResult{consts.ENDORSED}
		if trustedFound {
			results = append( /*@ perm(1/2), @*/ results, consts.ENDORSED_TRUSTED)
		}
		// @ assert len(results) <= 2
		return results, issuers /*@, p, s, authTs @*/
	} else {
		return nil, nil /*@, p, s, seq[term.Term] {} @*/
	}
}
