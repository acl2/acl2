; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "signed-in-signer")
(include-book "proposed-author-self")
(include-book "endorsed-author-other")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ author-round-pairs-in-validators
  :parents (correctness)
  :short "Author-round pairs in validator states."
  :long
  (xdoc::topstring
   (xdoc::p
    "An important notion for the correctness of the protocol
     is that of the author-round pairs in the state of a correct validator.
     These are the author-round pairs of the proposals
     (i) in (the certificates in) the DAG,
     (ii) in (the keys of) the pending proposal map, and
     (iii) in the set of endorsed proposals.
     Here we define this notion,
     and we prove some properties of it which are used elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-has-author+round-p ((author addressp)
                                      (round posp)
                                      (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a validator state includes a proposal
          with a given author or round
          in its DAG or pending proosal map or endorsed proposal set."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the DAG, it is equivalent to check whether
     there is a certificate with the given author and round,
     given that those are the same for the proposal in the certificate."))
  (b* (((validator-state vstate) vstate))
    (or (not (set::emptyp (certs-with-author+round
                           author round vstate.dag)))
        (not (set::emptyp (props-with-author+round
                           author round (omap::keys vstate.proposed))))
        (not (set::emptyp (props-with-author+round
                           author round vstate.endorsed)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled validator-has-author+round-p-when-signed-in-signer-p
  :short "Correct signers include, in their state,
          a record of the authors and rounds of
          all the proposals they have signed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case under
     the previously proved @(tsee signed-in-signer) invariant,
     which says that each proposal is
     either in the DAG
     or in (the set of keys of) the pending proposal map,
     or in the set of endorsed proposals.
     Then @(tsee validator-has-author+round-p) follows from the fact that
     retrieving proposals with that author and round
     must yield a non-empty result from at least one of the sets."))
  (implies (and (signed-in-signer-p systate)
                (set::in signer (correct-addresses systate))
                (set::in prop (signed-props signer systate)))
           (validator-has-author+round-p
            (proposal->author prop)
            (proposal->round prop)
            (get-validator-state signer systate)))
  :enable (validator-has-author+round-p
           emptyp-of-certs-with-author+round-to-props
           proposal-setp-of-keys-when-proposal-address-set-mapp)
  :use (signed-in-signer-p-necc
        (:instance in-of-props-with-author+round
                   (author (proposal->author prop))
                   (round (proposal->round prop))
                   (props (cert-set->prop-set
                           (validator-state->dag
                            (get-validator-state signer systate)))))
        (:instance in-of-props-with-author+round
                   (author (proposal->author prop))
                   (round (proposal->round prop))
                   (props (omap::keys
                           (validator-state->proposed
                            (get-validator-state signer systate)))))
        (:instance in-of-props-with-author+round
                   (author (proposal->author prop))
                   (round (proposal->round prop))
                   (props (validator-state->endorsed
                           (get-validator-state signer systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-validator-has-author+round-p-when-propose-possiblep
  :short "If a @('propose') event is possible,
          and the proposer is correct,
          then the proposer's state does not include
          any proposal with the proposed proposal's author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a @('propose') event,
     the proposer makes a weaker check,
     namely that the DAG has no certifcates with the author and round,
     and that the pending proposal map has no proposals with the round.
     However, under previously proved invariants,
     the weaker checks imply the stronger checks,
     i.e. that @(tsee validator-has-author+round-p) does not hold.")
   (xdoc::p
    "The check on the certificates of the DAG
     in @(tsee propose-possiblep)
     is equivalent to
     the check on the proposals of the DAG
     in @(tsee validator-has-author+round-p).")
   (xdoc::p
    "Under the @(see proposed-author-self) invariant,
     all the proposals in the pending proposal map
     are authored by the validator.
     So the weaker check that just involves the round
     in @(tsee propose-possiblep)
     is equivalent to
     the stronger check involving author and round
     in @(tsee validator-has-author+round-p).
     The key rules used in this part of the proof are
     @('props-with-author+round-to-props-with-round') and
     @('prop-set-all-author-p-when-proposed-author-self-p').")
   (xdoc::p
    "Under the @(see endorsed-author-other) invariant,
     all the proposals in the endorsed set are not authored by the validator.
     Does, that set can never contain a proposal
     with the validator as author (and with the validator's round).
     Thus, the check in @(tsee validator-has-author+round-p)
     would be redundant.
     The key rules used in this part of the proof are
     @('props-with-author+round-when-none-author') and
     @('prop-set-none-author-p-when-endorsed-author-other-p')."))
  (implies (and (proposed-author-self-p systate)
                (endorsed-author-other-p systate)
                (propose-possiblep prop dests systate)
                (set::in (proposal->author prop)
                         (correct-addresses systate)))
           (not (validator-has-author+round-p
                 (proposal->author prop)
                 (proposal->round prop)
                 (get-validator-state (proposal->author prop) systate))))
  :enable (propose-possiblep
           validator-has-author+round-p
           props-with-author+round-to-props-with-round
           prop-set-all-author-p-when-proposed-author-self-p
           props-with-author+round-when-none-author
           prop-set-none-author-p-when-endorsed-author-other-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-validator-has-author+round-p-when-endorse-possiblep
  :short "If an @('endorse') event is possible,
          and the endorser is correct,
          then the endorser's state does not include
          any proposal with the endorsed proposal's author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "In an @('endorse') event,
     the endorser make a weaker check,
     nameley that the DAG has no certifcates with the author and round,
     and that the pending proposal map has no proposals with the round.
     However, under previously proved invariants,
     the weaker checks imply the stronger checks,
     i.e. that @(tsee validator-has-author+round-p) does not hold.")
   (xdoc::p
    "The check on the certificates of the DAG
     in @(tsee propose-possiblep)
     is equivalent to
     the check on the proposals of the DAG
     in @(tsee validator-has-author+round-p).")
   (xdoc::p
    "Under the @(see proposal-to-other) invariant,
     the message that carries the proposal is addressed to
     a validator different from the author,
     so the endorser is different from the author.
     Under the @(see proposed-author-self) invariant,
     all the proposals in the pending proposal map of the endorser
     are authored by the endorser,
     which, as explained above, differs from the proposal author.
     Thus, checking the endorser's pending proposal map
     would be redundant.
     The key rules for this part of the proof are
     @('props-with-author+round-when-none-author') and
     @('prop-set-none-author-p-when-proposed-author-self-p').")
   (xdoc::p
    "The check on the endorsed proposal set
     in @(tsee endorse-possiblep)
     is equivalent to
     the check on the the endorsed proposal set
     in @(tsee validator-has-author+round-p)."))
  (implies (and (proposed-author-self-p systate)
                (proposal-to-other-p systate)
                (endorse-possiblep prop endor systate)
                (set::in endor (correct-addresses systate)))
           (not (validator-has-author+round-p
                 (proposal->author prop)
                 (proposal->round prop)
                 (get-validator-state endor systate))))
  :enable (endorse-possiblep
           validator-has-author+round-p
           props-with-author+round-when-none-author
           prop-set-none-author-p-when-proposed-author-self-p)
  :use (:instance proposal-to-other-p-necc
                  (prop (proposal-fix prop))
                  (dest endor))
  :cases ((equal (proposal->author prop)
                 (address-fix endor))))
