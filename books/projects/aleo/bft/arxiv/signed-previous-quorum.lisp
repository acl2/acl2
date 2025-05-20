; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "signed-certificates")
(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signed-previous-quorum
  :parents (correctness)
  :short "Invariant that each certificate signed by a correct validator
          has references to previous certificates
          that form a non-zero quorum in the committee for the previous round,
          as calculated by that signing validator,
          unless the round is 1,
          in which case there are no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant is expressed on
     the set of certificates signed by a correct validator,
     as returned by @(tsee signed-certs).
     The invariant is satisfied by every certificate in that set,
     with respect to (the state of) the signing validator.")
   (xdoc::p
    "When a new certificate is created via a @('create') event,
     that event's preconditions require that the certificate includes
     a non-zero quorum of references to certificates in the previous round,
     unless the certificate round is 1,
     in which case there must be no references.")
   (xdoc::p
    "As proved in @(see signed-certs-of-next),
     the only kind of events that changes @(tsee signed-certs) is @('create').
     All the other kinds of events leave the set unchanged,
     and thus the invariant is preserved.")
   (xdoc::p
    "The names for this invariant,
     i.e. this XDOC topic as well as the function and theorem names,
     just mention `quorum' for brevity,
     even though that does not apply to round 1.
     But rounds greater than 1 are the ``normal'' case,
     while round 1 is a special case.
     The names do not mention the `non-zero' requirement either,
     but the quorum aspect is the main one here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-signed-previous-quorum-p ((cert certificatep)
                                            (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if either a certificate has round 1
          and it has no references to previous certificates,
          or the round is not 1 and
          the certificate's references to previous certificates
          are in the committee for the round just before the certificate round
          and form a non-zero quorum in that committee,
          where the committee is calculated by a validator
          (represented by its state)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee signed-previous-quorum-p) to define our invariant.
     The validator whose state is @('vstate') is
     the one that has signed the certificate.
     The guard ensures that the validator can calculate the committee.")
   (xdoc::p
    "The validator must be able to calculate the committee;
     this is part of the invariant definition.
     To check the non-zeroness of the quorum,
     we equivalently check the non-emptiness of the previous references."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (if (= cert.round 1)
        (set::emptyp cert.previous)
      (b* ((commtt
            (active-committee-at-round (1- cert.round) vstate.blockchain)))
        (and commtt
             (not (set::emptyp cert.previous))
             (set::subset cert.previous
                          (committee-members commtt))
             (>= (committee-members-stake cert.previous commtt)
                 (committee-quorum-stake commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signed-previous-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate signed by each correct validator,
          either the certificate's round is 1
          and the certificate has no references to previous certificates,
          or the certificate's round is not 1
          and the references to previous certificates
          form a non-zero quorum in the committee of
          the preceding round of the certificate."
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (signed-certs val systate)))
                   (validator-signed-previous-quorum-p
                    cert
                    (get-validator-state val systate))))
  ///
  (fty::deffixequiv-sk signed-previous-quorum-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-previous-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no signed certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (signed-previous-quorum-p systate))
  :enable (signed-previous-quorum-p
           signed-certs-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-previous-quorum-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that creates a new certificate is @('create').
     As proved in @(see signed-certs-of-next),
     @(tsee signed-certs) changes only under this kind of event.")
   (xdoc::p
    "For a @('create') event, there are two cases to consider.
     For an existing (i.e. old) certificate,
     the invariant is easily shown to be preserved,
     since the blockchain of the signer does not change.
     For the new certificate,
     the invariant is established by
     the conditions checked in @(tsee create-possiblep).")
   (xdoc::p
    "A @('commit') event does not introduce new certificates,
     but extends the blockchain of the target validator.
     However, as proved for other invariants,
     extending the blockchain does not affect
     the calculation of the previously calculable committees.
     But we need to assume some already proved invariants.")
   (xdoc::p
    "The other four kinds of events
     neither introduce new certificates
     nor modify blockchains,
     and so the preservation proof is easy."))

  ;; create:

  (defruled validator-signed-previous-quorum-p-of-create-next-old
    (implies (validator-signed-previous-quorum-p
              cert1
              (get-validator-state val systate))
             (validator-signed-previous-quorum-p
              cert1
              (get-validator-state val (create-next cert systate))))
    :enable (validator-signed-previous-quorum-p))

  (defruled validator-signed-previous-quorum-p-of-create-next-new
    (implies (and (create-possiblep cert systate)
                  (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate)))
             (validator-signed-previous-quorum-p
              cert
              (get-validator-state signer systate)))
    :use (:instance create-endorser-possiblep-when-create-endorsers-possiblep
                    (endorser signer))
    :enable (validator-signed-previous-quorum-p
             create-possiblep
             create-endorser-possiblep
             create-author-possiblep
             create-signer-possiblep
             certificate->signers))

  (defruled signed-previous-quorum-p-of-create-next
    (implies (and (signed-previous-quorum-p systate)
                  (create-possiblep cert systate))
             (signed-previous-quorum-p (create-next cert systate)))
    :enable (signed-previous-quorum-p
             signed-previous-quorum-p-necc
             signed-certs-of-create-next
             validator-signed-previous-quorum-p-of-create-next-old
             validator-signed-previous-quorum-p-of-create-next-new))

  ;; accept:

  (defruled validator-signed-previous-quorum-p-of-accept-next
    (implies (and (validator-signed-previous-quorum-p
                   cert
                   (get-validator-state val systate))
                  (accept-possiblep msg systate))
             (validator-signed-previous-quorum-p
              cert
              (get-validator-state val (accept-next msg systate))))
    :enable validator-signed-previous-quorum-p)

  (defruled signed-previous-quorum-p-of-accept-next
    (implies (and (signed-previous-quorum-p systate)
                  (accept-possiblep msg systate))
             (signed-previous-quorum-p (accept-next msg systate)))
    :enable (signed-previous-quorum-p
             signed-previous-quorum-p-necc
             signed-certs-of-accept-next
             validator-signed-previous-quorum-p-of-accept-next))

  ;; advance:

  (defruled validator-signed-previous-quorum-p-of-advance-next
    (implies (and (validator-signed-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (advance-possiblep val systate))
             (validator-signed-previous-quorum-p
              cert
              (get-validator-state val1 (advance-next val systate))))
    :enable validator-signed-previous-quorum-p)

  (defruled signed-previous-quorum-p-of-advance-next
    (implies (and (signed-previous-quorum-p systate)
                  (advance-possiblep val systate))
             (signed-previous-quorum-p (advance-next val systate)))
    :enable (signed-previous-quorum-p
             signed-previous-quorum-p-necc
             signed-certs-of-advance-next
             validator-signed-previous-quorum-p-of-advance-next))

  ;; commit:

  (defruled validator-signed-previous-quorum-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-signed-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (commit-possiblep val systate))
             (validator-signed-previous-quorum-p
              cert
              (get-validator-state val1 (commit-next val systate))))
    :enable (validator-signed-previous-quorum-p
             validator-state->blockchain-of-commit-next
             active-committee-at-round-of-extend-blockchain-no-change
             active-committee-at-previous-round-when-at-round
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp))

  (defruled signed-previous-quorum-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signed-previous-quorum-p systate)
                  (commit-possiblep val systate))
             (signed-previous-quorum-p (commit-next val systate)))
    :enable (signed-previous-quorum-p
             signed-previous-quorum-p-necc
             signed-certs-of-commit-next
             validator-signed-previous-quorum-p-of-commit-next))

  ;; all events:

  (defruled signed-previous-quorum-p-of-event-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signed-previous-quorum-p systate)
                  (event-possiblep event systate))
             (signed-previous-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-previous-quorum-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-even-p systate)
                (signed-previous-quorum-p systate))
           (signed-previous-quorum-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-previous-quorum-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (signed-previous-quorum-p systate))
  :enable (system-state-reachablep
           signed-previous-quorum-p-when-init
           ordered-even-p-when-init
           last-blockchain-round-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-even-p from)
                   (signed-previous-quorum-p from))
              (signed-previous-quorum-p systate))
     :use (:instance
           signed-previous-quorum-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
