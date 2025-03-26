; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "certificates-of-validators")
(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ accepted-certificate-committee
  :parents (correctness)
  :short "Invariant that validators know
          the active committees at the rounds of their accepted certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via @('create-certificate'),
     the author must know the active committee at the certificate's round,
     which it uses to check quorum conditions.")
   (xdoc::p
    "When a certificate is received via @('receive-certificate'),
     the receiver must know the active committee at the certificate's round,
     which it uses to check quorum conditions.")
   (xdoc::p
    "The above events are the only ones that extend
     the set of certificates accepted by a validator.
     Thus, it is the case that the active committee
     at the round of each certificate accepted by a validator
     is known to (i.e. calculable by) the validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk accepted-certificate-committee-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every certificate accepted by a validator,
          the validator can calculate the active committee
          at the round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that this invariant implies @(tsee dag-committees-p),
     i.e. that every certificate in the DAG of every correct validator
     has a calculable active committee at the certificate's round.
     While we need to formulate and prove this invariant
     on all accepted certificates
     to have a sufficiently strong induction hypothesis,
     we are mainly interested in the certificates in the DAG."))
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (accepted-certificates val systate)))
                   (active-committee-at-round
                    (certificate->round cert)
                    (validator-state->blockchain
                     (get-validator-state val systate))
                    (all-addresses systate))))

  ///

  (fty::deffixequiv-sk accepted-certificate-committee-p
    :args ((systate system-statep)))

  (defruled accepted-certificate-committee-p-necc-fixing-binding
    (implies (and (accepted-certificate-committee-p systate)
                  (set::in (address-fix val) (correct-addresses systate))
                  (set::in cert (accepted-certificates val systate))
                  (equal blockchain
                         (validator-state->blockchain
                          (get-validator-state val systate))))
             (active-committee-at-round (certificate->round cert)
                                        blockchain
                                        (all-addresses systate)))
    :use (:instance accepted-certificate-committee-p-necc
                    (val (address-fix val))))

  (defruled dag-committees-p-when-accepted-certificate-committee-p
    (implies (and (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate)))
             (dag-committees-p (validator-state->dag
                                (get-validator-state val systate))
                               (validator-state->blockchain
                                (get-validator-state val systate))
                               (all-addresses systate)))
    :enable (dag-committees-p
             accepted-certificate-committee-p-necc
             accepted-certificates)
    :disable accepted-certificate-committee-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled accepted-certificate-committee-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no accepted certificates in the system,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (accepted-certificate-committee-p systate))
  :enable (accepted-certificate-committee-p
           accepted-certificates-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection accepted-certificate-committee-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('create-certificate') and @('receive-certificate'),
     which may extend the set of accepted certificates,
     we open @(tsee create-certificate-possiblep)
     and @(tsee receive-certificate-possiblep)
     to expose the fact that author or receiver
     can calculate the committee at the round
     of the created or received certificate.
     For already accepted certificates,
     the ability to calculate the committee follows from
     the assumption of the invariant in the state before the transition.")
   (xdoc::p
    "The other events do not change the accepted certificates or blockchains,
     but @('commit-anchors') changes the blockchain of the target validator.
     However, it extends it, and thus the previously calculated committee
     can be still calculated with the extended blockchain:
     the main rule used for this is
     @('active-committee-at-round-of-extend-blockchain-no-change'),
     along with others to relieve its hypotheses."))

  (defruled accepted-certificate-committee-p-of-create-certificate-next
    (implies (and (accepted-certificate-committee-p systate)
                  (create-certificate-possiblep cert systate))
             (accepted-certificate-committee-p
              (create-certificate-next cert systate)))
    :enable (accepted-certificate-committee-p
             accepted-certificate-committee-p-necc
             validator-state->blockchain-of-create-certificate-next
             accepted-certificates-of-create-certificate-next
             create-certificate-possiblep
             create-certificate-author-possiblep))

  (defruled accepted-certificate-committee-p-of-receive-certificate-next
    (implies (and (accepted-certificate-committee-p systate)
                  (receive-certificate-possiblep msg systate))
             (accepted-certificate-committee-p
              (receive-certificate-next msg systate)))
    :enable (accepted-certificate-committee-p
             accepted-certificate-committee-p-necc
             validator-state->blockchain-of-receive-certificate-next
             accepted-certificates-of-receive-certificate-next
             receive-certificate-possiblep))

  (defruled accepted-certificate-committee-p-of-store-certificate-next
    (implies (and (accepted-certificate-committee-p systate)
                  (store-certificate-possiblep val cert systate))
             (accepted-certificate-committee-p
              (store-certificate-next val cert systate)))
    :enable (accepted-certificate-committee-p
             accepted-certificate-committee-p-necc
             validator-state->blockchain-of-store-certificate-next
             accepted-certificates-of-store-certificate-next))

  (defruled accepted-certificate-committee-p-of-advance-round-next
    (implies (and (accepted-certificate-committee-p systate)
                  (advance-round-possiblep val systate))
             (accepted-certificate-committee-p
              (advance-round-next val systate)))
    :enable (accepted-certificate-committee-p
             accepted-certificate-committee-p-necc
             validator-state->blockchain-of-advance-round-next
             accepted-certificates-of-advance-round-next))

  (defruled accepted-certificate-committee-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (commit-anchors-possiblep val systate))
             (accepted-certificate-committee-p
              (commit-anchors-next val systate)))
    :use (:instance accepted-certificate-committee-p-necc
                    (val (mv-nth 0
                                 (accepted-certificate-committee-p-witness
                                  (commit-anchors-next val systate))))
                    (cert (mv-nth 1
                                  (accepted-certificate-committee-p-witness
                                   (commit-anchors-next val systate)))))
    :enable (accepted-certificate-committee-p
             validator-state->blockchain-of-commit-anchors-next
             accepted-certificates-of-commit-anchors-next
             commit-anchors-possiblep
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-anchors-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             evenp
             certificate->round-of-certificate-with-author+round))

  (defruled accepted-certificate-committee-p-of-timer-expires-next
    (implies (and (accepted-certificate-committee-p systate)
                  (timer-expires-possiblep val systate))
             (accepted-certificate-committee-p
              (timer-expires-next val systate)))
    :enable (accepted-certificate-committee-p
             accepted-certificate-committee-p-necc
             validator-state->blockchain-of-timer-expires-next
             accepted-certificates-of-timer-expires-next))

  (defruled accepted-certificate-committee-p-of-event-next
    (implies (and (accepted-certificate-committee-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (event-possiblep event systate))
             (accepted-certificate-committee-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection accepted-certificate-committee-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled accepted-certificate-committee-p-of-events-next
    (implies (and (accepted-certificate-committee-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (and (accepted-certificate-committee-p (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             accepted-certificate-committee-p-of-event-next
             ordered-even-p-of-event-next
             last-blockchain-round-p-of-event-next))

  (defruled accepted-certificate-committee-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (accepted-certificate-committee-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (accepted-certificate-committee-p-when-init
             ordered-even-p-when-init
             last-blockchain-round-p-when-init
             accepted-certificate-committee-p-of-events-next)))
