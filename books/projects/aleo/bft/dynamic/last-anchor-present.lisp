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

(include-book "ordered-even-blocks")
(include-book "last-anchor-def-and-init")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-present
  :parents (correctness)
  :short "Invariant that the last committed round, if non-zero,
          has an anchor certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0, so the invariant trivially holds.
     The only kind of event that modifies the last committed round
     is @('commit-anchors'), which is conditioned under the fact that
     there is a certificate anchor for the new last committed round;
     see @(tsee commit-anchors-possiblep).
     The other events do not change the last committed round,
     and certificates are never removed from the DAG,
     so if there was an anchor at the last committed round before the event,
     there is still one after the event."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-anchor-present-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator,
          if the last committed round is not 0,
          there is an anchor at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This predicate implicitly requires that the validator
     can calculate the active committee at the last committed round (if not 0),
     because otherwise @(tsee last-anchor) returns @('nil')."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* ((vstate (get-validator-state val systate)))
                     (implies (not (equal (validator-state->last vstate) 0))
                              (last-anchor vstate
                                           (all-addresses systate))))))
  ///
  (fty::deffixequiv-sk last-anchor-present-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-present-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round is initially 0,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (last-anchor-present-p systate))
  :enable (last-anchor-present-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-present-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each kind of event,
     we first prove a theorem (or two in the case of @('commit-anchors'))
     about the preservation of @(tsee last-anchor) being not @('nil'),
     which we use in the proof of the main theorem for each event.")
   (xdoc::p
    "The definition of @(tsee last-anchor) depends on
     the DAG, blockchain, and last committed round of a validator.
     The proofs are based on how the events modify (or not) these components.")
   (xdoc::p
    "A @('create-certificate') event modifies the DAG of the author
     but not its blockchain or last committed round.
     However, in general the extension of a set of certificates
     preserves the fact that @(tsee cert-with-author+round)
     is not @('nil') (see @('cert-with-author+round-of-insert-iff')),
     although technically it may not return the same certificate,
     unless one assumes unequivocation (which is not needed here).
     For validators different from the author,
     there is no change to the DAG or last committed round.")
   (xdoc::p
    "A @('store-certificate') event modifies the DAG of the target validator
     but not its blockchain or last committed round.
     However, similarly to the @('create-certificate') case,
     the extension of the DAG preserves the fact that
     @(tsee cert-with-author+round) is not @('nil').")
   (xdoc::p
    "A @('commit-anchors') event modifies
     the blockchain and last committed round of the target validator,
     but not its DAG.
     The event is conditioned by @(tsee commit-anchors-possiblep),
     which requires the presence in the DAG of the certificate
     that becomes the new last anchor.
     But we need to show that the extension of the blockchain
     does not affect the choice of the leader for that round,
     so we use @('active-committee-at-round-of-extend-blockchain-no-change')
     and additional rules to discharge its hypotheses,
     similarly to other invariant preservation proofs
     that involve calculations of committees.
     This needs the already proved invariants that
     blocks have ordered even rounds
     and that the last committed block is the one of the latest block.
     Our theorem for this case of @('commit-anchors')
     is @('last-anchor-not-nil-of-commit-anchors-next-same'),
     while @('last-anchor-not-nil-of-commit-anchors-next-diff')
     takes care of the case of a validator that is not the event's target,
     whose DAG, blockchain, and last committed round do not change.")
   (xdoc::p
    "The other three kinds of events do not change
     any DAG or blockchain or last committed round,
     so the preservation of the invariant is easy to prove."))

  ;; create-certificate:

  (defruled last-anchor-not-nil-of-create-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (create-certificate-next cert systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             validator-state->dag-of-create-certificate-next
             cert-with-author+round-of-insert-iff))

  (defruled last-anchor-present-p-of-create-certificate-next
    (implies (last-anchor-present-p systate)
             (last-anchor-present-p
              (create-certificate-next cert systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-create-certificate-next
             validator-state->last-of-create-certificate-next))

  ;; receive-certificate:

  (defruled last-anchor-not-nil-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (last-anchor (get-validator-state
                           val (receive-certificate-next msg systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next))

  (defruled last-anchor-present-p-of-receive-certificate-next
    (implies (and (last-anchor-present-p systate)
                  (receive-certificate-possiblep msg systate))
             (last-anchor-present-p
              (receive-certificate-next msg systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-receive-certificate-next
             validator-state->last-of-receive-certificate-next))

  ;; store-certificate:

  (defruled last-anchor-not-nil-of-store-certificate-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (last-anchor (get-validator-state val1 systate)
                               (all-addresses systate))
                  (store-certificate-possiblep val cert systate))
             (last-anchor (get-validator-state
                           val1 (store-certificate-next val cert systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-store-certificate-next
             validator-state->blockchain-of-store-certificate-next
             validator-state->dag-of-store-certificate-next
             cert-with-author+round-of-insert-iff))

  (defruled last-anchor-present-p-of-store-certificate-next
    (implies (and (last-anchor-present-p systate)
                  (store-certificate-possiblep val cert systate))
             (last-anchor-present-p
              (store-certificate-next val cert systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-store-certificate-next
             validator-state->last-of-store-certificate-next))

  ;; advance-round:

  (defruled last-anchor-not-nil-of-advance-round-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (last-anchor (get-validator-state val1 systate)
                               (all-addresses systate))
                  (advance-round-possiblep val systate))
             (last-anchor (get-validator-state
                           val1 (advance-round-next val systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             validator-state->dag-of-advance-round-next))

  (defruled last-anchor-present-p-of-advance-round-next
    (implies (and (last-anchor-present-p systate)
                  (advance-round-possiblep msg systate))
             (last-anchor-present-p
              (advance-round-next msg systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-advance-round-next
             validator-state->last-of-advance-round-next))

  ;; commit-anchors:

  (defruled last-anchor-not-nil-of-commit-anchors-next-diff
    (implies (and (set::in val1 (correct-addresses systate))
                  (not (equal (address-fix val1)
                              (address-fix val)))
                  (commit-anchors-possiblep val systate)
                  (last-anchor (get-validator-state val1 systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val1 (commit-anchors-next val systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next))

  (defruled last-anchor-not-nil-of-commit-anchors-next-same
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (commit-anchors-possiblep val systate))
             (last-anchor (get-validator-state
                           val (commit-anchors-next val systate))
                          (all-addresses systate)))
    :use (:instance lemma (val (address-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (ordered-even-p systate)
                     (last-blockchain-round-p systate)
                     (addressp val)
                     (commit-anchors-possiblep val systate))
                (last-anchor (get-validator-state
                              val (commit-anchors-next val systate))
                             (all-addresses systate)))
       :enable (last-anchor
                commit-anchors-possiblep
                validator-state->last-of-commit-anchors-next
                validator-state->blockchain-of-commit-anchors-next
                validator-state->dag-of-commit-anchors-next
                active-committee-at-previous-round-when-at-round
                active-committee-at-round-of-extend-blockchain-no-change
                blocks-ordered-even-p-of-extend-blockchain
                certificates-ordered-even-p-of-collect-anchors
                ordered-even-p-necc-fixing
                collect-anchors-above-last-committed-round
                last-blockchain-round-p-necc-fixing
                posp
                evenp
                certificate->round-of-cert-with-author+round))))

  (defruled last-anchor-present-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (last-anchor-present-p systate)
                  (commit-anchors-possiblep val systate))
             (last-anchor-present-p
              (commit-anchors-next val systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-commit-anchors-next-diff
             last-anchor-not-nil-of-commit-anchors-next-same
             validator-state->last-of-commit-anchors-next))

  ;; timer-expires:

  (defruled last-anchor-not-nil-of-timer-expires-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (last-anchor (get-validator-state val1 systate)
                               (all-addresses systate))
                  (timer-expires-possiblep val systate))
             (last-anchor (get-validator-state
                           val1 (timer-expires-next val systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->last-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             validator-state->dag-of-timer-expires-next))

  (defruled last-anchor-present-p-of-timer-expires-next
    (implies (and (last-anchor-present-p systate)
                  (timer-expires-possiblep msg systate))
             (last-anchor-present-p
              (timer-expires-next msg systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-timer-expires-next
             validator-state->last-of-timer-expires-next))

  ;; all events:

  (defruled last-anchor-present-p-of-event-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (last-anchor-present-p systate)
                  (event-possiblep event systate))
             (last-anchor-present-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-present-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled last-anchor-present-p-of-events-next
    (implies (and (last-anchor-present-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (and (last-anchor-present-p (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             last-anchor-present-p-of-event-next
             ordered-even-p-of-event-next
             last-blockchain-round-p-of-event-next))

  (defruled last-anchor-present-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (last-anchor-present-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (last-anchor-present-p-when-init
             ordered-even-p-when-init
             last-blockchain-round-p-when-init
             last-anchor-present-p-of-events-next)))
