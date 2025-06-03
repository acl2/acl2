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

(include-book "ordered-blockchain")
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
     is @('commit'), which is conditioned under the fact that
     there is a certificate anchor for the new last committed round;
     see @(tsee commit-possiblep).
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
                              (last-anchor vstate)))))
  ///
  (fty::deffixequiv-sk last-anchor-present-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule last-anchor-present-p-when-init
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
     we first prove a theorem (or two in the case of @('commit'))
     about the preservation of @(tsee last-anchor) being not @('nil'),
     which we use in the proof of the main theorem for each event.")
   (xdoc::p
    "The definition of @(tsee last-anchor) depends on
     the DAG, blockchain, and last committed round of a validator.
     The proofs are based on how the events modify (or not) these components.")
   (xdoc::p
    "A @('create') event modifies the DAG of the author
     but not its blockchain or last committed round.
     However, in general the extension of a set of certificates
     preserves the fact that @(tsee cert-with-author+round)
     is not @('nil') (see @('cert-with-author+round-of-insert-iff')),
     although technically it may not return the same certificate,
     unless one assumes unequivocation (which is not needed here).
     For validators different from the author,
     there is no change to the DAG or last committed round.")
   (xdoc::p
    "An @('accept') event modifies the DAG of the target validator
     but not its blockchain or last committed round.
     However, similarly to the @('create') case,
     the extension of the DAG preserves the fact that
     @(tsee cert-with-author+round) is not @('nil').")
   (xdoc::p
    "A @('commit') event modifies
     the blockchain and last committed round of the target validator,
     but not its DAG.
     The event is conditioned by @(tsee commit-possiblep),
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
     Our theorem for this case of @('commit')
     is @('last-anchor-not-nil-of-commit-next-same'),
     while @('last-anchor-not-nil-of-commit-next-diff')
     takes care of the case of a validator that is not the event's target,
     whose DAG, blockchain, and last committed round do not change.")
   (xdoc::p
    "An @('advance') event does not change
     any DAG or blockchain or last committed round,
     so the preservation of the invariant is easy to prove."))

  ;; create:

  (defruled last-anchor-not-nil-of-create-next
    (implies (and (set::in val (correct-addresses systate))
                  (last-anchor (get-validator-state val systate)))
             (last-anchor (get-validator-state
                           val (create-next cert systate))))
    :enable (last-anchor
             validator-state->dag-of-create-next
             cert-with-author+round-of-insert-iff))

  (defruled last-anchor-present-p-of-create-next
    (implies (last-anchor-present-p systate)
             (last-anchor-present-p (create-next cert systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-create-next))

  ;; accept:

  (defruled last-anchor-not-nil-of-accept-next
    (implies (and (set::in val (correct-addresses systate))
                  (last-anchor (get-validator-state val systate))
                  (accept-possiblep msg systate))
             (last-anchor (get-validator-state
                           val (accept-next msg systate))))
    :enable (last-anchor
             validator-state->dag-of-accept-next
             cert-with-author+round-of-insert-iff))

  (defruled last-anchor-present-p-of-accept-next
    (implies (and (last-anchor-present-p systate)
                  (accept-possiblep msg systate))
             (last-anchor-present-p (accept-next msg systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-accept-next))

  ;; advance:

  (defruled last-anchor-not-nil-of-advance-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (last-anchor (get-validator-state val1 systate))
                  (advance-possiblep val systate))
             (last-anchor (get-validator-state
                           val1 (advance-next val systate))))
    :enable last-anchor)

  (defruled last-anchor-present-p-of-advance-next
    (implies (and (last-anchor-present-p systate)
                  (advance-possiblep msg systate))
             (last-anchor-present-p (advance-next msg systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-advance-next))

  ;; commit:

  (defruled last-anchor-not-nil-of-commit-next-diff
    (implies (and (set::in val1 (correct-addresses systate))
                  (not (equal (address-fix val1)
                              (address-fix val)))
                  (commit-possiblep val systate)
                  (last-anchor (get-validator-state val1 systate)))
             (last-anchor (get-validator-state
                           val1 (commit-next val systate))))
    :enable (last-anchor
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next))

  (defruled last-anchor-not-nil-of-commit-next-same
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (last-anchor (get-validator-state
                           val (commit-next val systate))))
    :enable (last-anchor
             commit-possiblep
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next
             active-committee-at-previous-round-when-at-round
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-orderedp-of-extend-blockchain
             certificate-list-orderedp-of-collect-anchors
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             evenp))

  (defruled last-anchor-present-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (last-anchor-present-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (last-anchor-present-p (commit-next val systate)))
    :enable (last-anchor-present-p
             last-anchor-present-p-necc
             last-anchor-not-nil-of-commit-next-diff
             last-anchor-not-nil-of-commit-next-same
             validator-state->last-of-commit-next))

  ;; all events:

  (defruled last-anchor-present-p-of-event-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (last-anchor-present-p systate)
                  (event-possiblep event systate))
             (last-anchor-present-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-present-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-even-p systate)
                (last-anchor-present-p systate))
           (last-anchor-present-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-present-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (last-anchor-present-p systate))
  :enable (system-state-reachablep
           last-anchor-present-p-when-init
           ordered-even-p-when-init
           last-blockchain-round-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-even-p from)
                   (last-anchor-present-p from))
              (last-anchor-present-p systate))
     :use (:instance
           last-anchor-present-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
