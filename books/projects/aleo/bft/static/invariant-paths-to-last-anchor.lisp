; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-unequivocal-dag")
(include-book "invariant-dag-authors-are-validators")
(include-book "invariant-previous-in-dag")
(include-book "invariant-dag-previous-are-quorum")
(include-book "invariant-last-anchor-voters")
(include-book "invariant-last-is-even")
(include-book "property-paths-to-voted-anchor")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-paths-to-last-anchor
  :parents (correctness)
  :short "Invariant that all the certificates in a DAG
          at least two rounds after the last committed anchor
          have paths to that anchor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is one of the most important invariants in the protocol.
     The bulk of this is proved in @(see property-paths-to-voted-anchor),
     but here we lift it from DAGs to the whole system.")
   (xdoc::p
    "This invariant is implied by other already proved invariants,
     which establish the (suitably instantiated) hypothesis
     of @(tsee dag-all-path-to-p-holds),
     so that it can be applied to the DAG of each correct validator.
     See @(see property-paths-to-voted-anchor)
     for an explanation of this invariant/property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-paths-to-last-anchor-p ((systate system-statep))
  :guard (system-last-is-even-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator,
          if at least one anchor is committed,
          there is a path to the last committed anchor
          from every certificate in the DAG that is
          at least two rounds after that anchor."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* ((vstate (get-validator-state val systate))
                        (vals (all-addresses systate))
                        (anchor (last-anchor vstate vals)))
                     (implies anchor
                              (dag-all-path-to-p
                               anchor
                               (validator-state->dag vstate))))))
  :guard-hints
  (("Goal"
    :in-theory (enable nonempty-all-addresses-when-correct-validator
                       system-last-is-even-p-necc
                       in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-paths-to-last-anchor-p-when-other-invariants
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The other invariants serve to establish
     the hypotheses of @(tsee dag-all-path-to-p-holds),
     which we cannot quite use as a rewrite rule due to its free variables,
     so we use it in a @(':use') hints instead.
     We generally enable the @('-necc') rules of the other invariants,
     but some of them need @(':use') hints because they contain
     functions that do not appear in the subgoals (e.g. @(tsee quorum)),
     because the subgoals contain their expanded form instead;
     so, besides the @(':use') hints, we also enable those functions.")
   (xdoc::p
    "One hypothesis of @(tsee dag-all-path-to-p-holds)
     takes a little more work, because it uses @(tsee incoming),
     while @(tsee system-last-anchor-voters-p) uses @(tsee tally-leader-votes).
     We bridge the gap by proving, as a rewrite rule,
     an alternative definition of @(tsee validator-last-anchor-voters-p)
     in terms of @(tsee incoming)."))

  ;; Alternative definition of VALIDATOR-LAST-ANCHOR-VOTERS-P.

  (defrulel validator-last-anchor-voters-p-alt-def
    (implies (last-anchor vstate vals)
             (equal (validator-last-anchor-voters-p vstate
                                                    max-faulty
                                                    vals)
                    (>= (set::cardinality
                         (incoming (last-anchor vstate vals)
                                   (validator-state->dag vstate)))
                        (1+ max-faulty))))
    :enable (validator-last-anchor-voters-p
             last-anchor
             cardinality-of-incoming-to-tally-leader-votes
             certificate->author-of-cert-with-author+round
             certificate->round-of-cert-with-author+round))

  ;; Main theorem.

  (defrule system-paths-to-last-anchor-p-when-other-invariants
    (implies (and (system-unequivocal-dag-p systate)
                  (system-previous-in-dag-p systate)
                  (system-dag-previous-are-quorum-p systate)
                  (system-authors-are-validators-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-last-anchor-voters-p systate))
             (system-paths-to-last-anchor-p systate))
    :enable (system-paths-to-last-anchor-p
             system-unequivocal-dag-p-necc
             quorum
             number-validators
             nonempty-all-addresses-when-correct-validator
             dag-authors-are-validators-p
             anchorp
             system-previous-in-dag-p-necc
             system-last-is-even-p-necc
             certificate->author-of-last-anchor
             certificate->round-of-last-anchor
             last-anchor-in-dag)
    :use ((:instance dag-all-path-to-p-holds
                     (dag (validator-state->dag
                           (get-validator-state
                            (system-paths-to-last-anchor-p-witness systate)
                            systate)))
                     (anchor (last-anchor
                              (get-validator-state
                               (system-paths-to-last-anchor-p-witness systate)
                               systate)
                              (all-addresses systate)))
                     (vals (all-addresses systate))
                     (f (max-faulty systate)))
          (:instance system-dag-previous-are-quorum-p-necc
                     (val (system-paths-to-last-anchor-p-witness systate)))
          (:instance system-last-anchor-voters-p-necc
                     (val (system-paths-to-last-anchor-p-witness systate)))
          (:instance system-authors-are-validators-p-necc
                     (val (system-paths-to-last-anchor-p-witness systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-paths-to-last-anchor-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate)
                (fault-tolerant-p systate))
           (system-paths-to-last-anchor-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-paths-to-last-anchor-p-when-other-invariants
           system-unequivocal-dag-p-when-reachable
           system-previous-in-dag-p-when-reachable
           system-dag-previous-are-quorum-p-when-reachable
           system-authors-are-validators-p-when-reachable
           system-last-is-even-p-when-reachable
           system-last-anchor-present-p-when-reachable
           system-last-anchor-voters-p-when-reachable))
