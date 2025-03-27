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
(include-book "invariant-unequivocal-dags")
(include-book "invariant-dag-authors-are-validators")
(include-book "invariant-previous-in-dag")
(include-book "invariant-dag-previous-are-quorum")
(include-book "invariant-last-anchor-voters")
(include-book "invariant-last-is-even")
(include-book "property-paths-to-other-voted-anchor")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-paths-to-other-last-anchor
  :parents (correctness)
  :short "Invariant that all the certificate in a DAG
          at least two rounds after the last committed anchor
          of a possibly different DAG
          have paths to that anchor in the first DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a very fundamental and critical invariant of the protocol.
     It generalizes @(see invariant-paths-to-last-anchor),
     by considering two DAGs in two validators,
     which logically means that they could be the same DAG and validator or not.
     So in fact this invariant subsumes that invariant,
     but for now we prefer to keep that invariant around,
     also because it is a bit simpler to understand and prove.")
   (xdoc::p
    "This invariant is implied by other already proved invariants,
     which establish the (suitably instantiated) hypothesis
     of @(tsee dag-all-path-to-p-other-holds),
     so that it can be applied to the DAGs of the two validators.
     See @(see property-paths-to-other-voted-anchor)
     for an explanation of this invariant/property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-paths-to-other-last-anchor-p ((systate system-statep))
  :guard (system-last-is-even-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two (equal or different) correct validators,
          if at least one anchor is committed in one,
          the other has a path to the same anchor
          from every certificate at least two rounds after the anchor."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (b* ((vstate1 (get-validator-state val1 systate))
                        (vstate2 (get-validator-state val2 systate))
                        (vals (all-addresses systate))
                        (anchor (last-anchor vstate1 vals)))
                     (implies anchor
                              (dag-all-path-to-p
                               anchor
                               (validator-state->dag vstate2))))))
  :guard-hints
  (("Goal"
    :in-theory (enable nonempty-all-addresses-when-correct-validator
                       system-last-is-even-p-necc
                       in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-paths-to-other-last-anchor-p-when-other-invariants
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
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round))

  (defrule system-paths-to-other-last-anchor-p-when-other-invariants
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-previous-in-dag-p systate)
                  (system-dag-previous-are-quorum-p systate)
                  (system-authors-are-validators-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-last-anchor-voters-p systate))
             (system-paths-to-other-last-anchor-p systate))
    :enable (system-paths-to-other-last-anchor-p
             system-unequivocal-dag-p-necc
             system-unequivocal-dags-p-necc
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
    :use
    ((:instance
      dag-all-path-to-p-other-holds
      (dag1 (validator-state->dag
             (get-validator-state
              (mv-nth 0
                      (system-paths-to-other-last-anchor-p-witness systate))
              systate)))
      (dag2 (validator-state->dag
             (get-validator-state
              (mv-nth 1
                      (system-paths-to-other-last-anchor-p-witness systate))
              systate)))
      (anchor (last-anchor
               (get-validator-state
                (mv-nth 0
                        (system-paths-to-other-last-anchor-p-witness systate))
                systate)
               (all-addresses systate)))
      (vals (all-addresses systate))
      (f (max-faulty systate)))
     (:instance
      system-dag-previous-are-quorum-p-necc
      (val (mv-nth 1
                   (system-paths-to-other-last-anchor-p-witness systate))))
     (:instance
      system-last-anchor-voters-p-necc
      (val (mv-nth 0
                   (system-paths-to-other-last-anchor-p-witness systate))))
     (:instance
      system-authors-are-validators-p-necc
      (val (mv-nth 0
                   (system-paths-to-other-last-anchor-p-witness systate))))
     (:instance
      system-authors-are-validators-p-necc
      (val (mv-nth 1
                   (system-paths-to-other-last-anchor-p-witness systate)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-paths-to-other-last-anchor-p-when-reachable
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
           (system-paths-to-other-last-anchor-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-paths-to-other-last-anchor-p-when-other-invariants
           system-unequivocal-dag-p-when-reachable
           system-unequivocal-dags-p-when-reachable
           system-previous-in-dag-p-when-reachable
           system-dag-previous-are-quorum-p-when-reachable
           system-authors-are-validators-p-when-reachable
           system-last-is-even-p-when-reachable
           system-last-anchor-present-p-when-reachable
           system-last-anchor-voters-p-when-reachable))
