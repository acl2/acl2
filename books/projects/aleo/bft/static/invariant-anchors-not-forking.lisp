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

(include-book "operations-anchors")
(include-book "properties-anchors")
(include-book "properties-anchors-extension")
(include-book "invariant-last-is-even")
(include-book "invariant-last-anchor-present")
(include-book "invariant-paths-to-other-last-anchor")

(include-book "../library-extensions/lists-noforkp")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-anchors-not-forking
  :parents (correctness)
  :short "Invariant that committed anchors do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is most of what is needed to show the non-forking of blockchains,
     given that the blockchain in each validator
     is fully determined by the anchors it has committed so far.")
   (xdoc::p
    "This invariant is implied by other already proved invariants.
     Consider two validators, each with some committed anchors
     (if any validator has no committed anchors yet,
     the two anchor sequences clearly cannot fork,
     because the empty list is a prefix of any list).
     If their last committed round is the same,
     it means that their last committed anchor is the same,
     and thus collecting all the anchors starting from that one
     results in the same list of anchors,
     because of @(tsee collect-all-anchors-of-unequivocal-dags).
     If instead the two last committed rounds differ,
     one must be greater than the other.
     But since the smaller one has at least @($F+1$) votes,
     we use @(see invariant-paths-to-other-last-anchor)
     to derive that the anchor at the larger round
     has a path to the same anchor, which must be also in the second DAG
     (the one with the larger last committed round).
     Then we use @(see properties-anchors-extension)
     to conclude that the longer list of anchors
     is an extension of the shorter list of anchors.
     In summary, anchor sequences never fork."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-anchors-nofork-p ((systate system-statep))
  :guard (and (not (set::emptyp (all-addresses systate)))
              (system-last-is-even-p systate)
              (system-last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two correct validators in the system,
          their sequences of committed anchor do not fork."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (lists-noforkp
                    (committed-anchors (get-validator-state val1 systate)
                                       (all-addresses systate))
                    (committed-anchors (get-validator-state val2 systate)
                                       (all-addresses systate)))))
  :guard-hints
  (("Goal" :in-theory (enable* system-last-is-even-p-necc
                               system-last-anchor-present-p-necc
                               set::expensive-rules
                               in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-anchors-nofork-p-when-other-invariants
  :short "Proof of the invariant from other invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we prove local lemmas for two generic validators,
     considering all the possible cases
     (which need slightly different proofs).
     Then we prove a local lemma for the general case,
     easily from the ones for the different cases.
     Finally we prove the non-local theorem about the invariant,
     which follows easily from the lemma."))

  ;; If the first validator has not committed any anchors yet,
  ;; the proof is easy because any list (in the second validator) extends NIL.

  (defruledl case-last1-0
    (implies (equal (validator-state->last
                     (get-validator-state val1 systate))
                    0)
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :enable committed-anchors)

  ;; The case in which the second validator has not committed any anchor
  ;; is symmetric with respect to the previous one.

  (defruledl case-last2-0
    (implies (equal (validator-state->last
                     (get-validator-state val2 systate))
                    0)
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :enable committed-anchors)

  ;; If the two validators have the same last committed round,
  ;; their last anchor must be the same (via SAME-LAST-ANCHOR-IF-SAME-LAST),
  ;; and so we can use the theorem about COLLECT-ALL-ANCHORS
  ;; returning consistent results across two unequivocal DAGs
  ;; starting from the same anchor present in both DAGs.
  ;; We do not even need the hypothesis that
  ;; the common last round is not 0,
  ;; but everything would still work if we included that hypothesis,
  ;; since the 0 case has been covered by preceding theorems.

  (defruledl case-last1-equal-last2
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate))
                  (equal (validator-state->last
                          (get-validator-state val1 systate))
                         (validator-state->last
                          (get-validator-state val2 systate))))
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :enable (committed-anchors
             system-unequivocal-dag-p-necc
             system-unequivocal-dags-p-necc
             system-previous-in-dag-p-necc
             system-last-anchor-present-p-necc
             last-anchor-in-dag)
    :use ((:instance collect-all-anchors-of-unequivocal-dags
                     (dag1 (validator-state->dag
                            (get-validator-state val1 systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state val2 systate)))
                     (last-anchor (last-anchor
                                   (get-validator-state val1 systate)
                                   (all-addresses systate)))
                     (vals (all-addresses systate)))
          (:instance same-last-anchor-if-same-last
                     (vstate1 (get-validator-state val1 systate))
                     (vstate2 (get-validator-state val2 systate))
                     (vals (all-addresses systate)))))

  ;; If both validators have committed anchors
  ;; and the second validator is ahead of the first one,
  ;; we use COLLECT-ALL-ANCHORS-TO-APPEND-OF-COLLECT-ANCHORS-OTHER
  ;; to replace the longer anchor sequence
  ;; with the APPEND of the shorter one and something else
  ;; (that something else being the anchors in between),
  ;; and then a rule about LISTS-NOFORKP and APPEND fires.

  (defruledl case-last1-before-last2
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-previous-in-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-paths-to-other-last-anchor-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate))
                  (not (equal (validator-state->last
                               (get-validator-state val1 systate))
                              0))
                  (> (validator-state->last
                      (get-validator-state val2 systate))
                     (validator-state->last
                      (get-validator-state val1 systate))))
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :enable (system-unequivocal-dag-p-necc
             system-unequivocal-dags-p-necc
             system-previous-in-dag-p-necc
             system-last-is-even-p-necc
             system-last-anchor-present-p-necc
             system-paths-to-other-last-anchor-p-necc
             committed-anchors
             certificate->round-of-last-anchor
             anchorp-of-last-anchor)
    :use ((:instance collect-all-anchors-to-append-of-collect-anchors-other
                     (dag1 (validator-state->dag
                            (get-validator-state val1 systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state val2 systate)))
                     (vals (all-addresses systate))
                     (anchor1 (last-anchor
                               (get-validator-state val1 systate)
                               (all-addresses systate)))
                     (anchor2 (last-anchor
                               (get-validator-state val2 systate)
                               (all-addresses systate))))))

  ;; If both validators have committed anchors
  ;; and the first one is ahead of the second one,
  ;; things are symmetric with respect to the previous theorem,
  ;; which in fact we use to prove this one, swapping the validators' roles.

  (defruledl case-last2-before-last1
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-previous-in-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-paths-to-other-last-anchor-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate))
                  (not (equal (validator-state->last
                               (get-validator-state val2 systate))
                              0))
                  (> (validator-state->last
                      (get-validator-state val1 systate))
                     (validator-state->last
                      (get-validator-state val2 systate))))
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :use (:instance case-last1-before-last2
                    (val1 val2)
                    (val2 val1)))

  ;; Given that we have covered all the possible cases above,
  ;; we can prove the non-forking in general.
  ;; Just enabling the lemmas above does not get the proof through,
  ;; not even after splitting into cases via :CASES.
  ;; So we just use a :USE hints,
  ;; which is in fact as compact as an :ENABLE hint.

  (defrulel committed-anchors-nofork-p-holds
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-previous-in-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-paths-to-other-last-anchor-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate)))
             (lists-noforkp
              (committed-anchors (get-validator-state val1 systate)
                                 (all-addresses systate))
              (committed-anchors (get-validator-state val2 systate)
                                 (all-addresses systate))))
    :use (case-last1-0
          case-last2-0
          case-last1-equal-last2
          case-last1-before-last2
          case-last2-before-last1))

  ;; The previous theorem covers generic validators,
  ;; and so our main theorem easily follows from it.

  (defrule system-anchors-nofork-p-when-other-invariants
    (implies (and (system-unequivocal-dag-p systate)
                  (system-unequivocal-dags-p systate)
                  (system-previous-in-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-paths-to-other-last-anchor-p systate))
             (system-anchors-nofork-p systate))
    :enable system-anchors-nofork-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-anchors-nofork-p-when-reachable
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
           (system-anchors-nofork-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-anchors-nofork-p-when-other-invariants
           system-unequivocal-dag-p-when-reachable
           system-unequivocal-dags-p-when-reachable
           system-previous-in-dag-p-when-reachable
           system-last-is-even-p-when-reachable
           system-last-anchor-present-p-when-reachable
           system-paths-to-other-last-anchor-p-when-reachable))
