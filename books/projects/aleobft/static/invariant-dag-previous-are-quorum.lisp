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

(include-book "operations-dags-additional")
(include-book "invariant-previous-are-quorum")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-dag-previous-are-quorum
  :parents (correctness)
  :short "Invariant that
          the previous certificates of every certificate in every DAG
          form a quorum if the round is not 1, and there are none in round 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(see invariant-previous-are-quorum),
     which applies to all certificates in the system;
     the specialization only applies to DAGs.
     This specialized invariant is formulated in a way
     that is useful to prove further properties.")
   (xdoc::p
    "This specialized invariant is expressed
     in terms of the @(tsee dag-previous-are-quorum-p) predicate,
     which is used in further proofs of correctness properties."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-dag-previous-are-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the number of previous certificate references
          of every certificate of every validator's DAG
          is equal to the quorum number if the round number is not 1,
          or to 0 if the round number is 1."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-previous-are-quorum-p
                    (validator-state->dag
                     (get-validator-state val systate))
                    (quorum systate))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-dag-previous-are-quorum-p-when-all-previous-are-quorum
  :short "Proof of the specialized invariant from the general invariant."
  (implies (system-previous-are-quorum-p systate)
           (system-dag-previous-are-quorum-p systate))
  :enable (system-dag-previous-are-quorum-p
           dag-previous-are-quorum-p
           in-certificates-for-validator-when-in-dag
           system-previous-are-quorum-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-dag-previous-are-quorum-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-dag-previous-are-quorum-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-dag-previous-are-quorum-p-when-all-previous-are-quorum
           system-previous-are-quorum-p-when-reachable))
