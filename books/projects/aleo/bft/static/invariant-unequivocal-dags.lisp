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

(include-book "operations-unequivocal-certificates")
(include-book "invariant-unequivocal-certificates")
(include-book "invariant-same-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-unequivocal-dags
  :parents (correctness)
  :short "Invariant that the certificates in two DAGs
          have a unique combination of author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "While @(see invariant-unequivocal-dag) (note the singular)
     concerns a single DAG of a validator,
     this invariant here (note the plural)
     concerns the DAGs of two validators.
     The two validators may of course be the same,
     so this invariant subsumes the other one,
     but it seems convenient to also have the other one explcitly.")
   (xdoc::p
    "We formulate this invariant on DAGs
     using the @(tsee certificate-sets-unequivocalp) predicate on DAG pairs,
     which will be used to prove some further properties elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-unequivocal-dags-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every pair of validators their DAGs are such that
          if two certificate from the DAGs (one per DAG)
          have the same author and round
          then they are the same certificate."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (certificate-sets-unequivocalp
                    (validator-state->dag
                     (get-validator-state val1 systate))
                    (validator-state->dag
                     (get-validator-state val2 systate)))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-unequivocal-dags-p-when-unequivocal-and-same
  :short "Proof of the invariant from
          the one about all the certificates of each validator
          and the one about the same certificates across validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a consequence of two existing invariants.
     Take two (not necessarily distinct) validators,
     and a certificate from the DAG of each,
     such that the two certificates have the same author and round.
     Then each certificate must be also in @(tsee certificates-for-validator)
     applied to the respective validator.
     But by @(tsee same-certificates-p),
     the two @(tsee certificates-for-validator) sets are the same;
     validators have the same certificates,
     taking into account DAGs, buffers, and network.
     Then we can use @(tsee system-unequivocal-certificates-p),
     for either validator, to show the equality of the certificates."))
  (implies (and (system-unequivocal-certificates-p systate)
                (same-certificates-p systate))
           (system-unequivocal-dags-p systate))
  :enable (system-unequivocal-dags-p
           certificate-sets-unequivocalp
           in-certificates-for-validator-when-in-dag
           set::expensive-rules)
  :use ((:instance
         system-unequivocal-certificates-p-necc
         (val (mv-nth 0 (system-unequivocal-dags-p-witness systate)))
         (cert1 (mv-nth
                 0
                 (certificate-sets-unequivocalp-witness
                  (validator-state->dag
                   (get-validator-state
                    (mv-nth 0
                            (system-unequivocal-dags-p-witness systate))
                    systate))
                  (validator-state->dag
                   (get-validator-state
                    (mv-nth 1
                            (system-unequivocal-dags-p-witness systate))
                    systate)))))
         (cert2 (mv-nth
                 1
                 (certificate-sets-unequivocalp-witness
                  (validator-state->dag
                   (get-validator-state
                    (mv-nth 0
                            (system-unequivocal-dags-p-witness systate))
                    systate))
                  (validator-state->dag
                   (get-validator-state
                    (mv-nth 1
                            (system-unequivocal-dags-p-witness systate))
                    systate))))))
        (:instance
         same-certificates-p-necc
         (val1 (mv-nth 0 (system-unequivocal-dags-p-witness systate)))
         (val2 (mv-nth 1 (system-unequivocal-dags-p-witness systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-unequivocal-dags-p-when-reachable
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
           (system-unequivocal-dags-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-unequivocal-dags-p-when-unequivocal-and-same
           system-unequivocal-certificates-p-when-reachable
           same-certificates-p-when-reachable))
