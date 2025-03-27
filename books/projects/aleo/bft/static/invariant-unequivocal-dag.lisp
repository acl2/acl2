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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-unequivocal-dag
  :parents (correctness)
  :short "Invariant that the certificates in each DAG
          have a unique combination of author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(see invariant-unequivocal-certificates),
     restricted to just the DAG of each validator,
     instead of all the certificates for the validator,
     which include the DAG, the buffer, and the messages in the network.
     That invariant needs to involve all those certificates
     in order to provide a sufficiently strong induction,
     since certificates are moved between DAGs, buffers, and network.
     However, it is the unequivocation in DAGs that is of interest
     in order to prove further correctness properties of the protocol.
     Thus, it is convenient to formulate and prove
     this more specialized invariant on DAGs only.")
   (xdoc::p
    "We formulate this invariant on DAGs
     using the @(tsee certificate-set-unequivocalp) predicate on DAGs,
     which will be used to prove some further properties elsewhere.
     (We could re-formulate @(see invariant-unequivocal-certificates)
     to use that predicate too, on all the certificates of a validator,
     but there is no real need for that.)")
   (xdoc::p
    "Also see the related @(see invariant-unequivocal-dags)
     (note the plural instead of the singular)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-unequivocal-dag-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          every DAG of every correct validator is such that
          if two certificates have the same author and round
          then they are the same certificate."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (certificate-set-unequivocalp
                    (validator-state->dag
                     (get-validator-state val systate)))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-unequivocal-dag-p-when-system-unequivocal-certificates-p
  :short "Proof of the specialized invariant from the general invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just show that this system-level invariant
     is implied by the more general one,
     which is easy to prove.
     There is no need to prove explicitly
     the establishment and preservation of the specialized invariant,
     as that has already been done for the more general one,
     and the specialized one is just implied by that."))
  (implies (system-unequivocal-certificates-p systate)
           (system-unequivocal-dag-p systate))
  :enable (system-unequivocal-dag-p
           certificate-set-unequivocalp
           certificates-for-validator)
  :use (:instance
        system-unequivocal-certificates-p-necc
        (cert1 (mv-nth
                0
                (certificate-set-unequivocalp-witness
                 (validator-state->dag
                  (get-validator-state
                   (system-unequivocal-dag-p-witness systate) systate)))))
        (cert2 (mv-nth
                1
                (certificate-set-unequivocalp-witness
                 (validator-state->dag
                  (get-validator-state
                   (system-unequivocal-dag-p-witness systate) systate)))))
        (val (system-unequivocal-dag-p-witness systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-unequivocal-dag-p-when-reachable
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
           (system-unequivocal-dag-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-unequivocal-dag-p-when-system-unequivocal-certificates-p
           system-unequivocal-certificates-p-when-reachable))
