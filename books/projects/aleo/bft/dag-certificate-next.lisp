; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "unequivocal-dags-next")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-certificate-next
  :parents (correctness)
  :short "Invariant that retrieving an existing certificate from a DAG
          always returns the same result under all transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a transition invariant, instead of a state invariant.
     It says that if a certificate with a given author and round
     can be retrieved from the DAG of a correct validator,
     then it can be still retrieved, yielding the same result,
     as the validator changes state via events.
     That is, certificate retrieval is ``stable'' under state changes.")
   (xdoc::p
    "A critical assumption is that certificates are unequivocal.
     This transition invariant is based on
     properties of retrieval operations on unequivocal DAGs,
     which here we lift to (validators in) the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection cert-with-author+round-of-next
  :short "Transition invariant for @(tsee cert-with-author+round)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kinds of events that change the DAG
     are @('create') and @('accept').
     They do so by extending the DAG, adding a certificate to it.
     We have already proved the preservation of
     the DAG non-equivocation invariant,
     and here we need to use, directly,
     the fact that DAG non-equivocation is preserved by the transitions:
     this tells us that the new DAG (the one with the added certificate)
     is unequivocal, which lets us use
     @('cert-with-author+round-of-unequivocal-superset')
     to show that we retrieve the same certificate.")
   (xdoc::p
    "We need to assume a number of previously proved invariants,
     which are hypotheses for the preservation of DAG non-equivocation.")
   (xdoc::p
    "The other four kinds of events do not change the DAG,
     and thus the proof is easy."))

  (defruled cert-with-author+round-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (set::in val (correct-addresses systate))
                  (create-possiblep cert systate)
                  (cert-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (create-next cert systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-create-next
    :use ((:instance cert-with-author+round-of-unequivocal-superset
                     (certs0 (validator-state->dag
                              (get-validator-state
                               (certificate->author cert)
                               systate)))
                     (certs (validator-state->dag
                             (get-validator-state
                              (certificate->author cert)
                              (create-next cert systate)))))
          (:instance unequivocal-dags-p-necc-single
                     (val (certificate->author cert))
                     (systate (create-next cert systate)))))

  (defruled cert-with-author+round-of-accept-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (set::in val (correct-addresses systate))
                  (accept-possiblep msg systate)
                  (messagep msg)
                  (cert-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (accept-next msg systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (validator-state->dag-of-accept-next
             unequivocal-dags-p-of-accept-next)
    :use ((:instance cert-with-author+round-of-unequivocal-superset
                     (certs0 (validator-state->dag
                              (get-validator-state val systate)))
                     (certs (validator-state->dag
                             (get-validator-state
                              val
                              (accept-next msg systate)))))
          (:instance unequivocal-dags-p-necc-single
                     (systate (accept-next msg systate)))))

  (defruled cert-with-author+round-of-advance-next
    (implies (advance-possiblep val1 systate)
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (advance-next val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-advance-next)

  (defruled cert-with-author+round-of-commit-next
    (implies (commit-possiblep val1 systate)
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (commit-next val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-commit-next)

  (defruled cert-with-author+round-of-event-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (unequivocal-signed-certs-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (set::in val (correct-addresses systate))
                  (event-possiblep event systate)
                  (cert-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (event-next event systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (event-possiblep
             event-next
             cert-with-author+round-of-create-next
             cert-with-author+round-of-accept-next
             cert-with-author+round-of-advance-next
             cert-with-author+round-of-commit-next)))
