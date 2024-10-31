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

(include-book "properties-dags")
(include-book "invariant-unequivocal-dag")
(include-book "invariant-previous-in-dag")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-causal-histories
  :parents (correctness)
  :short "Invariant that the causal histories of existing certificates
          do not change as states change."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a transition invariant, instead of a state invariant.
     It says that if a certificate is in the DAG of a correct validator,
     then its causal history stays the same as the validator state changes.
     That is, causal histories are ``stable'' under state changes.")
   (xdoc::p
    "This lifts the theorem
     @(tsee certificate-causal-history-of-unequivocal-dag-superset)
     to (validators in) the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certificate-causal-history-of-event-next
  :short "Invariant that @(tsee certificate-causal-history)
          is stable under state changes."

  (defrule certificate-causal-history-of-create-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (create-certificate-possiblep cert systate)
                  (set::in cert1 (validator-state->dag
                                  (get-validator-state val systate))))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (create-certificate-next cert systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (system-previous-in-dag-p-necc
             validator-state->dag-of-create-certificate-next)
    :use ((:instance certificate-causal-history-of-unequivocal-dag-superset
                     (cert cert1)
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state
                             (certificate->author cert)
                             (create-certificate-next cert systate)))))
          (:instance system-unequivocal-dag-p-necc
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  (defrule certificate-causal-history-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (receive-certificate-next msg systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-receive-certificate-next)

  (defrule certificate-causal-history-of-store-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-previous-in-dag-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (set::in cert1 (validator-state->dag
                                  (get-validator-state val systate))))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (store-certificate-next cert val1 systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (system-previous-in-dag-p-necc
             validator-state->dag-of-store-certificate-next)
    :use ((:instance certificate-causal-history-of-unequivocal-dag-superset
                     (cert cert1)
                     (dag (validator-state->dag
                           (get-validator-state
                            val1
                            systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state
                             val1
                             (store-certificate-next cert val1 systate)))))
          (:instance system-unequivocal-dag-p-necc
                     (val val1)
                     (systate (store-certificate-next cert val1 systate)))))

  (defrule certificate-causal-history-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (advance-round-next val1 systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-advance-round-next)

  (defrule certificate-causal-history-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (commit-anchors-next val1 systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-commit-anchors-next)

  (defrule certificate-causal-history-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (timer-expires-next val1 systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-timer-expires-next)

  (defrule certificate-causal-history-of-event-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (set::in val (correct-addresses systate))
                  (event-possiblep event systate)
                  (set::in cert1 (validator-state->dag
                                  (get-validator-state val systate))))
             (equal (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state
                       val (event-next event systate))))
                    (certificate-causal-history
                     cert1
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (event-possiblep
             event-next)
    :disable (validator-state->dag-of-advance-round-next
              validator-state->dag-of-commit-anchors-next
              validator-state->dag-of-create-certificate-next
              validator-state->dag-of-receive-certificate-next
              validator-state->dag-of-store-certificate-next
              validator-state->dag-of-timer-expires-next)))
