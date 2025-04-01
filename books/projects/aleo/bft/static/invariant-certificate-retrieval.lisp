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

(include-book "properties-certificate-retrieval")
(include-book "invariant-unequivocal-dag")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-certificate-retrieval
  :parents (correctness)
  :short "Invariant that the retrieval operations on existing certificates
          do not change results as states change."
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
    "This is based on some of the properties proved in
     @(see properties-certificate-retrieval),
     which here we lift to (validators in) the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-cert-with-author+round
  :short "Invariant that @(tsee cert-with-author+round)
          is stable under state changes."

  (defrule cert-with-author+round-of-create-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (fault-tolerant-p systate)
                  (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (create-certificate-possiblep cert systate)
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
                       val (create-certificate-next cert systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-create-certificate-next
    :use ((:instance cert-with-author+round-of-unequivocal-superset
                     (certs1 (validator-state->dag
                              (get-validator-state
                               (certificate->author cert)
                               systate)))
                     (certs2 (validator-state->dag
                              (get-validator-state
                               (certificate->author cert)
                               (create-certificate-next cert systate)))))
          (:instance system-unequivocal-dag-p-necc
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  (defrule cert-with-author+round-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (receive-certificate-next msg systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-receive-certificate-next)

  (defrule cert-with-author+round-of-store-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
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
                       val (store-certificate-next cert val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-store-certificate-next
    :use ((:instance cert-with-author+round-of-unequivocal-superset
                     (certs1 (validator-state->dag
                              (get-validator-state
                               val1
                               systate)))
                     (certs2 (validator-state->dag
                              (get-validator-state
                               val1
                               (store-certificate-next cert val1 systate)))))
          (:instance system-unequivocal-dag-p-necc
                     (val val1)
                     (systate (store-certificate-next cert val1 systate)))))

  (defrule cert-with-author+round-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (advance-round-next val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-advance-round-next)

  (defrule cert-with-author+round-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (commit-anchors-next val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-commit-anchors-next)

  (defrule cert-with-author+round-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (timer-expires-next val1 systate))))
                    (cert-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-timer-expires-next)

  (defrule cert-with-author+round-of-event-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (fault-tolerant-p systate)
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
             event-next)
    :disable (validator-state->dag-of-advance-round-next
              validator-state->dag-of-commit-anchors-next
              validator-state->dag-of-create-certificate-next
              validator-state->dag-of-receive-certificate-next
              validator-state->dag-of-store-certificate-next
              validator-state->dag-of-timer-expires-next)))
