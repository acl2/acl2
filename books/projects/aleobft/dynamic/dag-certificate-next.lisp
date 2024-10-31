; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "unequivocal-accepted-certificates-next")

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

(defsection certificate-with-author+round-of-next
  :short "Transition invariant for @(tsee certificate-with-author+round)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kinds of events that change the DAG
     are @('create-certificate') and @('receive-certificate').
     They do so by extending the DAG, adding a certificate to it.
     We have already proved the non-equivocation invariant,
     and here we need to use directly
     the fact that non-equivocation is preserved by the transitions:
     this tells us that the new DAG (the one with the added certificate)
     is unequivocal, which lets us use
     @('certificate-with-author+round-of-unequivocal-superset')
     to show that we retrieve the same certificate.")
   (xdoc::p
    "We need to assume a number of previously proved invariants,
     which are hypotheses for the preservation of non-equivocation,
     specifically of @(tsee unequivocal-accepted-certificates-p).")
   (xdoc::p
    "The other four kinds of events do not change the DAG,
     and thus the proof is easy."))

  (defruled certificate-with-author+round-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (create-certificate-possiblep cert systate)
                  (certificate-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (create-certificate-next cert systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (unequivocal-accepted-certificates-p-of-create-certificate-next
             validator-state->dag-of-create-certificate-next)
    :use ((:instance certificate-with-author+round-of-unequivocal-superset
                     (certs0 (validator-state->dag
                              (get-validator-state
                               (certificate->author cert)
                               systate)))
                     (certs (validator-state->dag
                             (get-validator-state
                              (certificate->author cert)
                              (create-certificate-next cert systate)))))
          (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  (defruled certificate-with-author+round-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (receive-certificate-next msg systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-receive-certificate-next)

  (defruled certificate-with-author+round-of-store-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate)
                  (certificate-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (store-certificate-next val1 cert systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :use (:instance lemma (val1 (address-fix val1)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (unequivocal-accepted-certificates-p systate)
                     (signer-records-p systate)
                     (committees-in-system-p systate)
                     (system-fault-tolerant-p systate)
                     (signer-quorum-p systate)
                     (same-committees-p systate)
                     (no-self-buffer-p systate)
                     (no-self-endorsed-p systate)
                     (same-owned-certificates-p systate)
                     (accepted-certificate-committee-p systate)
                     (set::in val (correct-addresses systate))
                     (addressp val1)
                     (store-certificate-possiblep val1 cert systate)
                     (certificate-with-author+round
                      author
                      round
                      (validator-state->dag
                       (get-validator-state val systate))))
                (equal (certificate-with-author+round
                        author
                        round
                        (validator-state->dag
                         (get-validator-state
                          val (store-certificate-next val1 cert systate))))
                       (certificate-with-author+round
                        author
                        round
                        (validator-state->dag
                         (get-validator-state val systate)))))
       :enable (unequivocal-accepted-certificates-p-of-store-certificate-next
                validator-state->dag-of-store-certificate-next)
       :use ((:instance certificate-with-author+round-of-unequivocal-superset
                        (certs0 (validator-state->dag
                                 (get-validator-state val1 systate)))
                        (certs (validator-state->dag
                                (get-validator-state
                                 val1
                                 (store-certificate-next
                                  val1 cert systate)))))
             (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                        (val val1)
                        (systate (store-certificate-next
                                  val1 cert systate)))))))

  (defruled certificate-with-author+round-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (advance-round-next val1 systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-advance-round-next)

  (defruled certificate-with-author+round-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (commit-anchors-next val1 systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-commit-anchors-next)

  (defruled certificate-with-author+round-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (timer-expires-next val1 systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable validator-state->dag-of-timer-expires-next)

  (defruled certificate-with-author+round-of-event-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (event-possiblep event systate)
                  (certificate-with-author+round
                   author
                   round
                   (validator-state->dag
                    (get-validator-state val systate))))
             (equal (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state
                       val (event-next event systate))))
                    (certificate-with-author+round
                     author
                     round
                     (validator-state->dag
                      (get-validator-state val systate)))))
    :enable (event-possiblep
             event-next
             certificate-with-author+round-of-create-certificate-next
             certificate-with-author+round-of-receive-certificate-next
             certificate-with-author+round-of-store-certificate-next
             certificate-with-author+round-of-advance-round-next
             certificate-with-author+round-of-commit-anchors-next
             certificate-with-author+round-of-timer-expires-next)))
