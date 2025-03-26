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

(include-book "system-states")
(include-book "operations-certificate-retrieval")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-store-certificate
  :parents (transitions)
  :short "Transitions for certificate storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('store-certificate') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-certificate-possiblep ((cert certificatep)
                                     (val addressp)
                                     (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('store-certificate') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a certificate is received,
     the (correct) validator puts it into the buffer.
     From there, it is moved to the DAG
     when the DAG contains all the certificates
     referenced in the @('previous') component of the certificate.
     This is the reason for the buffer,
     as mentioned in @(tsee certificate):
     certificates may be received out of order,
     and so we need a staging area (the buffer)
     for certificates that cannot be added to the DAG yet.")
   (xdoc::p
    "The address @('val') of the validator indicated in the event
     must be a correct validator of the system;
     we do not model the internal state of faulty validators.
     The certificate must be in the buffer of the validator.
     If the certificate's round number is 1,
     there is no other requirement,
     because there are no previous certificates
     (this is an invariant of the system).
     Otherwise, we obtain the certificates in the DAG at the previous round,
     and we check that their authors contain
     the addresses in the @('previous') component of the certificate."))
  (b* (((certificate cert) cert)
       ((unless (set::in val (correct-addresses systate))) nil)
       (vstate (get-validator-state val systate))
       (buffer (validator-state->buffer vstate))
       ((unless (set::in cert buffer)) nil)
       ((when (equal cert.round 1)) t)
       (dag (validator-state->dag vstate))
       (all-previous-round-certs
        (certificates-with-round (1- cert.round) dag))
       (all-previous-round-authors
        (cert-set->author-set all-previous-round-certs))
       ((unless (set::subset cert.previous all-previous-round-authors)) nil))
    t)
  :guard-hints
  (("Goal" :in-theory (enable posp
                              in-all-addresses-when-in-correct-addresses)))

  ///

  (fty::deffixequiv store-certificate-possiblep
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-certificate-next ((cert certificatep)
                                (val addressp)
                                (systate system-statep))
  :guard (store-certificate-possiblep cert val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('store-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate is added to the DAG and removed from the buffer.")
   (xdoc::p
    "In addition, if the certificate's round number is
     greater than the current round number plus one,
     the current round number is fast-forwarded to
     the certificate's round number minus one.
     Further advancement to the certificate's round
     is handled in a separate event, namely @('advance-round').")
   (xdoc::p
    "The network is unaffected."))
  (b* ((vstate (get-validator-state val systate))
       (new-vstate (store-certificate-next-val cert vstate)))
    (update-validator-state val new-vstate systate))
  :guard-hints
  (("Goal" :in-theory (enable store-certificate-possiblep
                              in-all-addresses-when-in-correct-addresses)))

  :prepwork
  ((define store-certificate-next-val ((cert certificatep)
                                       (vstate validator-statep))
     :returns (new-vstate validator-statep)
     :parents nil
     (b* (((certificate cert) cert)
          (buffer (validator-state->buffer vstate))
          (dag (validator-state->dag vstate))
          (round (validator-state->round vstate))
          (new-buffer (set::delete cert buffer))
          (new-dag (set::insert cert dag))
          (new-round (if (> cert.round (1+ round))
                         (1- cert.round)
                       round)))
       (change-validator-state vstate
                               :buffer new-buffer
                               :dag new-dag
                               :round new-round))
     :guard-hints (("Goal" :in-theory (enable posp)))))

  ///

  (fty::deffixequiv store-certificate-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (validator-state->round
                     (get-validator-state val
                                          (store-certificate-next cert
                                                                  val1
                                                                  systate)))
                    (if (and (equal val val1)
                             (> (certificate->round cert)
                                (1+ (validator-state->round
                                     (get-validator-state val systate)))))
                        (1- (certificate->round cert))
                      (validator-state->round
                       (get-validator-state val systate)))))
    :enable (store-certificate-next-val
             store-certificate-possiblep
             get-validator-state-of-update-validator-state
             posp))

  (defruled validator-state->dag-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (store-certificate-next cert
                                                                  val1
                                                                  systate)))
                    (if (equal val val1)
                        (set::insert cert
                                     (validator-state->dag
                                      (get-validator-state val systate)))
                      (validator-state->dag
                       (get-validator-state val systate)))))
    :enable (store-certificate-next-val
             store-certificate-possiblep))

  (defruled validator-state->dag-subset-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (set::subset (validator-state->dag
                           (get-validator-state val systate))
                          (validator-state->dag
                           (get-validator-state
                            val (store-certificate-next cert val1 systate)))))
    :enable validator-state->dag-of-store-certificate-next
    :disable store-certificate-next)

  (defruled validator-state->dag-of-store-certificate-next-same
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (not (equal val val1)))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (store-certificate-next cert
                                                                  val1
                                                                  systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable validator-state->dag-of-store-certificate-next
    :disable store-certificate-next)

  (defruled validator-state->last-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (store-certificate-next
                                           cert val1 systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :enable (store-certificate-possiblep
             store-certificate-next-val
             get-validator-state-of-update-validator-state
             nfix))

  (defruled validator-state->blockchain-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (store-certificate-next
                                           cert val1 systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :enable (store-certificate-possiblep
             store-certificate-next-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->committed-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (store-certificate-next
                                           cert val1 systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :enable (store-certificate-possiblep
             store-certificate-next-val
             get-validator-state-of-update-validator-state)))
