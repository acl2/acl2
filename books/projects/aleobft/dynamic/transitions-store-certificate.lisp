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

(include-book "system-states")

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
     caused by @('store-certificate') events.")
   (xdoc::p
    "A certificate storage event involves just one correct validator.
     Since we do not model the internal state of faulty validators,
     there is no point modeling events that change that internal state.")
   (xdoc::p
    "The event identifies a certificate,
     which is moved from the buffer to the DAG.
     But in order for this event to happen,
     all the previous certificates referenced by the certificate
     must be already in the DAG.")
   (xdoc::p
    "Furthermore, the storage of a certiicate may result in
     advancing the current round of the validator.
     The rationale is to update a validator that is left behind,
     but this aspect of the model needs further study
     (it does not affect safety properties like blockchain non-forking).")
   (xdoc::p
    "A certificate storage event does not involve the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-certificate-possiblep ((val addressp)
                                     (cert certificatep)
                                     (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate storage event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') and @('cert') inputs of this function are
     the address and certificate in the @('store-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "When a certificate is received,
     the (correct) validator puts it into the buffer.
     From there, it is moved to the DAG
     when the DAG contains all the certificates
     referenced in the @('previous') component of the certificate.
     This is the reason for the buffer:
     certificates may be received out of order,
     and so we need a staging area (the buffer)
     for certificates that cannot be added to the DAG yet.")
   (xdoc::p
    "The address @('val') of the validator indicated in the event
     must be a correct validator of the system;
     we do not model the internal state of faulty validators.
     The certificate must be in the buffer of the validator.
     If the certificate's round number is 1,
     there is no further requirement,
     because there are no previous certificates.
     Otherwise, we obtain the certificates in the DAG at the previous round,
     and we check that their authors contain
     the addresses in the @('previous') component of the certificate."))
  (b* (((certificate cert) cert)
       ((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate))
       ((unless (set::in (certificate-fix cert) vstate.buffer)) nil)
       ((when (equal cert.round 1)) t)
       (all-previous-round-certs
        (get-certificates-with-round (1- cert.round) vstate.dag))
       (all-previous-round-authors
        (certificate-set->author-set all-previous-round-certs))
       ((unless (set::subset cert.previous all-previous-round-authors)) nil))
    t)
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-certificate-next ((val addressp)
                                (cert certificatep)
                                (systate system-statep))
  :guard (store-certificate-possiblep val cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('store-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') and @('cert') inputs of this function are
     the address and certificate in the @('store-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "The certificate is added to the DAG and removed from the buffer.")
   (xdoc::p
    "In addition, if the certificate's round number is
     greater than the current round number plus one,
     the current round number is fast-forwarded to
     the certificate's round number minus one.
     The idea is that, if there are certificates,
     such as the one being stored in the DAG,
     which must necessarily come from another validator,
     which are two or more rounds ahead of the validator
     that is storing the certificate into the DAG,
     it indicates that this validator is behind.
     Note that, as required in @(tsee store-certificate-possiblep),
     the DAG must contain all the previous certificates,
     which must form a quorum because of the way certificates are created
     (it needs to be proved that there is agreement on the quorum,
     as we indeed plan to do);
     thus, if the validator's round is advanced to the certificate's round,
     the validator can immediately generate its own new certificate
     for that round in our model (or a proposal in a more detailed model).
     This aspect of the protocol needs further study,
     along with the logic for
     round advancement in @('advance-round') events.")
   (xdoc::p
    "If we advance the round, we also reset the timer,
     by setting it to `running'.
     Although the timer also needs further study,
     its purpose appears to be that a validator
     does not spend excessive time in a round,
     regardless of certificates received.
     In that case, it seems appropriate to reset the timer
     every time the round is advanced.")
   (xdoc::p
    "The network is unaffected."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) (get-validator-state val systate))
       (new-buffer (set::delete (certificate-fix cert) vstate.buffer))
       (new-dag (set::insert (certificate-fix cert) vstate.dag))
       ((mv new-round new-timer)
        (if (> cert.round (1+ vstate.round))
            (mv (1- cert.round) (timer-running))
          (mv vstate.round vstate.timer)))
       (new-vstate (change-validator-state vstate
                                           :buffer new-buffer
                                           :dag new-dag
                                           :round new-round
                                           :timer new-timer))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable store-certificate-possiblep
                                           posp)))
  :hooks (:fix))
