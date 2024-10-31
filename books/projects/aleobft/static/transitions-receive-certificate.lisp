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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-receive-certificate
  :parents (transitions)
  :short "Transitions for certificate receival."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('receive-certificate') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define receive-certificate-possiblep ((msg messagep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('receive-certificate') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message must be present in the network,
     and the destination must be a correct validator.
     The latter condition is an invariant of the system,
     but we state it explicitly here because
     we put no requirements on the system state passed to this function.
     That and other invariants are formulated and proved elsewhere."))
  (and (set::in msg (get-network-state systate))
       (set::in (message->destination msg)
                (correct-addresses systate)))
  ///

  (fty::deffixequiv receive-certificate-possiblep
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define receive-certificate-next ((msg messagep) (systate system-statep))
  :guard (receive-certificate-possiblep msg systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('receive-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate is added to the buffer of the destination validator.
     Recall that @(tsee receive-certificate-possiblep) requires
     the destination address to be of a correct validator.")
   (xdoc::p
    "The message is removed from the network.")
   (xdoc::p
    "Furthermore, if the validator has previously endorsed that certificate,
     the author-round pair is removed from the set of pairs,
     because the certificate is now in the buffer,
     and can be checked there in @(tsee signers-do-not-have-author+round-p).
     The set deletion has no effect if the set does not have the pair."))
  (b* (((certificate cert) (message->certificate msg))
       (dest (message->destination msg))
       (vstate (get-validator-state dest systate))
       (new-vstate
        (receive-certificate-next-val (message->certificate msg) vstate))
       (systate (update-validator-state dest new-vstate systate))
       (network (get-network-state systate))
       (new-network (set::delete msg network)))
    (update-network-state new-network systate))
  :guard-hints
  (("Goal" :in-theory (enable receive-certificate-possiblep
                              in-all-addresses-when-in-correct-addresses)))

  :prepwork
  ((define receive-certificate-next-val ((cert certificatep)
                                         (vstate validator-statep))
     :returns (new-vstate validator-statep)
     :parents nil
     (b* (((certificate cert) cert)
          (buffer (validator-state->buffer vstate))
          (new-buffer (set::insert cert buffer))
          (endorsed (validator-state->endorsed vstate))
          (new-endorsed (set::delete (make-address+pos
                                      :address cert.author
                                      :pos cert.round)
                                     endorsed)))
       (change-validator-state
        vstate
        :buffer new-buffer
        :endorsed new-endorsed))))

  ///

  (fty::deffixequiv receive-certificate-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (validator-state->round
                     (get-validator-state val
                                          (receive-certificate-next msg
                                                                    systate)))
                    (validator-state->round
                     (get-validator-state val systate))))
    :enable (receive-certificate-next-val
             receive-certificate-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->dag-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (receive-certificate-next msg
                                                                    systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable (receive-certificate-next-val
             receive-certificate-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->last-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (receive-certificate-next
                                           msg systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :enable (receive-certificate-possiblep
             receive-certificate-next-val
             get-validator-state-of-update-validator-state
             nfix))

  (defruled validator-state->blockchain-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (receive-certificate-next
                                           msg systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :enable (receive-certificate-possiblep
             receive-certificate-next-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->committed-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (receive-certificate-next
                                           msg systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :enable (receive-certificate-possiblep
             receive-certificate-next-val
             get-validator-state-of-update-validator-state)))
