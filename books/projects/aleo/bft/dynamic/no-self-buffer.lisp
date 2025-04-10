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

(include-book "no-self-messages")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ no-self-buffer
  :parents (correctness)
  :short "Invariant that buffers of correct validators
          never contain messages authored by themselves."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a consequence of the invariant @(see no-self-messages).
     A validator's buffer contains certificates
     obtained from messages in the network,
     which are never self-addresses as proved in that invariant.
     Thus, any message in the buffer or a validator
     is not self-authored, i.e. it is authored by another validator.
     Initially all buffers are empty, so this invariant holds."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk no-self-buffer-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          every certificaates in the buffer of a correct validator
          is not authored by that validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We express this by saying that
     retrieving from the buffer
     the certificates with the validator as author
     yields the empty set."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (equal (certs-with-author
                           val
                           (validator-state->buffer
                            (get-validator-state val systate)))
                          nil)))

  ///

  (fty::deffixequiv-sk no-self-buffer-p
    :args ((systate system-statep)))

  (defruled no-self-buffer-p-necc-fixing
    (implies (and (no-self-buffer-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (equal (certs-with-author
                     val
                     (validator-state->buffer
                      (get-validator-state val systate)))
                    nil))
    :use (:instance no-self-buffer-p-necc (val (address-fix val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled no-self-buffer-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "All buffers are initially empty, so the invariant trivially holds."))
  (implies (system-initp systate)
           (no-self-buffer-p systate))
  :enable (no-self-buffer-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-self-buffer-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that adds a certificate to a buffer
     is @('receive-certificate').
     But if we assume the already proved invariant
     that messages are not self-addressed,
     then we know that the newly added certificate
     is not signed by the validator by which it is received.")
   (xdoc::p
    "A @('store-certificate') event removes a certificate from a buffer,
     which thus preserves the invariant (on the remaining certificates).")
   (xdoc::p
    "The other kinds of events to do change any buffers."))

  (defruled no-self-buffer-p-of-create-certificate-next
    (implies (no-self-buffer-p systate)
             (no-self-buffer-p
              (create-certificate-next cert systate)))
    :enable (no-self-buffer-p
             no-self-buffer-p-necc
             validator-state->buffer-of-create-certificate-next))

  (defruled no-self-buffer-p-of-receive-certiicate-next
    (implies (and (no-self-buffer-p systate)
                  (no-self-messages-p systate)
                  (receive-certificate-possiblep msg systate))
             (no-self-buffer-p
              (receive-certificate-next msg systate)))
    :enable (no-self-buffer-p
             no-self-buffer-p-necc
             validator-state->buffer-of-receive-certificate-next
             certs-with-author-of-insert
             receive-certificate-possiblep
             no-self-messages-p
             message-noselfp)
    :use (:instance message-set-noselfp-element
                    (msgs (get-network-state systate))
                    (msg (message-fix msg))))

  (defruled no-self-buffer-p-of-store-certificate-next
    (implies (and (no-self-buffer-p systate)
                  (store-certificate-possiblep val cert systate))
             (no-self-buffer-p
              (store-certificate-next val cert systate)))
    :enable (no-self-buffer-p
             validator-state->buffer-of-store-certificate-next
             no-self-buffer-p-necc-fixing
             certs-with-author-of-delete))

  (defruled no-self-buffer-p-of-advance-round-next
    (implies (and (no-self-buffer-p systate)
                  (advance-round-possiblep val systate))
             (no-self-buffer-p
              (advance-round-next val systate)))
    :enable (validator-state->buffer-of-advance-round-next
             no-self-buffer-p
             no-self-buffer-p-necc))

  (defruled no-self-buffer-p-of-commit-anchors-next
    (implies (and (no-self-buffer-p systate)
                  (commit-anchors-possiblep val systate))
             (no-self-buffer-p
              (commit-anchors-next val systate)))
    :enable (validator-state->buffer-of-commit-anchors-next
             no-self-buffer-p
             no-self-buffer-p-necc))

  (defruled no-self-buffer-p-of-timer-expires-next
    (implies (and (no-self-buffer-p systate)
                  (timer-expires-possiblep val systate))
             (no-self-buffer-p
              (timer-expires-next val systate)))
    :enable (validator-state->buffer-of-timer-expires-next
             no-self-buffer-p
             no-self-buffer-p-necc))

  (defruled no-self-buffer-p-of-event-next
    (implies (and (no-self-buffer-p systate)
                  (no-self-messages-p systate)
                  (event-possiblep event systate))
             (no-self-buffer-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-self-buffer-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled no-self-buffer-p-of-events-next
    (implies (and (no-self-buffer-p systate)
                  (no-self-messages-p systate)
                  (events-possiblep events systate))
             (and (no-self-buffer-p (events-next events systate))
                  (no-self-messages-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             no-self-messages-p-of-event-next
             no-self-buffer-p-of-event-next))

  (defruled no-self-buffer-p-when-reachable
    (implies (and (system-statep systate)
                  (system-initp systate)
                  (events-possiblep events systate))
             (no-self-buffer-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (no-self-messages-p-when-init
             no-self-buffer-p-when-init
             no-self-buffer-p-of-events-next)))
