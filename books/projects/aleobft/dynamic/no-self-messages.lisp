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

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ no-self-messages
  :parents (correctness)
  :short "Invariant that messages are never self-addressed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Messages come into existence only due to @('create-certificate') events.
     If the author is a correct validator,
     the certificate is broadcast to all the other correct validators,
     while it is immediately added to the author's DAG;
     the validator does not send a message to itself.
     If the author is a faulty validator,
     the certificate is broadcast to all the correct validators,
     and to no faulty validator;
     thus in particular the validator does not send the message to itself.
     Either way, messages are never self-addressed:
     the destination always differ from the sender,
     i.e. the certificate's author."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-noselfp ((msg messagep))
  :returns (yes/no booleanp)
  :short "Check that a message is not self-addressed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate's author, who is the sender,
     must differ from the destination, who is the recipient."))
  (not (equal (certificate->author (message->certificate msg))
              (message->destination msg)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-set-noselfp ((msgs message-setp))
  :returns (yes/no booleanp)
  :short "Check that all the messages in a set are not self-addressed."
  (or (set::emptyp msgs)
      (and (message-noselfp (set::head msgs))
           (message-set-noselfp (set::tail msgs))))

  ///

  (defrule message-set-noselfp-of-sfix
    (equal (message-set-noselfp (set::sfix msgs))
           (message-set-noselfp msgs))
    :induct t)

  (defruled message-set-noselfp-element
    (implies (and (message-set-noselfp msgs)
                  (set::in msg msgs))
             (message-noselfp msg))
    :induct t)

  (defruled message-set-noselfp-subset
    (implies (and (message-set-noselfp msgs)
                  (set::subset msgs0 msgs))
             (message-set-noselfp msgs0))
    :induct t
    :enable (set::subset
             message-set-noselfp-element))

  (defruled message-not-selfp-when-emptyp
    (implies (set::emptyp msgs)
             (message-set-noselfp msgs)))

  (defruled message-set-noselfp-of-insert
    (equal (message-set-noselfp (set::insert msg msgs))
           (and (message-noselfp msg)
                (message-set-noselfp msgs)))
    :induct (set::weak-insert-induction msg msgs)
    :enable message-set-noselfp-element)

  (defruled message-set-noselfp-of-union
    (equal (message-set-noselfp (set::union msgs1 msgs2))
           (and (message-set-noselfp msgs1)
                (message-set-noselfp msgs2)))
    :induct t
    :enable (set::union
             message-set-noselfp-of-insert))

  (defruled message-set-noselfp-of-delete
    (implies (message-set-noselfp msgs)
             (message-set-noselfp (set::delete msg msgs)))
    :enable message-set-noselfp-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define no-self-messages-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          all the messages in the network are not self-addressed."
  (message-set-noselfp (get-network-state systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled no-self-messages-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the network is empty in an initial state,
     the invariant trivially holds (there are no messages)."))
  (implies (system-initp systate)
           (no-self-messages-p systate))
  :enable (system-initp
           no-self-messages-p
           message-not-selfp-when-emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-self-messages-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Messages come into existence via @('create-certificate') events,
     precisely via the @(tsee make-certificate-messages) function.
     So we start by proving that this function
     never generates self-addresses.
     From this, the theorem for @('create-certificate') follows easily.")
   (xdoc::p
    "A @('receive-certificate') event removes one message from the network,
     so it preserves the invariant, which holds for all messages
     before and after the deletion.")
   (xdoc::p
    "All the other events do not change the network."))

  (defruled message-set-noselfp-of-make-certificate-messages
    (implies (and (address-setp dests)
                  (not (set::in (certificate->author cert) dests)))
             (message-set-noselfp (make-certificate-messages cert dests)))
    :induct t
    :enable (make-certificate-messages
             message-set-noselfp-of-insert
             message-noselfp))

  (defruled no-self-messages-p-of-create-certificate-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (create-certificate-next cert systate)))
    :enable (no-self-messages-p
             get-network-state-of-create-certificate-next
             message-set-noselfp-of-union
             message-set-noselfp-of-make-certificate-messages))

  (defruled no-self-messages-p-of-receive-certificate-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (receive-certificate-next msg systate)))
    :enable (no-self-messages-p
             get-network-state-of-receive-certificate-next
             message-set-noselfp-of-delete))

  (defruled no-self-messages-p-of-store-certificate-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (store-certificate-next val cert systate)))
    :enable (no-self-messages-p
             get-network-state-of-store-certificate-next))

  (defruled no-self-messages-p-of-advance-round-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (advance-round-next val systate)))
    :enable (no-self-messages-p
             get-network-state-of-advance-round-next))

  (defruled no-self-messages-p-of-commit-anchors-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (commit-anchors-next val systate)))
    :enable (no-self-messages-p
             get-network-state-of-commit-anchors-next))

  (defruled no-self-messages-p-of-timer-expires-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p
              (timer-expires-next val systate)))
    :enable (no-self-messages-p
             get-network-state-of-timer-expires-next))

  (defruled no-self-messages-p-of-event-next
    (implies (no-self-messages-p systate)
             (no-self-messages-p (event-next event systate)))
    :enable event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-self-messages-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled no-self-messages-p-of-events-next
    (implies (and (no-self-messages-p systate)
                  (events-possiblep events systate))
             (no-self-messages-p (events-next events systate)))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             no-self-messages-p-of-event-next))

  (defruled no-self-messages-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (no-self-messages-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (no-self-messages-p-when-init
             no-self-messages-p-of-events-next)))
