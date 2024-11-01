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

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-no-self-messages
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
     and to no faulty validator (the modeling rationale is explained elsewhere);
     thus in particular the validator does not send the message to itself.
     Either way, messages are never self-addressed:
     the destination always differ from the sender,
     i.e. the certificate's author."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-not-self-p ((msg messagep))
  :returns (yes/no booleanp)
  :short "Check that a message is not self-addressed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate's author, who is the sender,
     must differ from the destination, who is the recipient."))
  (not (equal (certificate->author (message->certificate msg))
              (message->destination msg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-set-not-self-p ((msgs message-setp))
  :returns (yes/no booleanp)
  :short "Check that all the messages in a set are not self-addressed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove a number of structural properties
     that are used as rules in the invariant preservation proofs.")
   (xdoc::p
    "This predicate and accompanying theorems
     could be automatically generated from @(tsee message-not-self-p),
     with a suitable macro."))
  (or (set::emptyp msgs)
      (and (message-not-self-p (set::head msgs))
           (message-set-not-self-p (set::tail msgs))))
  ///

  (defrule message-set-not-self-p-of-sfix
    (equal (message-set-not-self-p (set::sfix msgs))
           (message-set-not-self-p msgs))
    :induct t)

  (defruled message-set-not-self-p-element
    (implies (and (message-set-not-self-p msgs)
                  (set::in msg msgs))
             (message-not-self-p msg))
    :induct t)

  (defruled message-set-not-self-p-subset
    (implies (and (message-set-not-self-p msgs)
                  (set::subset msgs0 msgs))
             (message-set-not-self-p msgs0))
    :induct t
    :enable (set::subset
             message-set-not-self-p-element))

  (defruled message-set-not-self-of-delete
    (implies (message-set-not-self-p msgs)
             (message-set-not-self-p (set::delete msg msgs)))
    :enable message-set-not-self-p-subset)

  (defruled message-set-not-self-p-of-insert
    (equal (message-set-not-self-p (set::insert msg msgs))
           (and (message-not-self-p msg)
                (message-set-not-self-p msgs)))
    :induct (set::weak-insert-induction msg msgs)
    :enable message-set-not-self-p-element)

  (defruled message-set-not-self-p-of-union
    (equal (message-set-not-self-p (set::union msgs1 msgs2))
           (and (message-set-not-self-p msgs1)
                (message-set-not-self-p msgs2)))
    :induct t
    :enable (set::union
             message-set-not-self-p-of-insert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-messages-not-self-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          all the messages in the network are not self-addressed."
  (message-set-not-self-p (get-network-state systate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-not-self-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the network is empty in an initial state,
     the invariant trivially holds (there are no messages)."))
  (implies (system-state-initp systate)
           (system-messages-not-self-p systate))
  :enable (system-state-initp
           system-messages-not-self-p
           message-set-not-self-p
           get-network-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled message-set-not-self-p-of-messages-for-certificates
  :short "Auxiliary property about message creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Messages are created by @(tsee messages-for-certificate).
     So long as the author is none of the destinations,
     the messages are not self-addressed.
     That hypothesis is established in the proof of
     @(tsee system-messages-not-self-p-of-event-next)."))
  (implies (and (address-setp dests)
                (not (set::in (certificate->author cert) dests)))
           (message-set-not-self-p (messages-for-certificate cert dests)))
  :induct t
  :enable (messages-for-certificate
           message-set-not-self-p
           message-not-self-p
           message-set-not-self-p-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-not-self-p-of-event-next
  :short "Preservation of the invariant by every event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from
     @(tsee message-set-not-self-p-of-messages-for-certificates)
     and from the definition of the transitions for each event.
     All the events
     other than @('create-certificate') and @('receive-certificate')
     do not modify the network, so preservation is trivial.
     A @('receive-certificate') event removes a message,
     so preservation is also easy.
     A @('create-certificate') event adds messages,
     but in a way that establishes the hypothesis of
     @(tsee message-set-not-self-p-of-messages-for-certificates)."))
  (implies (and (system-messages-not-self-p systate)
                (event-possiblep event systate))
           (system-messages-not-self-p (event-next event systate)))
  :enable (event-possiblep
           event-next
           create-certificate-possiblep
           create-certificate-next
           receive-certificate-possiblep
           receive-certificate-next
           store-certificate-possiblep
           store-certificate-next
           advance-round-possiblep
           advance-round-next
           commit-anchors-possiblep
           commit-anchors-next
           timer-expires-possiblep
           timer-expires-next
           system-messages-not-self-p
           message-set-not-self-p-of-union
           message-set-not-self-p-of-messages-for-certificates))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-not-self-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-messages-not-self-p systate)
                (events-possiblep events systate))
           (system-messages-not-self-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-messages-not-self-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-not-self-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-messages-not-self-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-messages-not-self-p-when-system-state-initp
           system-messages-not-self-p-of-events-next))
