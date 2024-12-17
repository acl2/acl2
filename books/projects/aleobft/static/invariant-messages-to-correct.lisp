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

(defxdoc+ invariant-messages-to-correct
  :parents (correctness)
  :short "Invariant that messages are sent only to correct validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in the definition of
     the transitions for @('create-certificate') events,
     our model only generates messages to correct validators.
     There is no point in modeling messages to faulty validators,
     which can act arbitrarily anyways,
     regardless of which messages they receive or do not receive.")
   (xdoc::p
    "Thus, all the destination addresses that appear in messages
     are addresses of correct validators, never of faulty validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-to-correct-p ((msg messagep) (corrvals address-setp))
  :returns (yes/no booleanp)
  :short "Check that a message is addressed to a correct validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "To avoid passing the whole system state to this predicate
     (which is needed to obtain the addresses of the correct validators),
     we add the set of correct validator addresses as parameter,
     which will be suitably instantiated when this predicate
     is used in the definition of the system-level invariant."))
  (set::in (message->destination msg) corrvals))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-set-to-correct-p ((msgs message-setp) (corrvals address-setp))
  :returns (yes/no booleanp)
  :short "Check that all the messages in a set
          are addressed to corect validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee message-to-correct-p),
     we pass the addresses of correct validators to this predicate,
     which lifts that predicate to sets of messages."))
  (or (set::emptyp msgs)
      (and (message-to-correct-p (set::head msgs) corrvals)
           (message-set-to-correct-p (set::tail msgs) corrvals)))
  ///

  (defruled message-set-to-correct-p-element
    (implies (and (message-set-to-correct-p msgs corrvals)
                  (set::in msg msgs))
             (message-to-correct-p msg corrvals))
    :induct t)

  (defruled message-set-to-correct-p-subset
    (implies (and (message-set-to-correct-p msgs corrvals)
                  (set::subset msgs0 msgs))
             (message-set-to-correct-p msgs0 corrvals))
    :induct t
    :enable (set::subset
             message-set-to-correct-p-element))

  (defruled message-set-to-correct-of-delete
    (implies (message-set-to-correct-p msgs corrvals)
             (message-set-to-correct-p (set::delete msg msgs) corrvals))
    :enable message-set-to-correct-p-subset)

  (defruled message-set-to-correct-p-of-nil
    (message-set-to-correct-p nil corrvals))

  (defruled message-set-to-correct-p-of-insert
    (equal (message-set-to-correct-p (set::insert msg msgs) corrvals)
           (and (message-to-correct-p msg corrvals)
                (message-set-to-correct-p msgs corrvals)))
    :induct (set::weak-insert-induction msg msgs)
    :enable message-set-to-correct-p-element)

  (defruled message-set-to-correct-p-of-union
    (equal (message-set-to-correct-p (set::union msgs1 msgs2) corrvals)
           (and (message-set-to-correct-p msgs1 corrvals)
                (message-set-to-correct-p msgs2 corrvals)))
    :use (if-direction only-if-direction)
    :prep-lemmas
    ((defruled if-direction
       (implies (and (message-set-to-correct-p msgs1 corrvals)
                     (message-set-to-correct-p msgs2 corrvals))
                (message-set-to-correct-p (set::union msgs1 msgs2) corrvals))
       :induct t
       :enable (set::union
                message-set-to-correct-p-element
                message-set-to-correct-p-subset
                message-set-to-correct-p-of-insert))
     (defruled only-if-direction
       (implies (message-set-to-correct-p (set::union msgs1 msgs2) corrvals)
                (and (message-set-to-correct-p msgs1 corrvals)
                     (message-set-to-correct-p msgs2 corrvals)))
       :enable message-set-to-correct-p-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-messages-to-correct-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          all the messages in the network are addressed to correct validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('corrvals') parameter of @(tsee message-set-to-correct-p)
     is instantiated with the correct validator addresses in the system."))
  (message-set-to-correct-p (get-network-state systate)
                            (correct-addresses systate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-to-correct-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the network is empty in an initial state,
     the invariant trivially holds (there are no messages)."))
  (implies (system-state-initp systate)
           (system-messages-to-correct-p systate))
  :enable (system-state-initp
           system-messages-to-correct-p
           message-set-to-correct-p
           get-network-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled message-set-to-correct-p-of-messsages-for-certificate
  :short "Auxiliary property about message creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "New messages are created by @(tsee messages-for-certificate).
     The fact that this function creates only messages to correct validators
     can be reduced to the simpler fact that
     its @('dests') input is a subset of the correct validator addresses."))
  (implies (address-setp dests)
           (equal (message-set-to-correct-p
                   (messages-for-certificate cert dests)
                   corrvals)
                  (set::subset dests corrvals)))
  :induct t
  :enable (messages-for-certificate
           message-to-correct-p
           message-set-to-correct-p-of-nil
           message-set-to-correct-p-of-insert
           set::subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-to-correct-p-of-event-next
  :short "Preservation of the invariant by every event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from
     @(tsee message-set-to-correct-p-of-messsages-for-certificate)
     and from the definition of the transitions for each event.
     All the events
     other than @('create-certificate') and @('receive-certificate')
     do not modify the network, so preservation is trivial.
     A @('receive-certificate') event removes a message,
     so preservation is also easy.
     A @('create-certificate') event adds messages,
     but in a way that satisfies the subset condition
     that @(tsee message-set-to-correct-p) rewrites to
     via @(tsee message-set-to-correct-p-of-messsages-for-certificate)."))
  (implies (and (system-messages-to-correct-p systate)
                (event-possiblep event systate))
           (system-messages-to-correct-p (event-next event systate)))
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
           system-messages-to-correct-p
           message-set-to-correct-of-delete
           message-set-to-correct-p-of-union
           message-set-to-correct-p-of-messsages-for-certificate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-to-correct-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-messages-to-correct-p systate)
                (events-possiblep events systate))
           (system-messages-to-correct-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-messages-to-correct-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-messages-to-correct-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-messages-to-correct-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-messages-to-correct-p-when-system-state-initp
           system-messages-to-correct-p-of-events-next))
