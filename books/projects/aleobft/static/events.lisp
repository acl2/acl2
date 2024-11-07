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

(include-book "messages")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ events
  :parents (definition)
  :short "Events of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a fixtype for the events
     of the state transition system that models AleoBFT.
     In the framework of labeled state transition systems,
     these events are the labels."))
  :order-subtopics (messages
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum event
  :short "Fixtype of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The system evolves its state (see @(tsee system-state))
     in response to the following events:")
   (xdoc::ol
    (xdoc::li
     "A validator creates a new certificate.
      Note that the certificate includes the author,
      i.e. it indicates the validator.
      This adds the certificate to the DAG of the validator,
      and broadcasts the certificate to all the correct validators
      (the latter point is discussed in more detail later).")
    (xdoc::li
     "A validator receives a certificate,
      from a message in the network,
      which is removed from the network
      and added to the buffer of the validator.")
    (xdoc::li
     "A validator stores a certificate into the DAG,
      moving it there from the buffer.")
    (xdoc::li
     "A validator advances its round.")
    (xdoc::li
     "A validator commits anchors.")
    (xdoc::li
     "A validator's timer expires."))
   (xdoc::p
    "Each event can only happen in certain states,
     e.g. a validator can generate a new certificate
     only if it has a quorum of preceding certificates in the DAG.
     If an event is possible, then the next state is uniquely determined
     by the current state and the event."))
  (:create-certificate ((certificate certificate)))
  (:receive-certificate ((message message)))
  (:store-certificate ((certificate certificate)
                       (validator address)))
  (:advance-round ((validator address)))
  (:commit-anchors ((validator address)))
  (:timer-expires ((validator address)))
  :pred eventp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist event-list
  :short "Fixtype of lists of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Events are defined in @(tsee event)."))
  :elt-type event
  :true-listp t
  :elementp-of-nil nil
  :pred event-listp
  :prepwork ((local (in-theory (enable nfix)))))
