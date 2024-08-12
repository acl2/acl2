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

(include-book "events")
(include-book "transitions-create-certificate")
(include-book "transitions-receive-certificate")
(include-book "transitions-store-certificate")
(include-book "transitions-advance-round")
(include-book "transitions-commit-anchors")
(include-book "transitions-timer-expires")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions
  :parents (definition)
  :short "Transitions of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define predicates that say which events are possible in which states,
     and functions that say, for such combinations of events and states,
     which new states the events lead to.
     In other words, we define the transitions of
     the state transition system that models AleoBFT.")
   (xdoc::p
    "The functions from old system states to new system states
     include @('-val') companion functions
     that map old validator states to new validator states.
     This factoring facilitates formal proofs of invariants,
     so that validator-level invariants,
     which are part of system-level invariants,
     can be proved for the @('-val') function,
     making system-level invariant proofs more compositional."))
  :order-subtopics (transitions-create-certificate
                    transitions-receive-certificate
                    transitions-store-certificate
                    transitions-advance-round
                    transitions-commit-anchors
                    transitions-timer-expires)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define event-possiblep ((event eventp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if an event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the event, we use the appropriate predicate."))
  (event-case
   event
   :create-certificate (create-certificate-possiblep event.certificate systate)
   :receive-certificate (receive-certificate-possiblep event.message systate)
   :store-certificate (store-certificate-possiblep event.certificate
                                                   event.validator
                                                   systate)
   :advance-round (advance-round-possiblep event.validator systate)
   :commit-anchors (commit-anchors-possiblep event.validator systate)
   :timer-expires (timer-expires-possiblep event.validator systate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define event-next ((event eventp) (systate system-statep))
  :guard (event-possiblep event systate)
  :returns (new-systate system-statep)
  :short "New state resulting from an event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the event, we use the appropriate function."))
  (event-case
   event
   :create-certificate (create-certificate-next event.certificate systate)
   :receive-certificate (receive-certificate-next event.message systate)
   :store-certificate (store-certificate-next event.certificate
                                              event.validator
                                              systate)
   :advance-round (advance-round-next event.validator systate)
   :commit-anchors (commit-anchors-next event.validator systate)
   :timer-expires (timer-expires-next event.validator systate))
  :guard-hints (("Goal" :in-theory (enable event-possiblep))))
