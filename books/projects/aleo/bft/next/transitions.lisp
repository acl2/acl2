; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "events")
(include-book "elections")
(include-book "dags")
(include-book "anchors")
(include-book "blockchains")
(include-book "transitions-propose")
(include-book "transitions-endorse")
(include-book "transitions-augment")
(include-book "transitions-certify")
(include-book "transitions-accept")
(include-book "transitions-advance")
(include-book "transitions-commit")

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
    "Both the predicates and the functions are mostly executable;
     they only use a few constrained functions.
     This means that, given an initial state and a list of events,
     it is possible to simulate the execution of the system in ACL2
     by running each event in turn, starting with the initial state;
     all of this, assuming executable attachments for the constrained functions.
     The execution is not necessarily fast,
     because the definition of the labeled state transition system
     prioritizes clarity over efficiency."))
  :order-subtopics (elections
                    dags
                    anchors
                    blockchains
                    transitions-propose
                    transitions-endorse
                    transitions-augment
                    transitions-certify
                    transitions-accept
                    transitions-advance
                    transitions-commit
                    t)
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
   :propose (propose-possiblep event.proposal event.destinations systate)
   :endorse (endorse-possiblep event.proposal event.endorser systate)
   :augment (augment-possiblep event.proposal event.endorser systate)
   :certify (certify-possiblep event.certificate event.destinations systate)
   :accept (accept-possiblep event.validator event.certificate systate)
   :advance (advance-possiblep event.validator systate)
   :commit (commit-possiblep event.validator systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
   :propose (propose-next event.proposal event.destinations systate)
   :endorse (endorse-next event.proposal event.endorser systate)
   :augment (augment-next event.proposal event.endorser systate)
   :certify (certify-next event.certificate event.destinations systate)
   :accept (accept-next event.validator event.certificate systate)
   :advance (advance-next event.validator systate)
   :commit (commit-next event.validator systate))
  :guard-hints (("Goal" :in-theory (enable event-possiblep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define events-possiblep ((events event-listp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a sequence of events is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each event must be possible in the state that immediately precedes it,
     starting with the input @('systate') for the first state in @('events')
     (i.e. the @(tsee car), because we consider these events left to right),
     and using @(tsee event-next) to calculate the state
     for each successive event.
     This predicate returns @('t') on the empty list of events,
     since no events can always happen, so to speak."))
  (b* (((when (endp events)) t)
       ((unless (event-possiblep (car events) systate)) nil))
    (events-possiblep (cdr events) (event-next (car events) systate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define events-next ((events event-listp) (systate system-statep))
  :guard (events-possiblep events systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a sequence of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sequence of events must be possible,
     as expressed by @(tsee events-possiblep) in the guard.
     If the sequence is empty, we return the input state.
     Otherwise, we execute the events from left to right."))
  (b* (((when (endp events)) (system-state-fix systate))
       (systate (event-next (car events) systate)))
    (events-next (cdr events) systate))
  :guard-hints (("Goal" :in-theory (enable events-possiblep)))
  :hooks (:fix))
