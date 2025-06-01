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

(include-book "states")
(include-book "events")
(include-book "initialization")
(include-book "transitions")
(include-book "reachability")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definition
  :parents (aleobft)
  :short "Definition of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model the AleoBFT protocol as a labeled state transition system,
     according to the standard definition of that notion in the literature:
     we define the possible states of the system,
     the possible events that can take place in the system,
     and then we define, in essence, a ternary transition relation,
     each of whose triples relates an old state, an event, and a new state;
     the events are the labels in this labeled state transition system.
     In general, not every event may happen in every state,
     which is reflected in the transition relation not having triples
     with those given old states and events.
     More precisely, we define our transition relation via
     a predicate and a function:
     the predicate says whether an event is possible in a state;
     the function says, for the events and states for which the predicate holds,
     what the new state is after the event.
     In general there are multiple possible events in every state,
     which makes the system nondeterministic;
     however, given one of these events,
     the next state is determined by old state and event
     (we achieve that by putting enough information in the event).")
   (xdoc::p
    "We model the protocol as a labeled state transition system,
     according to the standard definition of that notion in the literature.
     We define the possible states of the system,
     the possible events of the system,
     the possible initial states,
     and the possible transitions by which
     an event takes a state to a new state
     (the events `label' the transitions between states)."))
  :order-subtopics (states
                    events
                    initialization
                    transitions
                    reachability))
