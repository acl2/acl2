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

(include-book "states")
(include-book "events")
(include-book "initialization")
(include-book "operations")
(include-book "transitions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definition
  :parents (aleobft-static)
  :short "Definition of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
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
                    operations
                    transitions))
