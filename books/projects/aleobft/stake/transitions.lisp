; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "events")
(include-book "elections")
(include-book "dags")
(include-book "anchors")
(include-book "blockchains")
(include-book "transitions-create")
(include-book "transitions-receive")
(include-book "transitions-store")
(include-book "transitions-advance")

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
    "Both the predicates and the functions are executable.
     This means that, given an initial state and a list of events,
     it is possible to simulate the execution of the system in ACL2,
     by running each event in turn, starting with the initial state.
     The execution is not necessarily fast,
     because the definition of the labeled state transition system
     prioritizes clearity over efficiency."))
  :order-subtopics (elections
                    dags
                    anchors
                    blockchains
                    transitions-create
                    transitions-receive
                    transitions-store
                    transitions-advance
                    t)
  :default-parent t)
