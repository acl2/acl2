; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "library-extensions/top")
(include-book "static/top")
(include-book "dynamic/top")
(include-book "stake/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft
  :parents (acl2::projects)
  :short "Formal specification and correctness proofs of AleoBFT."
  :long
  (xdoc::topstring
   (xdoc::p
    "AleoBFT is the consensus protocol of the "
    (xdoc::ahref "https://aleo.org" "Aleo blockchain")
    ". AleoBFT is based on "
    (xdoc::ahref "https://arxiv.org/abs/2105.11827" "Narwhal")
    " and "
    (xdoc::ahref "https://arxiv.org/abs/2201.05677" "Bullshark")
    ", particuarly "
    (xdoc::ahref "https://arxiv.org/abs/2209.05633"
                 "partially synchronous Bullshark")
    ", which AleoBFT extends with dynamic committees with staking.
     AleoBFT is implemented in "
    (xdoc::ahref "https://github.com/AleoNet/snarkOS" "snarkOS")
    " (primarily) and "
    (xdoc::ahref "https://github.com/AleoNet/snarkVM" "snarkVM")
    " (for some functionality).")
   (xdoc::p
    "This directory contains various versions of
     formal specification and correctness proofs of AleoBFT.
     The subdirectory @('static') contains a version for
     AleoBFT with static committees and without stake,
     which is therefore similar to Bullshark,
     but with some differences unique to AleoBFT.
     The subdirectory @('dynamic') contains a version for
     AleoBFT with dynamic committees but without stake,
     which is a significant extension of the static version.
     The subdirectory @('stake') contains a version for
     AleoBFT with dynamic committees and with stake,
     which mainly extends the previous one with stake.
     We plan to add other subdirectories,
     for versions that cover additional aspects of AleoBFT,
     such as syncing.")
   (xdoc::p
    "In each version,
     we formally specify AleoBFT as a labeled state transition system:
     we define the possible states of the system (of all validators),
     the possible events that can take place in the system,
     and then we define, in essence, a ternary transition relation
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
    "We formulate the correctness properties of AleoBFT
     mainly as state invariants, which we show
     to hold in the initial states
     and to be preserved by state transitions."))
  :order-subtopics (library-extensions
                    aleobft-static::aleobft-static
                    aleobft-dynamic::aleobft-dynamic
                    aleobft-stake::aleobft-stake))
