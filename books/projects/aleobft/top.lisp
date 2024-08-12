; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "static/top")

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
    "This directory contains works in progress towards
     a formal specification and correctness proofs of AleoBFT.
     The subdirectory @('static') contains
     a formal specification and correctness proofs
     of a version of AleoBFT with static committees and without stake,
     which is therefore similar to Bullshark,
     but with some differences unique to AleoBFT.
     We have also started another directory @('dynamic'),
     for a version of AleoBFT with dynamic committees.
     We plan to add other subdirectories,
     parallel to @('static') and @('dynamic'),
     for versions of the formal specification and correctness proofs
     that cover additional aspects of AleoBFT,
     such as stake and syncing.
     While this work is in progress,
     we may have these multiple subdirectories for different versions,
     but eventually we may converge to one version,
     in this directory (not in any subdirectory),
     which subsumes all the previous versions.
     The overall reason for tackling increasingly complex versions
     of the formal specification and correctness proofs of AleoBFT
     is to better manage the inherent complexity of the protocol.")
   (xdoc::p
    "We formally specify AleoBFT as a labeled state transition system:
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
  :order-subtopics (aleobft-static::aleobft-static))
