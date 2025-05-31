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

(include-book "library-extensions/top")
(include-book "current/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft
  :parents (aleo::aleo)
  :short "Formal model and correctness proofs of AleoBFT."
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
    ", which AleoBFT extends with dynamic committees, staking, and syncing.
     AleoBFT is implemented in "
    (xdoc::ahref "https://github.com/AleoNet/snarkOS" "snarkOS")
    " (primarily) and "
    (xdoc::ahref "https://github.com/AleoNet/snarkVM" "snarkVM")
    " (for some functionality).")
   (xdoc::p
    "This directory contains
     a formal model and correctness proofs of AleoBFT.
     The model is an abstraction of AleoBFT
     that mainly captures the Bullshark aspects of the protocol,
     but with dynamic committees and with stake,
     which are significant extensions to Bullshark.
     The Narwhal aspects of AleoBFT
     are modeled only at an abstract level,
     similarly to the way that the Bullshark papers model
     the underlying DAG consensus layer.
     The level of abstraction of this model
     is about the same as the Bullshark papers.
     This model does not capture garbage collection or syncing.")
   (xdoc::p
    "The subdirectory @('next') contains
     an in-progress extension of the model and proofs,
     which will replace the current version when completed.
     (The files in @('next') are not included in the manual,
     so that they can use names overlapping with the current version.)
     This extension refines certificate creation,
     which in the current model is an atomic event,
     to be a multi-step process,
     with explicit creation and exchange of
     proposals, endorsements, and certificates;
     that is, the extensions models the Narwhal aspects of AleoBFT
     in more detail.
     Modeling syncing and garbage collection
     is not part of this @('next') extension;
     it is future work, along with other possible refinements of the model.")
   (xdoc::p
    "The proofs of correctness in both the current and next version
     mainly concern the safety property that blockchains do not fork.
     Proving other correctness properties is future work.")
   (xdoc::p
    "The current version of the model and proofs is
     the last one of a series of versions that we have developed.
     We started with a version with static committees without stake,
     which was therefore very similar to plain Bullshark.
     Then we made the significant extension to dynamic committees,
     initially without stake, and then with stake;
     adding stake was not a big extension.
     The @('next') version also has dynamic committees with stake,
     but has a more refined model of certificate creation (see above).
     Since each new version subsumes the previous ones as special cases,
     there is no need to keep the previous versions.")
   (xdoc::p
    "The current version corresponds to the contents of "
    (xdoc::ahref "https://arxiv.org/abs/2504.16853" "this arXiv paper")
    ".")
   (xdoc::p
    "We formally specify AleoBFT as a labeled state transition system:
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
    "We formulate the correctness properties of AleoBFT
     mainly as state invariants, which we show
     to hold in the initial states
     to be preserved by state transitions,
     and to hold in every state reachable from an initial state."))
  :order-subtopics (library-extensions
                    aleobft-definition-and-correctness))
