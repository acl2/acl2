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
(include-book "static/top")
(include-book "dynamic/top")
(include-book "stake/top")
(include-book "stake2/top")
(include-book "proposals/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft
  :parents (aleo::aleo)
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
     a formal specification and correctness proofs of AleoBFT:")
   (xdoc::ul
    (xdoc::li
     "The subdirectory @('static') contains a version for
      AleoBFT with static committees and without stake,
      which is therefore very similar to plain Bullshark,
      with some slight differences unique to AleoBFT.
      This is useful as a baseline,
      simpler to understand than the other versions;
      given its similarity to plain Bullshark,
      this can be regarded as providing
      formal correctness proofs for certain important aspects of Bullshark.
      This version models the Narwhal component of AleoBFT somewhat abstractly,
      with certificate creation as an atomic event
      instead of an exchange of proposals, signatures, and certificates.
      The main properties proved are
      the non-equivocation of certificates (for the Narwhal component)
      and the nonforking of blockchains (for the Bullshark component),
      with the latter building on the former,
      and with many other properties involved,
      such as the nonforking of committed anchor sequences.")
    (xdoc::li
     "The subdirectory @('dynamic') contains a version for
      AleoBFT with dynamic committees but without stake,
      which is a significant extension of the static version.
      The same two key properties of the static version are proved,
      namely certificate non-equivocation and blockchain nonforking,
      along with many other properties like anchor nonforking.
      But here they cannot be all proved
      in a simple sequential way as in the static version:
      besides blockchain nonforking needing certificate nonequivocation,
      the latter, which depends on committees,
      needs validators to agree on committees,
      which are calculated from blockchains,
      thus requiring blockchain nonforking.
      The circularity is inductively well-formed in the proofs,
      but the proofs are more complex than in the static version.")
    (xdoc::li
     "The subdirectory @('stake') contains a version for
      AleoBFT with dynamic committees and with stake,
      which mainly extends the version in @('dynamic') with stake,
      generalizing from validator counts to validator stakes.
      This extension from @('dynamic') to @('stake') is not as big as
      the extension from @('static') to @('dynamic'),
      but it nonetheless involves non-trivial generalizations.
      We also take the opportunity, in this version,
      to allow empty committees,
      which would likely deadlock the protocol,
      although we have not studied the situation in detail yet.
      We also take the opportunity, in this version,
      to move certain checks
      from certificate receiving events
      to certificate storing events,
      which makes certain aspects of the definitions and proofs simpler.")
    (xdoc::li
     "The subdirectory @('stake2') contains a version that is
      a slightly simplified variant of the version in @('stake').
      It omits buffers from validator states,
      and combines certificate receiving and storing events
      into single certificate acceptance events;
      this makes the model simpler
      without really affecting its expressiveness.
      Another simplification in this version is that
      the round advancement logic is much simpler,
      and there are no timeout events and no timers in validator states:
      there is just an event to advance a validator's round by one,
      which may nondeterministically take place any time, like the other events.
      While this does not affect the expressiveness of the model
      for the purpose of proving properties like blockchain nonforking
      (because the simplification makes more executions possible
      than in a model with more detailed and restrictive
      round advancement logic),
      it could affect the ability to prove certain other properties,
      e.g. because the system may deadlock more easily in this model.
      In addition to the simplifications just described,
      this version also eliminates some invariants
      that are not needed to prove blockchain nonforking.")
    (xdoc::li
     "The subdirectory @('proposals') contains a version that
      extends the @('stake2') version
      by explicitly modeling the exchange of proposals and signatures.
      Certificate creation is no longer an atomic event:
      there are separate events for
      creating and broadcasting proposal,
      endorsing proposals,
      augmenting proposals with endorsements,
      and finally creating and broadcasting certificates.
      The other events, namely
      certificate acceptance,
      round advancement, and
      anchor commitment,
      are similar to the @('stake2') version."))
   (xdoc::p
    "We plan to add other subdirectories
     for versions that cover additional aspects of AleoBFT,
     such as syncing.
     We may also extend the existing directories with more proofs,
     or we may revise and improve the existing definitions and proofs,
     also in order to update the model to reflect the latest AleoBFT
     as implemented in the aforementioned snarkOS and snarkVM.")
   (xdoc::p
    "In each version of our formal model and proofs,
     we formally specify AleoBFT as a labeled state transition system:
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
                    aleobft-static::aleobft-static
                    aleobft-dynamic::aleobft-dynamic
                    aleobft-stake::aleobft-stake
                    aleobft-stake2::aleobft-stake2
                    aleobft-proposals::aleobft-proposals))
