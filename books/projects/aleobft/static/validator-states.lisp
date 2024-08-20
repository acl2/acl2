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

(include-book "blocks")
(include-book "certificates")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator-states
  :parents (states)
  :short "States of (correct) validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have internal states.
     For correct validators,
     i.e. the ones that follow the protocol,
     the internal states must contain certain information
     that is prescribed by the protocol,
     which we model here.
     For faulty validators,
     i.e. the ones that do not (always) follow the protcol,
     we do not need to model the internal state,
     because what matter in our model is only
     the effect that faulty validators may have on correct ones,
     via messages exchanged over the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod address+pos
  :short "Fixtype of pairs consisting of addresses and positive integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These pairs serve to record, in a validator state,
     which certificates have been endorsed
     but not received from the network yet.
     See the definition of validator states and of state transitions
     for details about the exact use of these pairs."))
  ((address address)
   (pos posp))
  :pred address+posp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset address+pos-set
  :short "Fixtype of sets of
          pairs consisting of addresses and positive integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined in @(tsee validator-state),
     a validator state includes one of this sets."))
  :elt-type address+pos
  :elementp-of-nil nil
  :pred address+pos-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum timer
  :short "Fixtype of timer states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our model does not represent real time,
     but it represents the state of timers,
     which may be either running or expired.
     Each validator has such a timer."))
  (:running ())
  (:expired ())
  :pred timerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod validator-state
  :short "Fixtype of states of a (correct) validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see validator-states),
     faulty validators are modeled with no internal state.
     This justifies the generic name @('validator-state') for this fixtype,
     as opposed to something like @('correct-validator-state').")
   (xdoc::p
    "We model the state of a correct validator as consisting of:")
   (xdoc::ol
    (xdoc::li
     "The current round number that the validator is at.")
    (xdoc::li
     "The DAG of certificates, modeled as a set.
      Invariants about the uniqueness of author and round combinations
      are stated later.")
    (xdoc::li
     "A buffer of certificates that the validator has received
      but has not been able to put into the DAG yet
      because some of its causal history is missing.
      Certificates move from the buffer to the DAG
      once their causal history is in the DAG.
      The buffer is modeled as a set,
      since ordering does not matter,
      given the way we formalize (later) certificate movement.")
    (xdoc::li
     "A set of pairs, each consisting of an address and a positive integer,
      which represents the author-round combinations
      for which the validator has endorsed proposals by signing them.
      When a (correct) validator receives a (valid) proposal,
      not only it signs the proposal and sends the signature back to the sender,
      but also it keeps track of which proposals it has signed
      to avoid signing different proposals
      for the same combination of author and round
      (such different proposals would come from a faulty validator):
      this is a critical property to guarantee non-equivocation.
      Here we model the exchange of proposals and signatures
      at a more abstract level,
      but we need to model this aspect to enforce that
      there will not be different certificates, in the system,
      with the same combination of author and round number.
      The use of this component of the state of a correct validator
      is explained in the definition of
      which events are possible and which new states they lead to.")
    (xdoc::li
     "The number of the last round at which
      this validator has committed an anchor.")
    (xdoc::li
     "The blockchain as seen by the validator.
      We model it as a list of blocks from right to left,
      i.e. the rightmost block is the oldest one
      and the leftmost block is the newest one.
      We leave the genesis block implicit:
      the rightmost block in our list is actually
      the block just after the genesis block.
      This blockchain state component of the validator should be redundant,
      calculable from the DAG state component
      and from information about the committed rounds.
      This is the case also because we do not model garbage collection.
      However, it is more convenient to explicate the blockchain
      in order to define the state transition system,
      and then to prove its redundancy as an invariant,
      since the proof may require a bit of work.")
    (xdoc::li
     "The set of all the certificates that have been committed so far,
      i.e. whose transactions have been included in the blockchain.
      These include not just the anchors,
      but also the nodes reachable from the anchors
      via the DAG edges.
      This state component serves to calculate the new certificates
      to be committed the next time anchors are committed,
      by computing the full causal history
      but removing the already committed certificates.
      This state component should be redundant,
      calculable from other state components,
      but for now we model it explicitly,
      because that is closer to the implementation.")
    (xdoc::li
     "The state of the timer; see @(tsee timer)."))
   (xdoc::p
    "The address of the validator, which never changes,
     is captured outside this fixtype,
     in the map from validator addresses to validator states
     in @(tsee system-state).")
   (xdoc::p
    "Invariants on validator states,
     such as the aforementioned uniqueness of
     author and round combinations in the DAG certificates,
     as well as others like disjointness of DAG and buffer,
     are formalized later."))
  ((round pos)
   (dag certificate-set)
   (buffer certificate-set)
   (endorsed address+pos-set)
   (last nat)
   (blockchain block-list)
   (committed certificate-set)
   (timer timer))
  :pred validator-statep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption validator-state-option
  validator-state
  :short "Fixtype of optional states of a (correct) validator."
  :pred validator-state-optionp)
