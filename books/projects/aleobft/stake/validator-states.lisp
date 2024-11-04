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

(acl2::set-waterfall-parallelism nil)

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
     because what matters in our model is only
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
     which certificates have been endorsed by the validator,
     but not received from the network yet.
     See @(tsee validator-state) and the definition of state transitions
     for details about the exact use of these pairs."))
  ((address address)
   (pos posp))
  :pred address+pos-p)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define address+pos-pairs-with-address ((addr addressp)
                                        (pairs address+pos-setp))
  :returns (pairs-with-addr address+pos-setp)
  :short "Retrieve, from a set of pairs of addresses and positive integers,
          the pairs with a given address."
  (b* (((when (set::emptyp pairs)) nil)
       (pair (set::head pairs)))
    (if (equal (address-fix addr) (address+pos->address pair))
        (set::insert (address+pos-fix pair)
                     (address+pos-pairs-with-address addr
                                                     (set::tail pairs)))
      (address+pos-pairs-with-address addr
                                      (set::tail pairs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv address+pos-pairs-with-address
    :args ((addr addressp)))

  (defrule address+pos-pairs-with-address-of-nil
    (equal (address+pos-pairs-with-address addr nil)
           nil))

  (defruled in-of-address+pos-pairs-with-address
    (implies (address+pos-setp pairs)
             (equal (set::in pair
                             (address+pos-pairs-with-address addr pairs))
                    (and (set::in pair pairs)
                         (equal (address+pos->address pair)
                                (address-fix addr)))))
    :induct t)

  (defruled address+pos-pairs-with-address-of-insert
    (implies (and (address+pos-p pair)
                  (address+pos-setp pairs))
             (equal (address+pos-pairs-with-address
                     addr (set::insert pair pairs))
                    (if (equal (address+pos->address pair)
                               (address-fix addr))
                        (set::insert pair
                                     (address+pos-pairs-with-address
                                      addr pairs))
                      (address+pos-pairs-with-address addr pairs))))
    :enable (in-of-address+pos-pairs-with-address
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable address+pos-pairs-with-address)

  (defruled address+pos-pairs-with-address-of-delete
    (implies (address+pos-setp pairs)
             (equal (address+pos-pairs-with-address
                     addr (set::delete pair pairs))
                    (set::delete pair
                                 (address+pos-pairs-with-address
                                  addr pairs))))
    :enable (in-of-address+pos-pairs-with-address
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable address+pos-pairs-with-address)

  (defruled author+round-pair-in-pairs-with-author
    (implies (and (address+pos-setp pairs)
                  (set::in (address+pos author round) pairs))
             (set::in (address+pos author round)
                      (address+pos-pairs-with-address author pairs)))
    :enable in-of-address+pos-pairs-with-address
    :disable address+pos-pairs-with-address)

  (defruled no-author+round-pair-if-no-pairs-with-author
    (implies (and (address+pos-setp pairs)
                  (equal (address+pos-pairs-with-address author pairs)
                         nil))
             (not (set::in (address+pos author round) pairs)))
    :use author+round-pair-in-pairs-with-author
    :disable address+pos-pairs-with-address))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum timer
  :short "Fixtype of timer states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our model does not represent real time,
     but it represents the state of timers,
     which may be either running or expired.
     Each validator has such a timer: see @(tsee validator-state)."))
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
     So this fixtype only models the state of correct validators.")
   (xdoc::p
    "We model the state of a correct validator as consisting of:")
   (xdoc::ol
    (xdoc::li
     "The current round number that the validator is at.")
    (xdoc::li
     "The DAG of certificates, modeled as a set.
      Invariants about the uniqueness of author and round combinations
      are stated and proved elsewhere.")
    (xdoc::li
     "A buffer of certificates that the validator has received
      but has not been able to put into the DAG yet
      because some of its predecessor certificates
      (identified by the @('previous') certificate component)
      are not in the DAG yet.
      Certificates move from the buffer to the DAG
      once their predecessors are in the DAG.
      This is in fact an important invariant, stated and proved elsewhere.
      The buffer is modeled as a set,
      since ordering does not matter,
      given the way we formalize certificate movement
      as non-deterministic choice.")
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
      at a more abstract level, not explicitly,
      but we still need to model this aspect to enforce that
      there will not be equivocal certificates,
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
      i.e. the rightmost block is the oldest/earliest one
      and the leftmost block is the newest/latest one.
      We leave the genesis block implicit:
      the rightmost block in our list is actually
      the block just after the genesis block.
      The blockchain is actually calculable from other state components,
      as proved elsewhere.
      However, the reasons (i.e. proof) of this redundancy are somewhat complex,
      and thus it is better to include the blockchain in the validator state,
      so that the state transitions can be defined in a more natural way.")
    (xdoc::li
     "The set of all the certificates that have been committed so far,
      i.e. whose transactions have been included in the blockchain.
      These include not just the anchors,
      but also the nodes reachable from the anchors via the DAG edges.
      This state component serves to calculate the new certificates
      to be committed the next time anchors are committed,
      by computing the full causal history
      but removing the already committed certificates.
      This is actually calculable from other state components,
      as proved elsewhere.
      However, for the same reason outlined above for the blockchain component,
      it is best to leave this component in the state,
      for a more natural definition of the state transitions.")
    (xdoc::li
     "The state of the timer; see @(tsee timer)."))
   (xdoc::p
    "The address of the validator, which never changes,
     is captured outside this fixtype,
     in the map from validator addresses to validator states
     that is in the system state.")
   (xdoc::p
    "There are many invariants on validator states,
     such as the ones mentioned above.
     These are stated and proved elsewhere."))
  ((round pos)
   (dag certificate-set)
   (buffer certificate-set)
   (endorsed address+pos-set)
   (last nat)
   (blockchain block-list)
   (committed certificate-set)
   (timer timer))
  :pred validator-statep)
