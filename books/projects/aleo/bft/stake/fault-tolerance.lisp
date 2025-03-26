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

(include-book "transitions")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ fault-tolerance
  :parents (correctness)
  :short "Fault tolerance."
  :long
  (xdoc::topstring
   (xdoc::p
    "In typical BFT systems, which have fixed sets of validators,
     the notion of fault tolerance applies to the system as a whole,
     based on the (fixed) number of correct and faulty validators:
     the system is fault-tolerant if the actual number of faulty validators
     does not exceed @($f$), which is calculated from the total @($n$),
     as formalized in @(tsee max-faulty-for-total)
     (applied to numbers of validators instead of stake).
     With dynamic committees with stake, the notion applies to
     every committee that arises during the execution of the protocol,
     in terms of stake instead of numbers of validators.
     It has to be an assumption on every such committee:
     it cannot be checked by validators,
     who do not know which validator is correct vs. faulty.")
   (xdoc::p
    "Here we formalize this notion for committees,
     which is then used as a hypothesis for
     certain correctness theorems of our formal development."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-correct-members ((commtt committeep) (systate system-statep))
  :returns (addresses address-setp)
  :short "Addresses of the correct validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "Whether a validator is correct or not
     depends on whether the map in the system state
     includes the validator's address as a key.
     Thus, we need the system state, besides the committee,
     to calculate this set of addresses of correct validators in the committee,
     which we do by intersecting the committee's addresses
     with the addressess of all the correct validators in the system.")
   (xdoc::p
    "Since, as proved in the definition of the system state transitions,
     the correctness vs. faultiness of validators never changes
     (expressed as the preservation of @(tsee correct-addresses)),
     it follows that, given a committee,
     the result of this ACL2 function does not change
     as the system state evolves,
     which we prove here."))
  (set::intersect (committee-members commtt)
                  (correct-addresses systate))
  :hooks (:fix)

  ///

  (defrule committee-correct-members-subset-committee-members
    (set::subset (committee-correct-members commtt systate)
                 (committee-members commtt)))

  (defret committee-correct-members-of-create-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :fn create-next)

  (defret committee-correct-members-of-receive-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (receive-possiblep msg systate)
    :fn receive-next)

  (defret committee-correct-members-of-store-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (store-possiblep val cert systate)
    :fn store-next)

  (defret committee-correct-members-of-advance-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next)

  (defret committee-correct-members-of-commit-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (commit-possiblep val systate)
    :fn commit-next)

  (defret committee-correct-members-of-timeout-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (timeout-possiblep val systate)
    :fn timeout-next)

  (defret committee-correct-members-of-event-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (event-possiblep event systate)
    :fn event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-faulty-members ((commtt committeep) (systate system-statep))
  :returns (addresses address-setp)
  :short "Addresses of the faulty validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the difference between
     all the validators in the committee
     and the correct ones."))
  (set::difference (committee-members commtt)
                   (correct-addresses systate))
  :hooks (:fix)

  ///

  (defrule committee-faulty-members-subset-committee-members
    (set::subset (committee-faulty-members commtt systate)
                 (committee-members commtt)))

  (defret committee-faulty-members-of-create-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :fn create-next)

  (defret committee-faulty-members-of-receive-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (receive-possiblep msg systate)
    :fn receive-next)

  (defret committee-faulty-members-of-store-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (store-possiblep val cert systate)
    :fn store-next)

  (defret committee-faulty-members-of-advance-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next)

  (defret committee-faulty-members-of-commit-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (commit-possiblep val systate)
    :fn commit-next)

  (defret committee-faulty-members-of-timeout-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (timeout-possiblep val systate)
    :fn timeout-next)

  (defret committee-faulty-members-of-event-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (event-possiblep event systate)
    :fn event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-fault-tolerant-p ((commtt committeep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a committee is fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when
     the total stake of faulty members in the committee does not exceed
     the maximum tolerated stake of faulty validators in the committee."))
  (<= (committee-members-stake (committee-faulty-members commtt systate)
                               commtt)
      (committee-max-faulty-stake commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk validator-committees-fault-tolerant-p ((vstate validator-statep)
                                                  (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if the active committees calculated by a validator
          are all fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator calculates its own active committee at each round,
     based on its own copy of the blockchain.
     This predicate checks whether a validator (represented by its state)
     calculates committees that are fault tolerant,
     for all the rounds for which it can calculate a committee,
     given the validator's current blockchain."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt (active-committee-at-round
                                 round
                                 (validator-state->blockchain vstate))))
                     (implies commtt
                              (committee-fault-tolerant-p commtt systate)))))
  ///
  (fty::deffixequiv-sk validator-committees-fault-tolerant-p
    :args ((vstate validator-statep) (systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-committees-fault-tolerant-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a system state is fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when every correct validator in the system
     calculates active committees that are all fault-tolerant.")
   (xdoc::p
    "As explained in @(see fault-tolerance),
     fault tolerance is an assumption that must be made for every system state;
     it is not just an invariant property of the system
     given that it holds in the initial state,
     as would be the case with static committees
     in AleoBFT and other systems."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-committees-fault-tolerant-p
                    (get-validator-state val systate)
                    systate)))
  ///
  (fty::deffixequiv-sk system-committees-fault-tolerant-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-system-committees-fault-tolerant-p ((systate system-statep)
                                                (events event-listp))
  :guard (events-possiblep events systate)
  :returns (yes/no booleanp)
  :short "Check if all the system states
          in an execution from a system state via a sequence of events
          are fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "When talking about properties of executions,
     i.e. sequences of states from a starting state
     through a serie of states that result from a sequence of events,
     we need to make the hypothesis that
     all the committees along the way are fault-tolerant.
     This predicate expresses that:
     @('systate') is the starting state,
     and @('events') are the events that take the system
     through a sequence of states from the starting state.")
   (xdoc::p
    "For this predicate to hold,
     first the starting state must be fault-tolerant.
     If there are no events, there is no other requirement.
     Otherwise, we execute the event
     and we recursively call this predicate with the resulting state:
     this covers all the states in the execution."))
  (b* (((unless (system-committees-fault-tolerant-p systate)) nil)
       ((when (endp events)) t))
    (all-system-committees-fault-tolerant-p (event-next (car events) systate)
                                            (cdr events)))
  :measure (acl2-count events)
  :guard-hints (("Goal" :in-theory (enable events-possiblep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pick-correct-validator ((vals address-setp) (systate system-statep))
  :returns (val? address-optionp)
  :short "Pick a correct validator address, if present,
          from a set of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Correct validators are identified via the system state,
     so we pass a system state to this function.
     The correct validators are the keys of
     the map from addresses to validator states,
     in the system state.")
   (xdoc::p
    "We go through all the addresses in the set,
     returning the first one we find that is of a correct validator.
     We return @('nil') if there is no correct validator address in the set.")
   (xdoc::p
    "We show that if this function returns an address,
     the address is in the input set,
     and it is the address of a correct validator.
     We show that if this function returns @('nil'),
     then all the addresses are of faulty validators
     (expressed by saying that they have an empty intersection
     with the set of correct validators),
     because otherwise we would have found a correct one.")
   (xdoc::p
    "From the latter fact,
     we prove that this function will return an address
     if the following conditions are satisfied:
     the input set is a subset of a fault-tolerant committee,
     and the total stake of validators is more than @($f$),
     i.e. the maximum tolerated stake of faulty validators
     (see @(tsee max-faulty-for-total)).
     The reason is that if @('pick-correct-validator') returned @('nil'),
     then, as proved in @('all-faulty-when-not-pick-correct-validator'),
     all the validators in @('vals') are faulty.
     But since we hypothesize that their stake is more than @($f$),
     and since the fault tolerance hypothesis means that
     the total stake of faulty validators is no more than @($f$),
     we have an impossibility.
     Thus @('pick-correct-validator') must return an address,
     which, as proved in the other theorems,
     is in @('vals') and is a correct validator.
     We use the @('committee-members-stake-monotone') theorem
     to inject the appropriate facts into the proof.
     Given that @('vals') is a subset of the committee members,
     but that @('vals') is disjoint from correct addresses
     (by @('all-faulty-when-not-pick-correct-validator'),
     we have that @('vals') is in fact a subset of
     the committee's faulty members,
     whose total stake does not exceed @($f$) by fault tolerance,
     and thus the total stake of @('vals') does not exceed @($f$) either,
     which contradicts the hypothesis that it does.")
   (xdoc::p
    "A related fact, which we also prove,
     is that, if the committee is fault-tolerant and not-empty,
     and the validators' total stake is at least the quorum,
     then the function will pick a correct validator.
     This is a simple consequence of the previous theorem,
     given that @($f < n - f$) when @($n \\neq 0$)."))
  (b* (((when (set::emptyp vals)) nil)
       (val (set::head vals))
       ((when (set::in val (correct-addresses systate))) (address-fix val)))
    (pick-correct-validator (set::tail vals) systate))

  ///

  (fty::deffixequiv pick-correct-validator
    :args ((systate system-statep)))

  (defruled pick-correct-validator-in-set
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate)
                      vals))
    :induct t)

  (defruled pick-correct-validator-is-correct
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate)
                      (correct-addresses systate)))
    :induct t)

  (defruled all-faulty-when-not-pick-correct-validator
    (implies (not (pick-correct-validator vals systate))
             (set::emptyp (set::intersect vals (correct-addresses systate))))
    :induct t
    :enable (set::intersect
             not-in-address-setp-when-not-addressp))

  (defruled pick-correct-validator-when-fault-tolerant-and-gt-max-faulty
    (implies (and (address-setp vals)
                  (set::subset vals (committee-members commtt))
                  (committee-fault-tolerant-p commtt systate)
                  (> (committee-members-stake vals commtt)
                     (committee-max-faulty-stake commtt)))
             (pick-correct-validator vals systate))
    :enable (committee-fault-tolerant-p
             committee-faulty-members
             set::subset-of-difference-when-disjoint)
    :disable pick-correct-validator
    :use (all-faulty-when-not-pick-correct-validator
          (:instance committee-members-stake-monotone
                     (members1 vals)
                     (members2 (committee-faulty-members commtt systate)))))

  (defruled pick-correct-validator-when-fault-tolerant-and-geq-quorum
    (implies (and (address-setp vals)
                  (set::subset vals (committee-members commtt))
                  (committee-fault-tolerant-p commtt systate)
                  (committee-nonemptyp commtt)
                  (>= (committee-members-stake vals commtt)
                      (committee-quorum-stake commtt)))
             (pick-correct-validator vals systate))
    :enable (pick-correct-validator-when-fault-tolerant-and-gt-max-faulty
             committee-max-faulty-stake-lt-committee-quorum-stake)))
