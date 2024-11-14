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

(define-sk validator-fault-tolerant-p ((vstate validator-statep)
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
  (fty::deffixequiv-sk validator-fault-tolerant-p
    :args ((vstate validator-statep) (systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-fault-tolerant-p ((systate system-statep))
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
                   (validator-fault-tolerant-p
                    (get-validator-state val systate)
                    systate)))
  ///
  (fty::deffixequiv-sk system-fault-tolerant-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-system-fault-tolerant-p ((events event-listp)
                                     (systate system-statep))
  :guard (events-possiblep events systate)
  :returns (yes/no booleanp)
  :short "Check if all the system states
          in an execution corresponding to a sequence of events
          are fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "When talking about properties of executions,
     i.e. sequences of states from a starting state
     through a serie of states that result from a sequence of events,
     we need to make the hypothesis that
     all the committees along the way are fault-tolerant.
     This predicate expresses that.")
   (xdoc::p
    "For this predicate to hold,
     first the input state must be fault-tolerant.
     If there are no events, there is no other requirement.
     Otherwise, we execute the event
     and we recursively call this predicate with the resulting state:
     this covers all the states in the execution."))
  (b* (((unless (system-fault-tolerant-p systate)) nil)
       ((when (endp events)) t))
    (all-system-fault-tolerant-p (cdr events)
                                 (event-next (car events) systate)))
  :guard-hints (("Goal" :in-theory (enable events-possiblep)))
  :hooks (:fix))
