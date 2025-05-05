; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "transitions")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)

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
    "In typical BFT systems, including AleoBFT with static committees,
     the notion of fault tolerance applies to the system as a whole,
     based on the number of correct and faulty validators:
     the system is fault-tolerant if the actual number of faulty validators
     does not exceed @($f$), which is calculated from the total @($n$),
     as formalized in @(tsee max-faulty-for-total).
     With dynamic committees, the notion applies to
     every committee that arises during the execution of the protocol.
     It has to be an assumption on every such committee:
     it cannot be checked by validators,
     who do not know which validator is correct vs. faulty.")
   (xdoc::p
    "Here we formalize this notion for committees,
     which is then used as a hypothesis for
     certain correctness theorems of AleoBFT."))
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
     associates a validator state or @('nil') to the validator's address.
     Thus, we need the system state besides the committee
     to calculate this set of addresses,
     which we do by intersecting the committee's addresses
     with the addressess of all the correct validators in the system.")
   (xdoc::p
    "Since, as proved in the definition of the system state transitions,
     the correctness vs. faultiness of validators never changes
     (recall that our system model includes all possible validators,
     not just the committee),
     it follows that, given a committee,
     the result of this ACL2 function does not change
     as the system state evolves,
     which we prove here."))
  (set::intersect (committee-members commtt)
                  (correct-addresses systate))
  :hooks (:fix)

  ///

  (defret committee-correct-members-of-create-certificate-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :fn create-certificate-next)

  (defret committee-correct-members-of-receive-certificate-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (receive-certificate-possiblep msg systate)
    :fn receive-certificate-next)

  (defret committee-correct-members-of-store-certificate-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (store-certificate-possiblep val cert systate)
    :fn store-certificate-next)

  (defret committee-correct-members-of-advance-round-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (advance-round-possiblep val systate)
    :fn advance-round-next)

  (defret committee-correct-members-of-commit-anchors-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (commit-anchors-possiblep val systate)
    :fn commit-anchors-next)

  (defret committee-correct-members-of-timer-expires-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (timer-expires-possiblep val systate)
    :fn timer-expires-next)

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
    "This is similar to @(tsee committee-correct-members),
     but for faulty instead of correct validators."))
  (set::intersect (committee-members commtt)
                  (faulty-addresses systate))
  :hooks (:fix)

  ///

  (defret committee-faulty-members-of-create-certificate-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :fn create-certificate-next)

  (defret committee-faulty-members-of-receive-certificate-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (receive-certificate-possiblep msg systate)
    :fn receive-certificate-next)

  (defret committee-faulty-members-of-store-certificate-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (store-certificate-possiblep val cert systate)
    :fn store-certificate-next)

  (defret committee-faulty-members-of-advance-round-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (advance-round-possiblep val systate)
    :fn advance-round-next)

  (defret committee-faulty-members-of-commit-anchors-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (commit-anchors-possiblep val systate)
    :fn commit-anchors-next)

  (defret committee-faulty-members-of-timer-expires-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (timer-expires-possiblep val systate)
    :fn timer-expires-next)

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
     the actual number of faulty members in the committee does not exceed
     the maximum number of faulty validators in the committee."))
  (<= (set::cardinality (committee-faulty-members commtt systate))
      (committee-max-faulty commtt))
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
     calculates committees that are fault-tolerant,
     for all the rounds for which it can calculate a committee,
     given the validator's current blockchain.")
   (xdoc::p
    "Note that we instantiate the @('all-vals') parameter
     of @(tsee create-certificate-endorser-possiblep)
     with the set of all the addresses of all validators in the system;
     that is indeed the rols of @('all-vals'),
     as explained in @(tsee update-committee-with-transaction)."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt (active-committee-at-round
                                 round
                                 (validator-state->blockchain vstate)
                                 (all-addresses systate))))
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
     given just the initial state,
     as was the case with static committees in AleoBFT."))
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
    "The input state must be fault-tolerant.
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
