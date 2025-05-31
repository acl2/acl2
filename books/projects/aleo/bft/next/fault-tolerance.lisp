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

(include-book "active-committees-after-commit")

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

  (defret committee-correct-members-of-propose-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :fn propose-next)

  (defret committee-correct-members-of-endorse-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :fn endorse-next)

  (defret committee-correct-members-of-augment-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next)

  (defret committee-correct-members-of-certify-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :fn certify-next)

  (defret committee-correct-members-of-accept-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next)

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

  (defret committee-correct-members-of-event-next
    (equal (committee-correct-members commtt new-systate)
           (committee-correct-members commtt systate))
    :hyp (event-possiblep event systate)
    :fn event-next
    :hints (("Goal" :in-theory (enable event-possiblep
                                       event-next)))))

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

  (defret committee-faulty-members-of-propose-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :fn propose-next)

  (defret committee-faulty-members-of-endorse-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :fn endorse-next)

  (defret committee-faulty-members-of-augment-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next)

  (defret committee-faulty-members-of-certify-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :fn certify-next)

  (defret committee-faulty-members-of-accept-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next)

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

  (defret committee-faulty-members-of-event-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (event-possiblep event systate)
    :fn event-next
    :hints (("Goal" :in-theory (enable event-possiblep
                                       event-next)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-fault-tolerant-p ((commtt committeep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a committee is fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when
     the total stake of faulty members in the committee does not exceed
     the maximum tolerated stake of faulty validators in the committee.
     Or, equivalently,
     when the total stake of the correct members in the committee
     is at least the quorum stake of the committee;
     we prove this equivalent definition as a theorem.")
   (xdoc::p
    "The fault tolerance of a committee does not change
     as the system transitions from one state to the next,
     because the dependency on the system state is only on
     the addresses of correct vs. faulty validators,
     which do not change as the system evolves."))
  (<= (committee-members-stake (committee-faulty-members commtt systate)
                               commtt)
      (committee-max-faulty-stake commtt))
  :hooks (:fix)

  ///

  (defruled committee-fault-tolerant-p-alt-def
    (equal (committee-fault-tolerant-p commtt systate)
           (>= (committee-members-stake
                (committee-correct-members commtt systate)
                commtt)
               (committee-quorum-stake commtt)))
    :enable (committee-correct-members
             committee-faulty-members
             committee-quorum-stake
             committee-total-stake
             committee-members-stake-of-difference
             committee-members-stake-of-union))

  (defret committee-fault-tolerant-p-of-propose-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :fn propose-next)

  (defret committee-fault-tolerant-p-of-endorse-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :fn endorse-next)

  (defret committee-fault-tolerant-p-of-augment-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next)

  (defret committee-fault-tolerant-p-of-certify-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :fn certify-next)

  (defret committee-fault-tolerant-p-of-accept-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next)

  (defret committee-fault-tolerant-p-of-advance-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next)

  (defret committee-fault-tolerant-p-of-commit-next
    (equal (committee-fault-tolerant-p commtt new-systate)
           (committee-fault-tolerant-p commtt systate))
    :hyp (commit-possiblep val systate)
    :fn commit-next)

  (defret committee-fault-tolerant-p-of-event-next
    (equal (committee-faulty-members commtt new-systate)
           (committee-faulty-members commtt systate))
    :hyp (event-possiblep event systate)
    :fn event-next))

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
     calculates committees that are fault-tolerant,
     for all the rounds for which it can calculate a committee,
     given the validator's current blockchain.")
   (xdoc::p
    "For each state transition,
     if this predicate holds on a validator's state after the transition,
     then it also holds on the validator's state before the transition.
     This is because the committees that
     a validator can calculate before the transition
     are a subset of the ones that
     the validator can calculate after the transition.
     They are in fact the same for all transitions except @('commit'),
     because the other transitions do not change any blockchains.
     For a @('commit') transition,
     only the blockchain of the target validator changes,
     but as proved in @(see active-committees-after-commit),
     the event does not affect
     the calculation of committees at earlier rounds.")
   (xdoc::p
    "First we prove lemmas involving
     just the @('systate') argument of the predicate,
     which follow directly from
     the preservation of @(tsee committee-fault-tolerant-p)
     proved earlier.
     The lemmas are then used to prove theorems
     involving both arguments of the predicate.
     For both the lemmas and the theorems,
     the @(':use') hints are needed to inject into the proofs
     the terms for which the appropriate rules apply."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt (active-committee-at-round
                                 round
                                 (validator-state->blockchain vstate))))
                     (implies commtt
                              (committee-fault-tolerant-p commtt systate)))))

  ///

  (fty::deffixequiv-sk validator-committees-fault-tolerant-p
    :args ((vstate validator-statep) (systate system-statep)))

  (defret validator-committees-fault-tolerant-p-of-propose-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :fn propose-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (propose-next prop dests systate))))))

  (defret validator-committees-fault-tolerant-p-of-endorse-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :fn endorse-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (endorse-next prop endor systate))))))

  (defret validator-committees-fault-tolerant-p-of-augment-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (augment-next prop endor systate))))))

  (defret validator-committees-fault-tolerant-p-of-certify-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :fn certify-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (certify-next cert dests systate))))))

  (defret validator-committees-fault-tolerant-p-of-accept-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (accept-next val cert systate))))))

  (defret validator-committees-fault-tolerant-p-of-advance-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (advance-next val systate))))))

  (defret validator-committees-fault-tolerant-p-of-commit-next-lemma
    (implies (validator-committees-fault-tolerant-p vstate new-systate)
             (validator-committees-fault-tolerant-p vstate systate))
    :hyp (commit-possiblep val systate)
    :fn commit-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           vstate systate))
                   (systate (commit-next val systate))))))

  (defret validator-committees-fault-tolerant-p-of-propose-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val systate) systate))
    :fn propose-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val systate)
                           systate))
                   (vstate (get-validator-state
                            val (propose-next prop dests systate)))))))

  (defret validator-committees-fault-tolerant-p-of-endorse-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val systate) systate))
    :fn endorse-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val systate)
                           systate))
                   (vstate (get-validator-state
                            val (endorse-next prop endor systate)))))))

  (defret validator-committees-fault-tolerant-p-of-augment-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val systate) systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val systate)
                           systate))
                   (vstate (get-validator-state
                            val (augment-next prop endor systate)))))))

  (defret validator-committees-fault-tolerant-p-of-certify-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val systate) systate))
    :fn certify-next
    :hints (("Goal"
             :in-theory (disable validator-committees-fault-tolerant-p-necc)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val systate)
                           systate))
                   (vstate (get-validator-state
                            val (certify-next cert dests systate)))))))

  (defret validator-committees-fault-tolerant-p-of-accept-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val1 new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val1 systate) systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next
    :hints (("Goal"
             :in-theory
             (enable
              validator-committees-fault-tolerant-p-of-accept-next-lemma)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val1 systate)
                           systate))
                   (vstate (get-validator-state
                            val1 (accept-next val cert systate)))))))

  (defret validator-committees-fault-tolerant-p-of-advance-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val1 new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val1 systate) systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next
    :hints (("Goal"
             :in-theory
             (enable
              validator-committees-fault-tolerant-p-of-advance-next-lemma)
             :use (:instance
                   validator-committees-fault-tolerant-p-necc
                   (round (validator-committees-fault-tolerant-p-witness
                           (get-validator-state val1 systate)
                           systate))
                   (vstate (get-validator-state
                            val1 (advance-next val systate)))))))

  (defret validator-committees-fault-tolerant-p-of-commit-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val1 new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val1 systate) systate))
    :hyp (and (commit-possiblep val systate)
              (last-blockchain-round-p systate)
              (ordered-blockchain-p systate))
    :fn commit-next
    :hints
    (("Goal"
      :in-theory (enable active-committee-at-round-of-commit-next)
      :use (:instance
            validator-committees-fault-tolerant-p-necc
            (round (validator-committees-fault-tolerant-p-witness
                    (get-validator-state val1 systate) systate))
            (vstate (get-validator-state
                     val1 (commit-next val systate)))))))

  (defret validator-committees-fault-tolerant-p-of-event-next
    (implies (validator-committees-fault-tolerant-p
              (get-validator-state val new-systate) new-systate)
             (validator-committees-fault-tolerant-p
              (get-validator-state val systate) systate))
    :hyp (and (event-possiblep event systate)
              (last-blockchain-round-p systate)
              (ordered-blockchain-p systate))
    :fn event-next
    :hints
    (("Goal" :in-theory (e/d (event-possiblep
                              event-next)
                             (validator-committees-fault-tolerant-p)))))

  (in-theory
   (disable validator-committees-fault-tolerant-p-of-propose-next-lemma
            validator-committees-fault-tolerant-p-of-endorse-next-lemma
            validator-committees-fault-tolerant-p-of-augment-next-lemma
            validator-committees-fault-tolerant-p-of-certify-next-lemma
            validator-committees-fault-tolerant-p-of-accept-next-lemma
            validator-committees-fault-tolerant-p-of-advance-next-lemma
            validator-committees-fault-tolerant-p-of-commit-next-lemma
            validator-committees-fault-tolerant-p-of-propose-next
            validator-committees-fault-tolerant-p-of-endorse-next
            validator-committees-fault-tolerant-p-of-augment-next
            validator-committees-fault-tolerant-p-of-certify-next
            validator-committees-fault-tolerant-p-of-accept-next
            validator-committees-fault-tolerant-p-of-advance-next
            validator-committees-fault-tolerant-p-of-commit-next
            validator-committees-fault-tolerant-p-of-event-next)))

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
     in AleoBFT and other systems.")
   (xdoc::p
    "We show that if this predicate holds after a state transition,
     it also holds before the state transition.
     We use the similar theorems proved for
     @(tsee validator-committees-fault-tolerant-p),
     to prove these theorems.
     We also extend it to sequences of events.
     These properties are conditional on two already proved invariants."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-committees-fault-tolerant-p
                    (get-validator-state val systate)
                    systate)))

  ///

  (fty::deffixequiv-sk system-committees-fault-tolerant-p
    :args ((systate system-statep)))

  (defret system-committees-fault-tolerant-p-of-propose-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :fn propose-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-propose-next
                      (val (system-committees-fault-tolerant-p-witness
                            systate))))))

  (defret system-committees-fault-tolerant-p-of-endorse-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :fn endorse-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-endorse-next
                      (val (system-committees-fault-tolerant-p-witness
                            systate))))))

  (defret system-committees-fault-tolerant-p-of-augment-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :hyp (augment-possiblep prop endor systate)
    :fn augment-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-augment-next
                      (val (system-committees-fault-tolerant-p-witness
                            systate))))))

  (defret system-committees-fault-tolerant-p-of-certify-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :fn certify-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-certify-next
                      (val (system-committees-fault-tolerant-p-witness
                            systate))))))

  (defret system-committees-fault-tolerant-p-of-accept-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :hyp (accept-possiblep val cert systate)
    :fn accept-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-accept-next
                      (val1 (system-committees-fault-tolerant-p-witness
                             systate))))))

  (defret system-committees-fault-tolerant-p-of-advance-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :hyp (advance-possiblep val systate)
    :fn advance-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-advance-next
                      (val1 (system-committees-fault-tolerant-p-witness
                             systate))))))

  (defret system-committees-fault-tolerant-p-of-commit-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :hyp (and (commit-possiblep val systate)
              (last-blockchain-round-p systate)
              (ordered-blockchain-p systate))
    :fn commit-next
    :hints
    (("Goal"
      :use (:instance validator-committees-fault-tolerant-p-of-commit-next
                      (val1 (system-committees-fault-tolerant-p-witness
                             systate))))))

  (defret system-committees-fault-tolerant-p-of-event-next
    (implies (system-committees-fault-tolerant-p new-systate)
             (system-committees-fault-tolerant-p systate))
    :hyp (and (event-possiblep event systate)
              (last-blockchain-round-p systate)
              (ordered-blockchain-p systate))
    :fn event-next
    :hints (("Goal" :in-theory (e/d (event-possiblep
                                     event-next)
                                    (system-committees-fault-tolerant-p)))))

  (defruled system-committees-fault-tolerant-p-of-events-next
    (implies (and (events-possiblep events systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate))
             (b* ((new-systate (events-next events systate)))
               (implies (system-committees-fault-tolerant-p new-systate)
                        (system-committees-fault-tolerant-p systate))))
    :induct t
    :enable (events-possiblep
             events-next))

  (in-theory (disable system-committees-fault-tolerant-p-of-propose-next
                      system-committees-fault-tolerant-p-of-endorse-next
                      system-committees-fault-tolerant-p-of-augment-next
                      system-committees-fault-tolerant-p-of-certify-next
                      system-committees-fault-tolerant-p-of-accept-next
                      system-committees-fault-tolerant-p-of-advance-next
                      system-committees-fault-tolerant-p-of-commit-next
                      system-committees-fault-tolerant-p-of-event-next
                      system-committees-fault-tolerant-p-of-events-next)))

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
     is in @('vals') and is the address of a correct validator.
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
     given that @($f < n - f$) when @($n \\neq 0$).
     This fact is important, as it allows, under fault tolerance assumptions,
     a validator to rely on at least a correct validator having performed
     the appropriate checks on a proposal
     when the proposal has a quorum of signers;
     this is used when a validator needs to decide
     whether to accept an incoming certificate or not."))
  (b* (((when (set::emptyp (address-set-fix vals))) nil)
       (val (set::head vals))
       ((when (set::in val (correct-addresses systate))) val))
    (pick-correct-validator (set::tail vals) systate))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :hooks (:fix)

  ///

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
             (set::emptyp (set::intersect (address-set-fix vals)
                                          (correct-addresses systate))))
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
