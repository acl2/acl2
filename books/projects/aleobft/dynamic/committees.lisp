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

(include-book "blocks")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committees
  :parents (states)
  :short "Committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "Dynamic committees are one of the most distinctive features of AleoBFT.
     Starting with a genesis (i.e. initial) committee,
     validators join and leave the committe, by bonding and unbonding,
     which happens via transactions in the blockchain.
     Since every validator has its own view of the blockchain,
     it also has its own view of how the committee evolves.
     The agreement on the blockchains of the validators
     also provides an agreement on how the committee evolves,
     as proved in @(see same-committees).")
   (xdoc::p
    "In our model a committee consists of
     a non-empty set of validator addresses.
     We introduce a fixtype to wrap that, to enforce non-emptiness,
     and also for greater abstraction and extensibility.")
   (xdoc::p
    "Membership in a committee is simply set membership,
     but we introduce a slightly more abstract operation for that,
     also for future extensibility.")
   (xdoc::p
    "The genesis committee is arbitrary,
     but fixed for each execution of the protocol.
     Thus, we model the genesis committee via a constrained nullary function
     that returns the genesis committee.
     The genesis committee is globally known to all validators.")
   (xdoc::p
    "Each validator's view of the evolution of the committee
     is formalized via functions that operate on the blockchain,
     and that, starting with the genesis committee,
     calculate the committee at every block,
     by taking into considerations bonding and unbonding transactions.
     Blocks are produced at, and are associated with,
     (a subset of the) even rounds of the DAG.
     The notion of interest is that of the committee at a round,
     but this actually specializes into two notions,
     because of the committee lookback approach of AleoBFT.")
   (xdoc::p
    "One notion is that of the committee bonded at each round,
     i.e. the committee resulting from applying
     all the bonding and unbonding transactions up to that round
     to the genesis committee in order.
     There are actually two possible choices for defining this notion precisely,
     based on whether the committee bonded at an even round that has a block
     includes or excludes the transactions in that block.
     That is, do we consider the committee resulting at the end of that block
     to be the committee at that even round, or at the odd round that follows?
     The exact choice might affect the correctness properties,
     so we will need to be careful about the choice.")
   (xdoc::p
    "The other notion is that of the committee active at each round,
     i.e. the committee that is in charge of that round.
     This is the lookback committee: it is the bonded committee
     at a fixed number of previous rounds (``lookback'').
     The choice of when a bonded committee starts vs. ends discussed above
     affects the choice of when an active committee starts vs. ends,
     and that is what most directly may affect the correctness properties.")
   (xdoc::p
    "Here we define both notions, of bonded and active committee.
     We might need to revise them slightly
     as we investigate the correctness properties.")
   (xdoc::p
    "Committees are not explicit components of the "
    (xdoc::seetopic "system-states" "system states")
    ", but they are, in a way, derived components of validator states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod committee
  :short "Fixtype of committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our model, a committee is just a set of addresses,
     but we wrap it in a fixtype for greater abstraction and extensibility.
     When we generalize the model with stake,
     this committee fixtype will need to include the stake of each validator,
     besides the addresses of the validators."))
  ((addresses address-set
              :reqfix (if (set::emptyp addresses)
                          (set::insert (address nil) nil)
                        addresses)))
  :require (not (set::emptyp addresses))
  :pred committeep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption committee-option
  committee
  :short "Fixtype of optional committees."
  :pred committee-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-members ((commtt committeep))
  :returns (addresses address-setp)
  :short "Addresses of the members of the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a synonym of the fixtype deconstructor,
     but it provides a bit of abstract,
     especially facilitating the extension of the model with stake,
     in which a committee will be not just a set of addresses."))
  (committee->addresses commtt)
  :hooks (:fix)

  ///

  (defret not-emptyp-of-committee-members
    (not (set::emptyp addresses)))
  (in-theory (disable not-emptyp-of-committee-members)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection genesis-committee
  :short "Genesis committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see committees),
     there is an arbitrary but fixed genesis committee,
     which we capture via a constrained nullary function."))

  (encapsulate
    (((genesis-committee) => *))

    (local
     (defun genesis-committee ()
       (make-committee :addresses (set::insert (address nil) nil))))

    (defrule committeep-of-genesis-committee
      (committeep (genesis-committee)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-committee-with-transaction ((trans transactionp)
                                           (commtt committeep)
                                           (all-vals address-setp))
  :returns (new-commtt committeep)
  :short "Update a committee with a transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of transactions:
     bonding, unbonding, and other.
     A bonding transaction adds the validator address to the committee;
     there is no change if the validator is already in the committee.
     An unbonding transaction removes the validator address from the committee
     (except in a case explained below);
     there is no change if the validator is not in the committee.
     The other kind of transaction leaves the committee unchanged.")
   (xdoc::p
    "In order to maintain the non-emptiness of the committee,
     attempting to remove the only member of the committee
     does not actually remove it.
     An implementation of AleoBFT may require larger minimal committees,
     but for the purposes of our model,
     it suffices for the committee to be never empty.
     The protocol works, although in a degenerate way,
     with just one validator.")
   (xdoc::p
    "It is an interesting question whether an AleoBFT implementation
     should have mechanisms in place to guarantee minimal committee sizes.
     If it does, our model of unbonding captures a form of that.
     If it does not, which is plausible since validators
     should be generally free to bond and unbond as they want,
     then the whole network could be considered to fail
     if all validators unbond and there is nobody to run the network.
     If that is the case, our model of unbonding is still adequate to capture
     the situation in which the whole network has not failed;
     as mentioned above, the unbonding transaction that does not unbond
     can be simply regarded as if it were an @(':other') kind of transaction.")
   (xdoc::p
    "In order to maintain the fact that
     the committee is a subset of all the validators in the system,
     we pass to this function an input @('all-vals')
     that consists of the set of all validator addresses in the system.
     If a bonding transaction references an address outside that set,
     the committee is unchanged by that transaction,
     i.e. it is ignored.
     This is just a technical device in our formal model;
     it does not mean that validators need to know @('all-vals')
     in order to calculate committees.
     In an AleoBFT implementation,
     the existence of a bonding transaction with a certain address
     means that a validator with that address is part of the system,
     which in our model consists of all possible validators,
     and the one with that address is certainly a possibly validator.
     Thus, this is more of a constraint on
     the system of all validators
     than on the calculation of committees per se.")
   (xdoc::p
    "We prove that, if the old committee's members are in @('all-vals'),
     then the same holds for the new committee's members.
     That is, the invariant is maintained."))
  (transaction-case
   trans
   :bond (b* ((addresses (committee->addresses commtt))
              (new-addresses (set::insert trans.validator addresses)))
           (if (set::in trans.validator (address-set-fix all-vals))
               (change-committee commtt :addresses new-addresses)
             (committee-fix commtt)))
   :unbond (b* ((addresses (committee->addresses commtt))
                (new-addresses (set::delete trans.validator addresses)))
             (if (set::emptyp new-addresses)
                 (committee-fix commtt)
               (change-committee commtt :addresses new-addresses)))
   :other (committee-fix commtt))
  :hooks (:fix)

  ///

  (defret update-committee-with-transactions-subset-all-vals
    (set::subset (committee-members new-commtt) all-vals)
    :hyp (and (address-setp all-vals)
              (set::subset (committee-members commtt) all-vals))
    :hints (("Goal" :in-theory (enable* committee-members
                                        set::expensive-rules))))
  (in-theory (disable update-committee-with-transactions-subset-all-vals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-committee-with-transaction-list ((transs transaction-listp)
                                                (commtt committeep)
                                                (all-vals address-setp))
  :returns (new-commtt committeep)
  :short "Update a committee with a list of transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We update the committee with each transaction in the list,
     from left to right.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "We prove that, if the old committee's members are in @('all-vals'),
     then the same holds for the new committee's members.
     That is, the invariant is maintained."))
  (b* (((when (endp transs)) (committee-fix commtt))
       (commtt
        (update-committee-with-transaction (car transs) commtt all-vals)))
    (update-committee-with-transaction-list (cdr transs) commtt all-vals))
  :hooks (:fix)

  ///

  (defret update-committee-with-transaction-list-subset-all-vals
    (set::subset (committee-members new-commtt) all-vals)
    :hyp (and (address-setp all-vals)
              (set::subset (committee-members commtt) all-vals))
    :hints (("Goal"
             :induct t
             :in-theory
             (enable update-committee-with-transactions-subset-all-vals))))
  (in-theory (disable update-committee-with-transaction-list-subset-all-vals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-after-blocks ((blocks block-listp) (all-vals address-setp))
  :returns (commtt committeep)
  :short "Calculate the committee after a list of blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of blocks is the blockchain (of a validator),
     or a prefix of that blockchain (more on this later).
     We calculate the committee that results from
     updating the genesis committee with all the transactions in the blocks.
     Since, as explained in @(tsee validator-state),
     the blockchain goes from right to left
     (i.e. the leftmost block is the newest
     and the rightmost block is the oldest),
     we update the genesis committee from right to left
     to arrive at the resulting committee.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "We show that the committee's members are in @('all-vals'),
     so long as the genesis committee's members are."))
  (b* (((when (endp blocks)) (genesis-committee))
       (commtt (committee-after-blocks (cdr blocks) all-vals)))
    (update-committee-with-transaction-list (block->transactions (car blocks))
                                            commtt
                                            all-vals))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret committee-after-blocks-subset-all-vals
    (set::subset (committee-members commtt) all-vals)
    :hyp (and (address-setp all-vals)
              (set::subset (committee-members (genesis-committee))
                           all-vals))
    :hints (("Goal"
             :induct t
             :in-theory
             (enable
              update-committee-with-transaction-list-subset-all-vals))))
  (in-theory (disable committee-after-blocks-subset-all-vals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bonded-committee-at-round ((round posp)
                                   (blocks block-listp)
                                   (all-vals address-setp))
  :returns (commtt? committee-optionp)
  :short "Bonded committee at a given round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the committee that results from updating the genesis committee
     with all the transactions up to the latest block not after the round.
     The previous sentence is approximate, so we need to clarify it.
     First, the bonded committee at round 1 is certainly the genesis committee.
     If there is a block at round 2,
     with transactions that change the committee,
     we have two choices for the bonded committee at round 2:
     it could be still the genesis committee,
     or it could be the new committee after the block;
     this depends on whether we consider the new committee
     to be bonded at the beginning or at the end of round 2.
     The same kind of choice applies to any other even round
     with a block that changes the committee;
     on the other hand, it is always clear
     what the bonded committee at an odd round is,
     and also at even rounds without blocks,
     or with blocks that do not change the committee.")
   (xdoc::p
    "There seems to be no real criterion to choose between the two options,
     and it should not matter to correctness,
     i.e. the protocol should be correct either way.
     We choose to change committee at the end of the even round.
     Thus, the bonded committee at round 2 is always the genesis committee,
     which may change in round 3.")
   (xdoc::p
    "This ACL2 function returns the committee bonded at a given round,
     according to the choice explained above,
     But note that not every round has a bonded committee:
     after a certain round, the bonded committee is unknown,
     because there are no blocks yet.
     Suppose that the last block is at (even) round @('R').
     Then we know the committee bonded at rounds @('R+1') and @('R+2'),
     namely the committee resulting from
     all the transactions in the blockchain.
     We also know the committee bonded at @('R') and earlier rounds,
     based on prefixes of the full blockchain.
     But we do not know the committee bounded at rounds @('R+3') and later,
     because a block may be committed at round @('R+2'),
     which would then apply to @('R+3').
     This is why this ACL2 function returns an optional committee,
     which is @('nil') if the committee is not known.")
   (xdoc::p
    "The above also works if we take @('R = 0'),
     which is not a round number because round numbers are positive,
     but it can be regarded as somewhat of a pseudo-round number.
     If the blockchain is empty, we know the bonded committee at rounds 1 and 2,
     namely the genesis committee;
     but we do not know the bonded committee at round 3 and later,
     because a block may be committed at round 2
     which determines a new bonded committee at round 3 (and 4).")
   (xdoc::p
    "So here is how this ACL2 function to calculate the bonded committee works.
     First, we calculate the latest round @('L') for which we have a block,
     or 0 if the blockchain is empty.
     If the requested round (i.e. the @('round') input of this function)
     is more than 2 rounds later than @('L'),
     then the bonded committee is unknown, and we return @('nil').
     Recall that, as explained in @(tsee validator-state),
     the latest block is the leftmost, i.e. the @(tsee car).
     If instead the requested round is less than or equal to @('L+2'),
     then it has a bonded committee, which we calculate in a loop.")
   (xdoc::p
    "Since, as explained above, we regard the committe as
     changing at the end of the even round of each block,
     we need to find the latest block whose round is below @('round').
     Assuming that the block rounds are ordered (more on this later),
     we stop the loop as soon as we find a block with round below @('round'):
     we calculate the committee from that block and preceding blocks,
     and we return that as the bonded committee.
     If we reach the end of the blockchain, we return the genesis committee.")
   (xdoc::p
    "In a well-formed blockchain, the blocks all have even rounds,
     and the rounds strictly decrease going from left to right in the list.
     In this function we do not have this invariant,
     but we do not need that in order to define this function.
     Note that the loop terminates regardless of the round numbers.
     But in order to understand this function, it is best to think of
     the @('blocks') input forming a well-formed blockchain.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "We show that the bonded committee, if calculable,
     has members in @('all-vals'), so long as the genesis committee does.
     This derives from the analogous property
     of @(tsee committee-after-blocks)."))
  (b* (((when (> (pos-fix round)
                 (+ 2 (blocks-last-round blocks))))
        nil))
    (bonded-committee-at-round-loop round blocks all-vals))
  :hooks (:fix)

  :prepwork
  ((define bonded-committee-at-round-loop ((round posp)
                                           (blocks block-listp)
                                           (all-vals address-setp))
     :returns (commtt committeep)
     :parents nil
     (b* (((when (endp blocks)) (genesis-committee))
          ((when (> (pos-fix round)
                    (block->round (car blocks))))
           (committee-after-blocks blocks all-vals)))
       (bonded-committee-at-round-loop round (cdr blocks) all-vals))
     :hooks (:fix)

     ///

     (defruled bonded-committee-at-round-loop-when-no-blocks
       (implies (endp blocks)
                (equal (bonded-committee-at-round-loop round blocks all-vals)
                       (genesis-committee))))

     (defret bonded-committee-at-round-loop-subset-all-vals
       (set::subset (committee-members commtt) all-vals)
       :hyp (and (address-setp all-vals)
                 (set::subset (committee-members (genesis-committee))
                              all-vals))
       :hints (("Goal"
                :induct t
                :in-theory
                (enable committee-after-blocks-subset-all-vals))))
     (in-theory (disable bonded-committee-at-round-loop-subset-all-vals))

     (defruled bonded-committee-at-round-loop-of-round-leq-2
       (implies (and (blocks-ordered-even-p blocks)
                     (<= (pos-fix round) 2))
                (equal (bonded-committee-at-round-loop round blocks all-vals)
                       (genesis-committee)))
       :induct t
       :hints ('(:use evenp-of-car-when-blocks-ordered-even-p)))

     (defruled bonded-committee-at-round-loop-of-append-no-change
       (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                     (or (endp blocks1)
                         (<= (pos-fix round)
                             (block->round (car (last blocks1))))))
                (equal (bonded-committee-at-round-loop round
                                                       (append blocks1 blocks)
                                                       all-vals)
                       (bonded-committee-at-round-loop round blocks all-vals)))
       :induct t
       :enable (blocks-ordered-even-p-of-append
                last)
       :hints ('(:use (:instance newest-geq-oldest-when-blocks-ordered-even-p
                                 (blocks blocks1)))))))

  ///

  (defruled bonded-committee-at-earlier-round-when-at-later-round
    (implies (and (bonded-committee-at-round later blocks all-vals)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (bonded-committee-at-round earlier blocks all-vals)))

  (defruled bonded-committee-at-round-when-no-blocks
    (implies (endp blocks)
             (b* ((commtt (bonded-committee-at-round round blocks all-vals)))
               (implies commtt
                        (equal commtt (genesis-committee)))))
    :enable bonded-committee-at-round-loop-when-no-blocks)

  (defret bonded-committee-at-round-subset-all-vals
    (implies commtt?
             (set::subset (committee-members commtt?) all-vals))
    :hyp (and (address-setp all-vals)
              (set::subset (committee-members (genesis-committee))
                           all-vals))
    :hints
    (("Goal"
      :in-theory (enable bonded-committee-at-round-loop-subset-all-vals))))
  (in-theory (disable bonded-committee-at-round-subset-all-vals))

  (defruled bonded-committee-at-round-iff-round-upper-bound
    (iff (bonded-committee-at-round round blocks all-vals)
         (<= (pos-fix round)
             (+ 2 (blocks-last-round blocks)))))

  (defruled bonded-committee-at-round-of-round-leq-2
    (implies (and (blocks-ordered-even-p blocks)
                  (<= (pos-fix round) 2))
             (equal (bonded-committee-at-round round blocks all-vals)
                    (genesis-committee)))
    :enable bonded-committee-at-round-loop-of-round-leq-2)

  (defruled bonded-committee-at-round-of-append-no-change
    (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                  (bonded-committee-at-round round blocks all-vals))
             (equal (bonded-committee-at-round round
                                               (append blocks1 blocks)
                                               all-vals)
                    (bonded-committee-at-round round blocks all-vals)))
    :enable (blocks-last-round
             blocks-ordered-even-p-of-append
             bonded-committee-at-round-loop-of-append-no-change
             bonded-committee-at-round-loop-of-round-leq-2)
    :hints ('(:use ((:instance newest-geq-oldest-when-blocks-ordered-even-p
                               (blocks blocks1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lookback
  :short "Lookback amount."
  :long
  (xdoc::topstring
   (xdoc::p
    "It may seem natural for the committee bonded at a round
     to be in charge of that round,
     i.e. proposing and signing certificates for that round, etc.
     However, validators are not always perfectly in sync;
     there may be delays,
     and a validator's blockchain may be
     ahead of another validator's blockchain.
     For this reason, AleoBFT uses a lookback approach:
     the committee in charge of a round is `looked back' by a given amount.
     That is, the committee in charge for a round @('R')
     is the committee bonded at round @('R-B'),
     where @('B') is a fixed globally known positive integer.
     When @('R <= B'), the genesis committee is used.")
   (xdoc::p
    "The idea behind this lookback approach is that,
     by going sufficiently back in rounds (e.g. @('B = 100')),
     all validators should have blocks for those rounds,
     and should be able to calculate (and agree on)
     the committee bonded at those rounds.
     This is an assumption, which should be subjected to more formal study,
     but it is the rationale behind the approach.")
   (xdoc::p
    "Since @('B') is fixed and globally known,
     we introduce a constrained nullary function that returns it.
     There is no need to pick a specific value in this model;
     this way the model is more general.
     Should the need arise to prove properties that depend on
     specific values of @('B'),
     or more generally, on whether @('B') is in a certain range,
     those constraints can be hypotheses of such theorems."))

  (encapsulate
    (((lookback) => *))

    (local (defun lookback () 1))

    (defrule posp-of-lookback
      (posp (lookback))
      :rule-classes (:rewrite :type-prescription))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define active-committee-at-round ((round posp)
                                   (blocks block-listp)
                                   (all-vals address-setp))
  :returns (commtt? committee-optionp)
  :short "Active committee at a given round."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee lookback),
     the active committee for a given round,
     i.e. the one in charge of the round,
     is the one bonded at the earlier round
     whose distance is @('B') from the round of interest,
     or the genesis committee if such earlier round does not exist
     (i.e. it would be 0 or negative, before round 1).
     This ACL2 function formalizes this notion of active committee.")
   (xdoc::p
    "Note that there is no guarantee that there is a bonded committee
     at round @('R - B'), where @('R') is the round of interest.
     Thus, this function returns an optional committee,
     @('nil') if no committee is available.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "We show that the bonded committee, if calculable,
     has members in @('all-vals'), so long as the genesis committee does.
     This derives from the analogous property
     of @(tsee bonded-committee-at-round)."))
  (if (> (pos-fix round) (lookback))
      (bonded-committee-at-round (- (pos-fix round) (lookback))
                                 blocks
                                 all-vals)
    (genesis-committee))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled active-committee-at-earlier-round-when-at-later-round
    (implies (and (active-committee-at-round later blocks all-vals)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (active-committee-at-round earlier blocks all-vals))
    :enable (bonded-committee-at-earlier-round-when-at-later-round
             posp))

  (defruled active-committee-at-previous-round-when-at-round
    (implies (and (active-committee-at-round round blocks all-vals)
                  (> (pos-fix round) 1))
             (active-committee-at-round (1- round) blocks all-vals))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (1- round)))
    :enable pos-fix)

  (defruled active-committee-at-previous2-round-when-at-round
    (implies (and (active-committee-at-round round blocks all-vals)
                  (> (pos-fix round) 2))
             (active-committee-at-round (- round 2) blocks all-vals))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (- round 2)))
    :enable pos-fix)

  (defruled active-committee-at-previous3-round-when-at-round
    (implies (and (active-committee-at-round round blocks all-vals)
                  (> (pos-fix round) 3))
             (active-committee-at-round (- round 3) blocks all-vals))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (- round 3)))
    :enable pos-fix)

  (defruled active-committee-at-round-when-no-blocks
    (implies (endp blocks)
             (b* ((commtt (active-committee-at-round round blocks all-vals)))
               (implies commtt
                        (equal commtt (genesis-committee)))))
    :enable bonded-committee-at-round-when-no-blocks)

  (defret active-committee-at-round-subset-all-vals
    (implies commtt?
             (set::subset (committee-members commtt?)
                          all-vals))
    :hyp (and (address-setp all-vals)
              (set::subset (committee-members (genesis-committee))
                           all-vals))
    :hints
    (("Goal"
      :in-theory (enable bonded-committee-at-round-subset-all-vals))))
  (in-theory (disable active-committee-at-round-subset-all-vals))

  (defruled active-committee-at-round-iff-round-upper-bound
    (iff (active-committee-at-round round blocks all-vals)
         (<= (nfix (- (pos-fix round) (lookback)))
             (+ 2 (blocks-last-round blocks))))
    :enable (bonded-committee-at-round-iff-round-upper-bound
             nfix
             pos-fix
             posp))

  (defruled active-committee-at-round-of-round-leq-2+lookback
    (implies (and (blocks-ordered-even-p blocks)
                  (<= (pos-fix round) (+ 2 (lookback))))
             (equal (active-committee-at-round round blocks all-vals)
                    (genesis-committee)))
    :enable bonded-committee-at-round-of-round-leq-2
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defruled active-committee-at-round-of-append
    (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                  (active-committee-at-round round blocks all-vals))
             (equal (active-committee-at-round round
                                               (append blocks1 blocks)
                                               all-vals)
                    (active-committee-at-round round blocks all-vals)))
    :enable bonded-committee-at-round-of-append-no-change))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-faulty-for-total ((total natp))
  :returns (max natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable natp zp))))
  :short "Maximum number of faulty validators, out of a total,
          for the protocol to be fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classic BFT condition for fault tolerance is that
     the number of faulty validators is (strictly) less than
     one third of the total number of validators:
     @($f < n/3$), using the common symbols
     @($f$) and @($n$) for the two numbers.
     This relation works for every positive @($n$),
     whether it is a multiple of 3 or not.
     Multiplying both sides by 3, we get @($3f < n$),
     and taking @($f$) as the maximum value that satisfies the inequality
     (as opposed to potentially smaller values than the maximum),
     we get to the sometimes stated condition @($n = 3f + 1$),
     although this condition is less general for @($n$),
     because it forces @($n$) to be one more than a multiple of 3.
     The other possibilities are @($n = 3f + 2$) and @($n = 3f + 3$).")
   (xdoc::p
    "The distinction between the maximum @($f$)
     and possibly smaller values of @($f$)
     is worth emphasizing,
     because recent BFT literature
     does not always state things clearly in this respect.
     The actual number of faulty validators
     is not something that validators know.
     In contrast, the total number @($n$) of validators is known,
     and thus the maximum @($f$) satisfying @($f < n/3$)
     can be calculated from @($n$).
     So when a validator needs to use @($f$) in some computation,
     it is the maximum such @($f$), calculable from @($n$),
     not the (unknowable to the validator) number of faulty validators.")
   (xdoc::p
    "Some BFT literature uses phrases like
     ``up to @($f < n/3$) faulty validators'',
     implying that @($f$) is another parameter of the system, besides @($n$).
     But when validators need to use @($f$) as part of their computation,
     as is the case for AleoBFT,
     it makes more sense for @($f$) to be the maximum value
     that satisfies the inequality,
     because it allows for the maximum possible number of faulty validators.
     So in our model @($f$) is always that maximum,
     and it is calculable from @($n$).")
   (xdoc::p
    "This ACL2 function performs this calculation.
     The input @('total') is @($n$),
     and the output is the maximum @($f$) such that @($f < n/3$).
     We define the function to return 0 if @($n = 0$),
     although @($n = 0$) does not correspond to a practical situation.
     So consider the normal case @($n > 0$)
     (we could strengthen the guard of this function
     to require a positive integer as input).
     If @($n$) is a multiple of 3,
     @($f$) is one less than the integer @($n/3$);
     if @($n$) is not a multiple of 3,
     @($f$) is the floor of @($n/3$).
     We can put the two cases together by noting that
     the ceiling of an integer is the integer (i.e. a no-op)
     and that the floor of a non-integer is
     one less than the ceiling of the non-integer.
     So we define @($f$) as
     one less than the ceiling of @($n/3$),
     or equivalently as the floor of @($(n-1)/3$).
     We prove the two equivalent, in fact.
     We also prove that this function returns something below @($n/3$),
     and one more is not below @($n/3$):
     that is, we prove that it returns the maximum.
     We could have alternatively defined this function in terms of maximum,
     via a recursion to find it, or even in a non-executable way,
     but instead we pick the definition with ceiling,
     and prove it equivalent to the other two possible definitions.
     We also prove that @($n \\geq 3f + 1$).")
   (xdoc::p
    "If @($n$) is 1 or 2 or 3, no failures are tolerated:
     @($f$) must be 0.
     The case @($n = 1$) is a degenerate one,
     but the protocol could probably still work in a degenerate way.
     The cases @($n = 2$) and @($n = 3$) could make sense,
     but since they tolerate no failures,
     they are not used in practice.
     If @($n$) is 4 or more, we can tolerate
     an increasing number of faulty validators,
     any number less than or equal to $f$,
     so that is usually the practical minimum for @($n$)."))
  (if (zp total)
      0
    (1- (ceiling total 3)))

  ///

  (fty::deffixequiv max-faulty-for-total
    :hints (("Goal" :in-theory (enable nfix))))

  (defruled max-faulty-for-total-alt-def
    (equal (max-faulty-for-total n)
           (if (zp n)
               0
             (floor (1- n) 3))))

  (theory-invariant (incompatible (:definition max-faulty-for-total)
                                  (:rewrite max-faulty-for-total-alt-def)))

  (defret max-faulty-for-total-upper-bound
    (< max (/ total 3))
    :hyp (not (zp total))
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total)))))
  (in-theory (disable max-faulty-for-total-upper-bound))

  (defret max-faulty-for-total-upper-bound-tight
    (>= (1+ max) (/ total 3))
    :hyp (not (zp total))
    :rule-classes ((:linear
                    :trigger-terms ((1+ (max-faulty-for-total total))))))
  (in-theory (disable max-faulty-for-total-upper-bound-tight))

  (defruled total-lower-bound-wrt-max-faulty
    (implies (not (zp total))
             (>= total
                 (1+ (* 3 (max-faulty-for-total total)))))
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total)))))

  (defret max-faulty-for-total-leq-total
    (<= max (nfix total))
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total))))
    :hints (("Goal" :in-theory (enable nfix))))
  (in-theory (disable max-faulty-for-total-leq-total))

  (defret max-faulty-for-total-lt-total-when-posp
    (< max total)
    :hyp (posp total)
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total))))
    :hints (("Goal" :in-theory (enable posp))))
  (in-theory (disable max-faulty-for-total-lt-total-when-posp))

  (assert-event (= (max-faulty-for-total 0) 0))
  (assert-event (= (max-faulty-for-total 1) 0))
  (assert-event (= (max-faulty-for-total 2) 0))
  (assert-event (= (max-faulty-for-total 3) 0))
  (assert-event (= (max-faulty-for-total 4) 1))
  (assert-event (= (max-faulty-for-total 5) 1))
  (assert-event (= (max-faulty-for-total 6) 1))
  (assert-event (= (max-faulty-for-total 7) 2))
  (assert-event (= (max-faulty-for-total 8) 2))
  (assert-event (= (max-faulty-for-total 9) 2))
  (assert-event (= (max-faulty-for-total 10) 3))
  (assert-event (= (max-faulty-for-total 11) 3))
  (assert-event (= (max-faulty-for-total 12) 3))
  (assert-event (= (max-faulty-for-total 13) 4))
  (assert-event (= (max-faulty-for-total 14) 4))
  (assert-event (= (max-faulty-for-total 15) 4))
  (assert-event (= (max-faulty-for-total 15) 4))
  (assert-event (= (max-faulty-for-total 16) 5))
  (assert-event (= (max-faulty-for-total 17) 5))
  (assert-event (= (max-faulty-for-total 18) 5))
  (assert-event (= (max-faulty-for-total 19) 6))
  (assert-event (= (max-faulty-for-total 20) 6))
  (assert-event (= (max-faulty-for-total 25) 8))
  (assert-event (= (max-faulty-for-total 100) 33)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-total ((commtt committeep))
  :returns (total posp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :in-theory (enable posp))))
  :short "Total number of validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just the number of addresses.")
   (xdoc::p
    "This is @($n$), using the notation in @(tsee max-faulty-for-total).
     But note that, unlike typical BFT literature,
     where there is a fixed set of validators,
     in AleoBFT we have dynamic committees,
     and so @($n$) is a function of the committee."))
  (set::cardinality (committee-members commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-max-faulty ((commtt committeep))
  :returns (maxf natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum tolerated number of faulty validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($f$) discussed in @(tsee max-faulty-for-total)
     applies to a committee, not to the whole system,
     in the same way as @($n$)."))
  (max-faulty-for-total (committee-total commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-quorum ((commtt committeep))
  :returns (quorum
            posp
            :rule-classes (:rewrite :type-prescription)
            :hints (("Goal"
                     :in-theory
                     (enable posp
                             committee-max-faulty
                             max-faulty-for-total-lt-total-when-posp))))
  :short "Quorum of validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in the BFT literature,
     the quorum number in AleoBFT is @($n - f$),
     where @($n$) and @($f$) are the numbers explained
     in @(tsee max-faulty-for-total).
     As @($n$) and @($f$) are functions of the committee,
     the quorum number is a function of the committee too.")
   (xdoc::p
    "Some recent BFT literature uses @($2f + 1$) as the quorum number,
     which is correct only if @($n = 3f + 1$),
     but not if @($n = 3f + 2$) and @($n = 3f + 3$),
     which are the other two possibilities,
     as discussed in @(tsee max-faulty-for-total).
     Unfortunately that literature uses @($2f + 1$)
     without explicating the @($n = 3f + 1$) assumption.
     There is indeed no reason for making this assumption,
     which is unnecessarily restrictive,
     given that the more general quorum @($n - f$)
     works for any value of @($n$)."))
  (- (committee-total commtt)
     (committee-max-faulty commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-bonded-committees-p ((blocks1 block-listp)
                                     (blocks2 block-listp)
                                     (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if two blockchains calculate consistent bonded committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two blockchains may differ, in particular in length,
     but the predicate checks that,
     when they both calculate a bonded committeed at a round,
     they calculate the same committee.
     It allows only one blockchain to calculate
     the bonded committee for a round,
     with the other blockchain being too short for that."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt1 (bonded-committee-at-round round
                                                            blocks1
                                                            all-vals))
                        (commtt2 (bonded-committee-at-round round
                                                            blocks2
                                                            all-vals)))
                     (implies (and commtt1
                                   commtt2)
                              (equal commtt1 commtt2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-active-committees-p ((blocks1 block-listp)
                                     (blocks2 block-listp)
                                     (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if two blockchains calculate consistent active committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two blockchains may differ, in particular in length,
     but the predicate checks that,
     when they both calculate a active committeed at a round,
     they calculate the same committee.
     It allows only one blockchain to calculate
     the active committee for a round,
     with the other blockchain being too short for that."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt1 (active-committee-at-round round
                                                            blocks1
                                                            all-vals))
                        (commtt2 (active-committee-at-round round
                                                            blocks2
                                                            all-vals)))
                     (implies (and commtt1
                                   commtt2)
                              (equal commtt1 commtt2))))))
