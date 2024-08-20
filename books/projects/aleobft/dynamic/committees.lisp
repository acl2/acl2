; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "blocks")

(local (include-book "arithmetic-3/top" :dir :system))

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
     it also has its own view of how the committees evolves.
     The agreement on the blockchains of the validators
     should also provide an agreement on how the committee evolves;
     this is what we are in the progress of formally proving.")
   (xdoc::p
    "In our model a committee consists of a set of validator addresses,
     but we introduce a fixtype to wrap that,
     for greater abstraction and extensibility.")
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
     That is, this is the committeed bonded at each round.
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
    ", but they are in a way derived components of validator states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod committee
  :short "Fixtype of committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our model, a committee is just a set of addresses,
     but we wrap it in a fixtype for greater abstract and extensibility.
     When we generalize the model with stake,
     this committee fixtype will need to include the stake of each validator,
     besides the addresses of the validators."))
  ((addresses address-set))
  :pred committeep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption committee-option
  committee
  :short "Fixtype of optional committees."
  :pred committee-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-memberp ((val addressp) (commtt committeep))
  :returns (yes/no booleanp)
  :short "Check if a validator is a member of a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator is identifier by its address.
     We check whether the address is in the committee."))
  (set::in (address-fix val) (committee->addresses commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-nonemptyp ((commtt committeep))
  :returns (yes/no booleanp)
  :short "Check if a committee is not empty."
  (not (set::emptyp (committee->addresses commtt)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection genesis-committee
  :short "Genesis committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see committees),
     there is an arbitrary but fixed genesis committee,
     which we capture via a constrained nullary function.
     We require the function to return a committee
     with a non-empty set of addresses."))

  (encapsulate
    (((genesis-committee) => *))

    (local
     (defun genesis-committee ()
       (make-committee :addresses (set::insert (address nil) nil))))

    (defrule committeep-of-genesis-committee
      (committeep (genesis-committee)))

    (defrule not-emptyp-of-genesis-committee-addresses
      (not (set::emptyp (committee->addresses (genesis-committee)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-committee-with-transaction ((trans transactionp)
                                           (commtt committeep))
  :returns (new-commtt committeep)
  :short "Update a committee with a transaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of transactions:
     bonding, unbonding, and other.
     A bonding transaction adds the validator address to the committee;
     there is no change if the validator is already in the committee.
     An unbonding transaction removes the validator address from the committee;
     there is no change if the validator is not in the committee.
     The other kind of transaction leaves the committee unchanged."))
  (transaction-case
   trans
   :bond (change-committee
          commtt
          :addresses (set::insert trans.validator
                                  (committee->addresses commtt)))
   :unbond (change-committee
            commtt
            :addresses (set::delete trans.validator
                                    (committee->addresses commtt)))
   :other (committee-fix commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-committee-with-transaction-list ((transs transaction-listp)
                                                (commtt committeep))
  :returns (new-commtt committeep)
  :short "Update a committee with a list of transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We update the committee with each transaction in the list,
     from left to right."))
  (b* (((when (endp transs)) (committee-fix commtt))
       (commtt (update-committee-with-transaction (car transs) commtt)))
    (update-committee-with-transaction-list (cdr transs) commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-after-blocks ((blocks block-listp))
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
     to arrive at the resulting committee."))
  (b* (((when (endp blocks)) (genesis-committee))
       (commtt (committee-after-blocks (cdr blocks))))
    (update-committee-with-transaction-list (block->transactions (car blocks))
                                            commtt))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bonded-committee-at-round ((round posp) (blocks block-listp))
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
     so we have two choices for the bonded committee at round 2:
     it could be still the genesis committee,
     or it could be the new committee after the block;
     this depends on whether we consider the new committee
     to be bonded at the beginning or at the end of round 2.
     The same kind of choice applies to any other even round
     with a block that changes the committee;
     on the other hand, it is always clear
     what the bonded committee at an odd round is,
     and also at even rounds without blocks
     or with blocks that do not change the committee.")
   (xdoc::p
    "There seems to be no real criterion to choose between the two options,
     and it probably does not matter, but we will establish whether it does
     as we develop formal proofs.
     For now, we choose to change committee at the end of the even round.
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
     the @('blocks') input forming a well-formed blockchain."))
  (b* ((last (if (consp blocks)
                 (block->round (car blocks))
               0))
       ((when (> (pos-fix round)
                 (+ 2 last))) nil))
    (bonded-committee-at-round-loop round blocks))
  :hooks (:fix)

  :prepwork
  ((define bonded-committee-at-round-loop ((round posp) (blocks block-listp))
     :returns (commtt committeep)
     :parents nil
     (b* (((when (endp blocks)) (genesis-committee))
          ((when (> (pos-fix round)
                    (block->round (car blocks))))
           (committee-after-blocks blocks)))
       (bonded-committee-at-round-loop round (cdr blocks)))
     :hooks (:fix)))

  ///

  (defruled bonded-committee-at-earlier-round-when-at-later-round
    (implies (and (bonded-committee-at-round later blocks)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (bonded-committee-at-round earlier blocks))))

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
     by going sufficiently back in rounds (e.g. @('B = 100'),
     all validators should have blocks for those rounds,
     and should be able to calculate (and agree on)
     the committee bonded at those rounds.
     This is an assumption, which should be subjected to more formal study,
     but it is the rationale behind the approach.")
   (xdoc::p
    "Since @('B') is fixed and globally known,
     we introduce a constrained nullary function that returns it.
     There is no need to pick a specific value in this model;
     this way, the model is more general.
     Should the need arise to prove properties that depend on
     specific values of @('B'), or more generally on @('B') be in certain range,
     those can be made into hypotheses of such theorems."))

  (encapsulate
    (((lookback) => *))

    (local (defun lookback () 1))

    (defrule posp-of-lookback
      (posp (lookback))
      :rule-classes (:rewrite :type-prescription))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define active-committee-at-round ((round posp) (blocks block-listp))
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
     (i.e. it would be 0 or negative, before round 1).")
   (xdoc::p
    "This ACL2 function formalizes this notion of active committee.
     The exact notion of `being in charge of a round'
     must of course be formalized, which we are doing in this model.
     It should make intuitive sense,
     but there may be subtle details involved.
     Ultimately, we need certain high-level properties,
     such as the non-forking of blockchains,
     to be provable (and proved) in this formal model;
     those will guide our fleshing out of the necessary details.")
   (xdoc::p
    "Note that there is no guarantee that there is a bonded committee
     at round @('R - B'), where @('R') is the round of interest.
     Thus, this function returns an optional committee,
     @('nil') if no committee is available."))
  (if (> (pos-fix round) (lookback))
      (bonded-committee-at-round (- (pos-fix round) (lookback)) blocks)
    (genesis-committee))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled active-committee-at-earlier-round-when-at-later-round
    (implies (and (active-committee-at-round later blocks)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (active-committee-at-round earlier blocks))
    :enable (bonded-committee-at-earlier-round-when-at-later-round
             posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-faulty-for-total ((total natp))
  :returns (max natp
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
     @($f$), and hence @($f$), must be 0.
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

  (defret max-faulty-for-total-upper-bound-tight
    (>= (1+ max) (/ total 3))
    :hyp (not (zp total))
    :rule-classes ((:linear
                    :trigger-terms ((1+ (max-faulty-for-total total))))))

  (defrule total-lower-bound-wrt-max-faulty
    (implies (not (zp total))
             (>= total
                 (1+ (* 3 (max-faulty-for-total total)))))
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total)))))

  (defret max-faulty-for-total-leq-total
    (<= max (nfix total))
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total))))
    :hints (("Goal" :in-theory (enable nfix))))

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
  :returns (total natp)
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
  (set::cardinality (committee->addresses commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-max-faulty ((commtt committeep))
  :returns (maxf natp)
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
  :returns (quorum natp
                   :hints (("Goal" :in-theory (enable natp
                                                      nfix
                                                      committee-max-faulty))))
  :short "Quorum of validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the BFT literature, the quorum number is @($n - f$),
     where @($n$) and @($f$) are the numbers explained
     in @(tsee max-faulty-for-total).
     As @($n$) and @($f$) are functions of the committee,
     the quorum number is a function of the committee too."))
  (- (committee-total commtt)
     (committee-max-faulty commtt))
  :hooks (:fix))
