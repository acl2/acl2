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

(include-book "blocks")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "library-extensions/oset-theorems"))
(local (include-book "library-extensions/omap-theorems"))

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
     as proved elsewhere.")
   (xdoc::p
    "In our model a committee consists of
     a finite map from validator addresses to their bonded stake,
     the latter expressed as a positive integer
     whose exact units are irrelevant (cf. @(tsee transaction)).
     We introduce a fixtype to wrap that,
     for greater abstraction and extensibility.")
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
     The exact choice should not actually matter to correctness:
     so long as committees are used consistently,
     the two key intersection arguments for correctness,
     namely quorum intersection and successor-predecessor intersection,
     should work fine either way.")
   (xdoc::p
    "The other notion is that of the committee active at each round,
     i.e. the committee that is in charge of that round.
     This is the lookback committee: it is the bonded committee
     at a fixed number of previous rounds (``lookback'').
     The choice of when a bonded committee starts vs. ends discussed above
     affects the choice of when an active committee starts vs. ends.")
   (xdoc::p
    "Committees are not explicit components of the "
    (xdoc::seetopic "system-states" "system states")
    ", but they are, in a way, derived components of validator states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()

  (set-induction-depth-limit 1)

  (fty::defomap address-pos-map
    :short "Fixtype of maps from addresses to positive integers."
    :key-type address
    :val-type pos
    :pred address-pos-mapp

    ///

    (defrule address-setp-of-keys-when-address-pos-mapp
      (implies (address-pos-mapp map)
               (address-setp (omap::keys map)))
      :induct t
      :enable omap::keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod committee
  :short "Fixtype of committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our model, a committee is a map from addresses to bonded stake
     (the latter modeled as positive integers),
     but we wrap it in a fixtype for greater abstraction and extensibility."))
  ((members-with-stake address-pos-map))
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
    "The members of a committees are the keys of the map."))
  (omap::keys (committee->members-with-stake commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-nonemptyp ((commtt committeep))
  :returns (yes/no booleanp)
  :short "Check is a committee is not empty."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether it has members."))
  (not (set::emptyp (committee-members commtt)))
  :hooks (:fix)

  ///

  (defruled committee-nonemptyp-when-nonempty-subset
    (implies (and (set::subset members (committee-members commtt))
                  (not (set::emptyp members)))
             (committee-nonemptyp commtt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-member-stake ((member addressp) (commtt committeep))
  :guard (set::in (address-fix member) (committee-members commtt))
  :returns (stake posp :rule-classes (:rewrite :type-prescription))
  :short "Stake of a member of the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the member's address in the map."))
  (pos-fix (omap::lookup (address-fix member)
                         (committee->members-with-stake commtt)))
  :guard-hints (("Goal" :in-theory (enable committee-members
                                           omap::in-of-keys-to-assoc)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-members-stake ((members address-setp) (commtt committeep))
  :guard (set::subset members (committee-members commtt))
  :returns (stake natp)
  :short "Total stake of a set of members of the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add up all the stakes of the members.")
   (xdoc::p
    "We prove various properties that relate this function to set operations.")
   (xdoc::p
    "The monotonicity property uses a (locally defined) custom induction,
     which removes from the second set the head of the first set
     in the recursive call, when the first set is not empty;
     this is needed to exclude the stake of that committee member
     (if present in the second set of committee members)
     in the induction hypothesis.")
   (xdoc::p
    "The union expansion property is analogous to
     the property of cardinalities of sets,
     but with stake in this case.
     The total stake of the union of two sets is their sum,
     minus the stake of the intersection (if any),
     which the sum union counts twice."))
  (cond ((set::emptyp (address-set-fix members)) 0)
        (t (+ (committee-member-stake (address-fix (set::head members)) commtt)
              (committee-members-stake (set::tail members) commtt))))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :guard-hints (("Goal" :in-theory (enable set::subset)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (more-returns
   (stake posp
          :hyp (not (set::emptyp (address-set-fix members)))
          :rule-classes (:rewrite :type-prescription)
          :hints (("Goal" :induct t))))

  (defruled committee-members-stake-0-to-emptyp-members
    (equal (equal (committee-members-stake members commtt) 0)
           (set::emptyp (address-set-fix members)))
    :induct t
    :enable fix)

  (defrule committee-members-stake-when-emptyp-members
    (implies (set::emptyp members)
             (equal (committee-members-stake members commtt)
                    0)))

  (defruled committee-members-stake-of-insert
    (implies (and (addressp member)
                  (address-setp members))
             (equal (committee-members-stake (set::insert member members)
                                             commtt)
                    (if (set::in member members)
                        (committee-members-stake members commtt)
                      (+ (committee-member-stake member commtt)
                         (committee-members-stake members commtt)))))
    :induct (set::weak-insert-induction member members)
    :enable set::expensive-rules)

  (defruled committee-members-stake-of-delete
    (implies (address-setp members)
             (equal (committee-members-stake (set::delete member members)
                                             commtt)
                    (if (set::in member members)
                        (- (committee-members-stake members commtt)
                           (committee-member-stake member commtt))
                      (committee-members-stake members commtt))))
    :induct t
    :enable (set::delete
             committee-members-stake-of-insert))

  (defruled committee-members-stake-monotone
    (implies (and (address-setp members1)
                  (address-setp members2)
                  (set::subset members1 members2))
             (<= (committee-members-stake members1 commtt)
                 (committee-members-stake members2 commtt)))
    :induct (ind members1 members2)
    :enable (set::subset-of-tail-and-delete-when-subset
             committee-members-stake-of-delete
             set::expensive-rules)
    :prep-lemmas
    ((defun ind (x y)
       (declare (irrelevant y))
       (cond ((set::emptyp x) nil)
             (t (ind (set::tail x) (set::delete (set::head x) y)))))))

  (defruled committee-members-stake-of-union
    (implies (and (address-setp members1)
                  (address-setp members2))
             (equal (committee-members-stake (set::union members1
                                                         members2)
                                             commtt)
                    (- (+ (committee-members-stake members1 commtt)
                          (committee-members-stake members2 commtt))
                       (committee-members-stake (set::intersect members1
                                                                members2)
                                                commtt))))
    :induct t
    :enable (committee-members-stake-of-insert
             set::union
             set::intersect
             fix))

  (defruled committee-members-stake-of-intersect
    (implies (and (address-setp members1)
                  (address-setp members2))
             (equal (committee-members-stake (set::intersect members1
                                                             members2)
                                             commtt)
                    (- (+ (committee-members-stake members1 commtt)
                          (committee-members-stake members2 commtt))
                       (committee-members-stake (set::union members1
                                                            members2)
                                                commtt))))
    :enable committee-members-stake-of-union
    :disable committee-members-stake)

  (theory-invariant
   (incompatible (:rewrite committee-members-stake-of-union)
                 (:rewrite committee-members-stake-of-intersect)))

  (defruled committee-members-stake-of-difference
    (implies (and (address-setp members1)
                  (address-setp members2))
             (equal (committee-members-stake (set::difference members1
                                                              members2)
                                             commtt)
                    (- (committee-members-stake (set::union members1
                                                            members2)
                                                commtt)
                       (committee-members-stake members2
                                                commtt))))
    :induct t
    :enable (set::difference
             set::union
             committee-members-stake-of-insert)))

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
       (make-committee :members-with-stake nil)))

    (defrule committeep-of-genesis-committee
      (committeep (genesis-committee)))))

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
     A bonding transaction has a different effect
     depending on whether the validator is already in the committee or not:
     if it is not already in the committee,
     it is added to the committee,
     with associated the stake indicated in the transaction;
     if the validator is already in the committee,
     its associated stake is increased by
     the amount indicated in the transaction.
     An unbonding transaction removes the validator from the committee,
     along with its stake;
     there is no change if the validator is not in the committee.
     The other kind of transaction leaves the committee unchanged.")
   (xdoc::p
    "It is an interesting question whether an AleoBFT implementation
     should have mechanisms in place to guarantee minimal committee sizes.
     If it does not, which is plausible since validators
     should be generally free to bond and unbond as they want,
     then the whole network could be considered to fail
     if all validators unbond and there is nobody to run the network."))
  (transaction-case
   trans
   :bond (b* ((members-with-stake (committee->members-with-stake commtt))
              (member-with-stake (omap::assoc trans.validator
                                              members-with-stake))
              (new-stake (if member-with-stake
                             (+ trans.stake (cdr member-with-stake))
                           trans.stake))
              (new-members-with-stake (omap::update trans.validator
                                                    new-stake
                                                    members-with-stake)))
           (committee new-members-with-stake))
   :unbond (b* ((members-with-stake (committee->members-with-stake commtt))
                (new-members-with-stake (omap::delete trans.validator
                                                      members-with-stake)))
             (committee new-members-with-stake))
   :other (committee-fix commtt))
  :hooks (:fix)

  :prepwork

  ((defrulel verify-guards-lemma1
     (implies (and (posp x)
                   (posp y))
              (posp (+ x y))))

   (defrulel verify-guards-lemma2
     (implies (posp x)
              (acl2-numberp x)))))

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
     but it can be regarded as a pseudo-round number.
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
    "Among other properties, we prove that
     if a round has a bonded committeed,
     then every round before that round does as well.
     We also show that extending a blockchain
     does not affect the bonded committee at rounds
     that have a bonded committee calculable from the original blockchain."))
  (b* (((when (> (pos-fix round)
                 (+ 2 (blocks-last-round blocks))))
        nil))
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
     :hooks (:fix)

     ///

     (defruled bonded-committee-at-round-loop-when-no-blocks
       (implies (endp blocks)
                (equal (bonded-committee-at-round-loop round blocks)
                       (genesis-committee))))

     (defruled bonded-committee-at-round-loop-of-round-leq-2
       (implies (and (blocks-ordered-even-p blocks)
                     (<= (pos-fix round) 2))
                (equal (bonded-committee-at-round-loop round blocks)
                       (genesis-committee)))
       :induct t
       :hints ('(:use evenp-of-car-when-blocks-ordered-even-p)))

     (defruled bonded-committee-at-round-loop-of-append-no-change
       (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                     (or (endp blocks1)
                         (<= (pos-fix round)
                             (block->round (car (last blocks1))))))
                (equal (bonded-committee-at-round-loop round
                                                       (append blocks1 blocks))
                       (bonded-committee-at-round-loop round blocks)))
       :induct t
       :enable (blocks-ordered-even-p-of-append
                last)
       :hints ('(:use (:instance newest-geq-oldest-when-blocks-ordered-even-p
                                 (blocks blocks1)))))))

  ///

  (defruled bonded-committee-at-round-when-no-blocks
    (implies (endp blocks)
             (b* ((commtt (bonded-committee-at-round round blocks)))
               (implies commtt
                        (equal commtt (genesis-committee)))))
    :enable bonded-committee-at-round-loop-when-no-blocks)

  (defruled bonded-committee-at-round-of-round-leq-2
    (implies (and (blocks-ordered-even-p blocks)
                  (<= (pos-fix round) 2))
             (equal (bonded-committee-at-round round blocks)
                    (genesis-committee)))
    :enable bonded-committee-at-round-loop-of-round-leq-2)

  (defruled bonded-committee-at-round-of-append-no-change
    (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                  (bonded-committee-at-round round blocks))
             (equal (bonded-committee-at-round round
                                               (append blocks1 blocks))
                    (bonded-committee-at-round round blocks)))
    :enable (blocks-last-round
             blocks-ordered-even-p-of-append
             bonded-committee-at-round-loop-of-append-no-change
             bonded-committee-at-round-loop-of-round-leq-2)
    :hints ('(:use ((:instance newest-geq-oldest-when-blocks-ordered-even-p
                               (blocks blocks1))))))

  (defruled bonded-committee-at-earlier-round-when-at-later-round
    (implies (and (bonded-committee-at-round later blocks)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (bonded-committee-at-round earlier blocks)))

  (defruled bonded-committee-at-round-iff-round-upper-bound
    (iff (bonded-committee-at-round round blocks)
         (<= (pos-fix round)
             (+ 2 (blocks-last-round blocks))))))

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
     (i.e. it would be 0 or negative, before round 1).
     This ACL2 function formalizes this notion of active committee.")
   (xdoc::p
    "Note that there is no guarantee that there is a bonded committee
     at round @('R - B'), where @('R') is the round of interest.
     Thus, this function returns an optional committee,
     @('nil') if no committee is available.")
   (xdoc::p
    "We prove some properties of active committees
     analogous to certain properties of bonded committees,
     using in fact those previously proved theorems in the proofs.
     We also prove some specializations of the theorem that says that
     if a round has an active committee
     then every round before that round does as well;
     the specializations are for the 1, 2, and 3 rounds before."))
  (if (> (pos-fix round) (lookback))
      (bonded-committee-at-round (- (pos-fix round) (lookback))
                                 blocks)
    (genesis-committee))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled active-committee-at-round-when-no-blocks
    (implies (endp blocks)
             (b* ((commtt (active-committee-at-round round blocks)))
               (implies commtt
                        (equal commtt (genesis-committee)))))
    :enable bonded-committee-at-round-when-no-blocks)

  (defruled active-committee-at-round-of-round-leq-2+lookback
    (implies (and (blocks-ordered-even-p blocks)
                  (<= (pos-fix round) (+ 2 (lookback))))
             (equal (active-committee-at-round round blocks)
                    (genesis-committee)))
    :enable (bonded-committee-at-round-of-round-leq-2
             posp))

  (defruled active-committee-at-round-of-append-no-change
    (implies (and (blocks-ordered-even-p (append blocks1 blocks))
                  (active-committee-at-round round blocks))
             (equal (active-committee-at-round round
                                               (append blocks1 blocks))
                    (active-committee-at-round round blocks)))
    :enable bonded-committee-at-round-of-append-no-change)

  (defruled active-committee-at-earlier-round-when-at-later-round
    (implies (and (active-committee-at-round later blocks)
                  (< (pos-fix earlier)
                     (pos-fix later)))
             (active-committee-at-round earlier blocks))
    :enable (bonded-committee-at-earlier-round-when-at-later-round
             posp))

  (defruled active-committee-at-previous-round-when-at-round
    (implies (and (active-committee-at-round round blocks)
                  (> (pos-fix round) 1))
             (active-committee-at-round (1- round) blocks))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (1- round)))
    :enable pos-fix)

  (defruled active-committee-at-previous2-round-when-at-round
    (implies (and (active-committee-at-round round blocks)
                  (> (pos-fix round) 2))
             (active-committee-at-round (- round 2) blocks))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (- round 2)))
    :enable pos-fix)

  (defruled active-committee-at-previous3-round-when-at-round
    (implies (and (active-committee-at-round round blocks)
                  (> (pos-fix round) 3))
             (active-committee-at-round (- round 3) blocks))
    :disable active-committee-at-round
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later round)
                    (earlier (- round 3)))
    :enable pos-fix)

  (defruled active-committee-at-round-iff-round-upper-bound
    (iff (active-committee-at-round round blocks)
         (<= (nfix (- (pos-fix round) (lookback)))
             (+ 2 (blocks-last-round blocks))))
    :enable (bonded-committee-at-round-iff-round-upper-bound
             nfix
             pos-fix
             posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-faulty-for-total ((total natp))
  :returns (max natp
                :rule-classes (:rewrite :type-prescription)
                :hints (("Goal" :in-theory (enable natp zp))))
  :short "Maximum number of units of stake associated to faulty validators,
          out of a total, for the protocol to be fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classic BFT condition for fault tolerance is that
     the number of faulty participants is (strictly) less than
     one third of the total number of participants:
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
    "In AleoBFT, the participants are not fixed,
     because they are the members of the changing committee;
     so @($n$) and @($f$) vary with the committee.
     Furthermore, AleoBFT uses not numbers of validators,
     but units of stake associated to the validators;
     thus @($n$) is the sum of the units of stake
     of all the validators in the committee,
     and @($f$) is the maximim sum of the units of stake
     of the faulty validators in the committee.")
   (xdoc::p
    "The distinction between the maximum @($f$)
     and possibly smaller values of @($f$)
     is worth emphasizing,
     because recent BFT literature
     does not always state things clearly in this respect.
     The stake associated to the faulty validators in a committee
     is not something that validators know,
     because validators do not know which validators are faulty.
     In contrast, the stake @($n$) associated to
     all the validators in a committee is known,
     because the committee is known (calculated from the blockchain).
     Thus the maximum @($f$) satisfying @($f < n/3$)
     can be calculated from @($n$).
     So when a validator needs to use @($f$) in some computation,
     it is the maximum such @($f$), calculable from @($n$),
     not the (unknowable to the validator)
     stake of the faulty validators in the committee.")
   (xdoc::p
    "Some BFT literature uses phrases like
     ``up to @($f < n/3$) faulty validators'',
     implying that @($f$) is another parameter of the system, besides @($n$).
     But when validators need to use @($f$) as part of their computation,
     as is the case for AleoBFT,
     it makes more sense for @($f$) to be the maximum value
     that satisfies the inequality,
     because it allows for the maximum possible stake faulty validators.
     So in our model @($f$) is always that maximum,
     and it is calculable from @($n$).")
   (xdoc::p
    "This ACL2 function performs this calculation.
     The input @('total') is @($n$),
     and the output is the maximum @($f$) such that @($f < n/3$).
     We define the function to return 0 if @($n = 0$),
     although @($n = 0$) does not correspond to a practical situation.
     So consider the normal case @($n > 0$).
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
     and that one more than that is not below @($n/3$):
     that is, we prove that it returns the maximum.
     We could have alternatively defined this function in terms of maximum,
     via a recursion to find it, or even in a non-executable way,
     but instead we pick the definition with ceiling,
     and prove it equivalent to the other two possible definitions.
     We also prove that @($n \\geq 3f + 1$) when @($n \\neq 0$),
     that @($n \\geq f$) even if @($n = 0$),
     that @($n > f$) when @($n \\neq 0$),
     and that @($f < n - f$) when @($n \\neq 0$);
     in the latter, the significance of @($n - f$) is that
     it is the quorum, corresponding to @($f$),
     necessary for fault tolerance conditions.")
   (xdoc::p
    "If @($n$) is 1 or 2 or 3, no failures are tolerated:
     @($f$) must be 0.
     The case @($n = 1$) is a degenerate one,
     but the protocol could probably still work in a degenerate way.
     The cases @($n = 2$) and @($n = 3$) could make sense,
     but since they tolerate no failures,
     they are not used in practice.
     If @($n$) is 4 or more, we can tolerate
     an increasing amount of faulty validators,
     any amount whose stake is less than or equal to $f$,
     so that is usually the practical minimum for @($n$)."))
  (if (zp total)
      0
    (1- (ceiling total 3)))

  ///

  (fty::deffixequiv max-faulty-for-total
    :hints (("Goal" :in-theory (enable nfix))))

  (defruled max-faulty-for-total-alt-def
    (equal (max-faulty-for-total total)
           (if (zp total)
               0
             (floor (1- total) 3))))

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
    (<= max total)
    :hyp (natp total)
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total))))
    :hints (("Goal" :in-theory (enable nfix))))
  (in-theory (disable max-faulty-for-total-leq-total))

  (defret max-faulty-for-total-lt-total
    (< max total)
    :hyp (posp total)
    :rule-classes ((:linear :trigger-terms ((max-faulty-for-total total))))
    :hints (("Goal" :in-theory (enable posp))))
  (in-theory (disable max-faulty-for-total-lt-total))

  (defret max-faulty-for-total-lt-quorum
    (< max (- total max))
    :hyp (posp total)
    :rule-classes :linear)
  (in-theory (disable max-faulty-for-total-lt-quorum))

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

(define committee-total-stake ((commtt committeep))
  :returns (total natp :rule-classes (:rewrite :type-prescription))
  :short "Total stake of validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @($n$), using the notation in @(tsee max-faulty-for-total).
     It is the sum of all the units of stake
     associated to members of the committee."))
  (committee-members-stake (committee-members commtt) commtt)
  :hooks (:fix)

  ///

  (more-returns
   (total posp
          :hyp (committee-nonemptyp commtt)
          :rule-classes (:rewrite :type-prescription)
          :hints (("Goal" :in-theory (enable committee-nonemptyp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-max-faulty-stake ((commtt committeep))
  :returns (maxf natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum tolerated stake of faulty validators in a committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($f$) discussed in @(tsee max-faulty-for-total)
     applies to a committee, not to the whole system,
     in the same way as @($n$)."))
  (max-faulty-for-total (committee-total-stake commtt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committee-quorum-stake ((commtt committeep))
  :returns (quorum natp
                   :rule-classes (:rewrite :type-prescription)
                   :hints (("Goal"
                            :in-theory
                            (enable natp
                                    committee-max-faulty-stake
                                    max-faulty-for-total-leq-total))))
  :short "Quorum stake in a committee."
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
     works for any value of @($n$).")
   (xdoc::p
    "If the committee is not empty,
     the maximum tolerated faulty stake
     is less than the quorum stake."))
  (- (committee-total-stake commtt)
     (committee-max-faulty-stake commtt))
  :hooks (:fix)

  ///

  (more-returns
   (quorum posp
           :hyp (committee-nonemptyp commtt)
           :rule-classes (:rewrite :type-prescription)
           :hints
           (("Goal" :in-theory (enable posp
                                       committee-max-faulty-stake
                                       max-faulty-for-total-lt-total)))))

  (defruled committee-max-faulty-stake-lt-committee-quorum-stake
    (implies (committee-nonemptyp commtt)
             (< (committee-max-faulty-stake commtt)
                (committee-quorum-stake commtt)))
    :rule-classes :linear
    :enable (committee-max-faulty-stake
             max-faulty-for-total-lt-quorum)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-bonded-committees-p ((blocks1 block-listp)
                                     (blocks2 block-listp))
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
                   (b* ((commtt1 (bonded-committee-at-round round blocks1))
                        (commtt2 (bonded-committee-at-round round blocks2)))
                     (implies (and commtt1
                                   commtt2)
                              (equal commtt1 commtt2)))))
  ///
  (fty::deffixequiv-sk same-bonded-committees-p
    :args ((blocks1 block-listp) (blocks2 block-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-active-committees-p ((blocks1 block-listp)
                                     (blocks2 block-listp))
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
                   (b* ((commtt1 (active-committee-at-round round blocks1))
                        (commtt2 (active-committee-at-round round blocks2)))
                     (implies (and commtt1
                                   commtt2)
                              (equal commtt1 commtt2)))))
  ///
  (fty::deffixequiv-sk same-active-committees-p
    :args ((blocks1 block-listp) (blocks2 block-listp))))
