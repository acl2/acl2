; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "ordered-even-blocks")
(include-book "nonforking-blockchains-def-and-init")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ same-committees-def-and-implied
  :parents (correctness)
  :short "Invariant that correct validators calculate the same committees:
          definition, and proof that it is implied by other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the definition of the labeled state transition systems,
     each validator calculates the (active) committee at each round
     using its own copy of the blockchain.
     If blockchains do not fork, then any two correct validators
     that can both calculate an active committee at a round,
     will in fact compute the same active committee at that round.")
   (xdoc::p
    "Here we formulate this invariant,
     and we prove that it is a consequence of
     the invariant that blockchains do not non fork.
     We also need the already proved invariant that
     rounds in blockchains are even and strictly increasing.")
   (xdoc::p
    "If the blockchains of two validators do not fork,
     either the two blockchains are equal
     or one extends the other:
     see @(tsee nonforking-blockchains-p) and @(tsee lists-noforkp).
     If the two blockchains are equal,
     clearly the same committees are calculated from them.
     If one is an extension of the other,
     they will still agree on the committees that they both calculate,
     because those are based only on the the blocks
     that are common to the two blockchains.
     The longer blockchain can calculate more committees (at later rounds),
     but the invariant that we prove here only concerns
     the committees that both blockchains can calculate.")
   (xdoc::p
    "Our proof fleshes out the details of the argument sketched above,
     which require some care.
     The interesting case for the proof is that of
     a longer blockchain that extends a shorter blockchain,
     since the case of two equal blockchains is easy.
     The calculation of the two committees can be rephrased in terms of
     a trimming operation applied to the blockchains.
     We define the trimming operation to remove
     the blocks that are not needed to calculate
     the (bonded) committee at a given round.
     Our rephrased calculations of the two committees
     trims the blockchains not quite at the round for the committee,
     but at the even round after the last round of the shorter blockchain,
     which is also the smallest round of the blocks
     that extend the shorter blockchain to become the longer blockchain
     (this may be clearer looking at the actual formulas).
     We show that trimming the shorter blockchain does not change it,
     and that trimming the longer blockchain
     yields exactly the shorter blockchain.
     Thus the two calculations have been reduced to be on equal blockchains,
     and therefore they must return the same committees.
     This is all for bonded committees,
     but the same easily follows for active committees,
     which are defined in terms of bonded committees.")
   (xdoc::p
    "Here we define the invariant,
     and we prove that is is implied by other invariants.
     Elsewhere we prove that
     this invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-committees-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for any two correct validators in the system,
          if they both calculate an active committee at a round,
          compute the same active committee at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that no requirement applies if
     only one validator can calculate the committee but not the other.
     A validator may be ahead of another one."))
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (same-active-committees-p
                    (validator-state->blockchain
                     (get-validator-state val1 systate))
                    (validator-state->blockchain
                     (get-validator-state val2 systate)))))
  ///
  (fty::deffixequiv-sk same-committees-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-committees-list-extension-equivalences
  :short "Equivalence between two ways to phrase list extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see same-committees-def-and-implied),
     the interesting case of the proof is that of
     a longer blockchain extending a shorter blockchain.
     In @(tsee lists-noforkp),
     the extension is expressed in terms of @(tsee nthcdr).
     However, for some of our proofs,
     a formulation in terms of @(tsee append) is more convenient.
     Here we provide a bridge between the two formulations.")
   (xdoc::p
    "We also prove an equivalence (really, an implication) between
     two ways to address the rightmost element of the extension.
     The extension is the @('(take ...)') term in the formula,
     and the two ways of addressing the rightmost element are
     as the last one of the extension and
     as the @(tsee nth) of the longer list.")
   (xdoc::p
    "This is really a generic theorem about lists,
     not specific to AleoBFT.
     We could consider putting it into a library,
     ideally in some more general form.
     Or perhaps there is a way to use more general list theorems
     in the proofs of this invariant."))
  (implies (and (< (len list1) (len list2))
                (equal list1
                       (nthcdr (- (len list2)
                                  (len list1))
                               list2)))
           (and (equal (append (take (- (len list2)
                                        (len list1))
                                     list2)
                               list1)
                       list2)
                (equal (nth (1- (- (len list2)
                                   (len list1)))
                            list2)
                       (car (last (take (- (len list2)
                                           (len list1))
                                        list2))))))
  :induct  (len list2)
  :enable (len nthcdr last nth fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define trim-blocks-for-round ((round posp) (blocks block-listp))
  :returns (trimmed-blocks block-listp)
  :short "Trim a blockchain to what is needed
          to calculate the (bonded) committee at a given round."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the definition of @(tsee bonded-committee-at-round),
     the calculation of the bonded committee at a round
     only depends on the blocks before that round.
     It does not depend on the blocks after that round,
     or on the block (if any) at that round.")
   (xdoc::p
    "This function removes from a list of blocks
     all the ones whose round is less than or equal to a given round.
     More precisely, it does that when the blocks are ordered
     (i.e. when they satisfy @(tsee blocks-ordered-even-p)).
     But we do not require the ordering here,
     and just remove blocks until we find one
     whose round is below the given round."))
  (b* (((when (endp blocks)) nil)
       ((when (> (pos-fix round)
                 (block->round (car blocks))))
        (block-list-fix blocks)))
    (trim-blocks-for-round round (cdr blocks)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled trim-blocks-for-round-no-change
  :short "Trimming a blockchain to a round after the last one
          causes no change."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that we use @(tsee blocks-last-round),
     so we allow the blockchain to be empty,
     in which case we consider its last round to be 0.
     Given the way @(tsee trim-blocks-for-round) is defined,
     if the round is after the last one,
     no block is removed.")
   (xdoc::p
    "With reference to the explanation in
     @(see same-committees-def-and-implied),
     this theorem will be used to show that
     trimming the shorter blockchain does not change it."))
  (implies (> (pos-fix round)
              (blocks-last-round blocks))
           (equal (trim-blocks-for-round round blocks)
                  (block-list-fix blocks)))
  :enable (trim-blocks-for-round
           blocks-last-round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled trim-blocks-for-round-of-append-yields-first
  :short "Trimming an extended blockchain to
          the smallest round of the extension
          yields the shorter blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to show that
     trimming the longer blockchain yields the shorter blockchain.
     We use the formulation with @(tsee append),
     where @('blocks2') is the shorter blockchain,
     @('blocks1') is the extension,
     and the @(tsee append) is the longer blockchain.
     The cutoff round is the smallest one of the extension.
     Here we need to assume that block rounds are ordered
     (in the longer blockchain, which implies that
     they are also ordered in the extension and in the smaller blockchain)."))
  (implies (and (blocks-ordered-even-p (append blocks1 blocks2))
                (consp blocks1))
           (equal (trim-blocks-for-round (block->round (car (last blocks1)))
                                         (append blocks1 blocks2))
                  (block-list-fix blocks2)))
  :induct t
  :enable (trim-blocks-for-round
           blocks-ordered-even-p
           last
           blocks-ordered-even-p-of-append)
  :hints ('(:use (:instance newest-geq-oldest-when-blocks-ordered-even-p
                            (blocks (cdr blocks1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bonded-committee-at-round-loop-to-trim-blocks-for-round
  :short "Rephrasing of @(tsee bonded-committee-at-round)
          in terms of @(tsee trim-blocks-for-round);
          part 1 of 2."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we prove a theorem about @('bonded-committee-at-round-loop'),
     which is the auxialiary recursive function
     used to define @(tsee bonded-committee-at-round).
     The calculation of the committee at a round @('round')
     does not depend on blocks after or at that round.
     We formulate the theorem more generically,
     in terms of a round @('round1') that is at least @('round').
     This generalization is important to the use of this theorem later.
     Recall that blocks should be thought of having increasing rounds,
     even though that hypothesis is not necessary to prove this theorem.")
   (xdoc::p
    "This theorem does not have the form of a good a rewrite rule.
     We could swap the left and right sides of the equality,
     but the current form is more in line with the intuition behind the proof.
     The intuition is that, in order to prove our main claim,
     we expand the left side of this equality to its right side,
     for both the longer and shorter blockchains,
     and then we use theorems to simplify away the trimming operation,
     yielding the same blockchains (see proofs later).
     This is a case in which the simplest and more intuitive proof strategy
     temporarily goes against always ``simplifying'' things:
     we make things temporarily more complex
     just so that we can then simplify them to the same thing."))
  (implies (>= (pos-fix round1)
               (pos-fix round))
           (equal (bonded-committee-at-round-loop round blocks)
                  (bonded-committee-at-round-loop
                   round
                   (trim-blocks-for-round round1 blocks))))
  :induct t
  :enable (trim-blocks-for-round
           bonded-committee-at-round-loop))

;;;;;;;;;;;;;;;;;;;;

(defruled bonded-committee-at-round-to-trim-blocks-for-round
  :short "Rephrasing of @(tsee bonded-committee-at-round)
          in terms of @(tsee trim-blocks-for-round);
          part 2 of 2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the previous theorem to prove this one
     about @(tsee bonded-committee-at-round),
     which is the one we are interested in,
     and which we will use in further proofs.
     While @('bonded-committee-at-round-loop') always calculates a committee,
     @(tsee bonded-committee-at-round) has an initial check
     that the round is not too far ahead.
     So here we need an additional hypothesis that
     the committee is in fact calculable.
     This hypothesis will be satisfied in our main theorem:
     see the inner implication in @(tsee same-committees-p)."))
  (implies (and (bonded-committee-at-round round blocks)
                (>= (pos-fix round1)
                    (pos-fix round)))
           (equal (bonded-committee-at-round round blocks)
                  (bonded-committee-at-round-loop
                   round
                   (trim-blocks-for-round round1 blocks))))
  :use bonded-committee-at-round-loop-to-trim-blocks-for-round
  :enable bonded-committee-at-round)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled trim-blocks-for-round-of-longer
  :short "Result of trimming the longer blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is one of the main reasoning steps in our overall proof.
     As mentioned earlier, we expand the two committee calculations
     to include calls of @(tsee trim-blocks-for-round),
     which we then simplify to the same thing.
     This theorem simplifies the call for the longer blockchain.
     The relation between longer and shorter blockchains
     is expressed in terms of @(tsee nthcdr),
     but the core theorem @(tsee trim-blocks-for-round-of-append-yields-first)
     uses the @(tsee append) formulation,
     so we use the theorem about list equivalences.")
   (xdoc::p
    "The theorem says that the trimming of the longer blockchain
     reduces to the shorter blockchain."))
  (implies (and (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (< (len blocks1) (len blocks2))
                (equal blocks1
                       (nthcdr (- (len blocks2)
                                  (len blocks1))
                               blocks2)))
           (equal (trim-blocks-for-round
                   (block->round (nth (1- (- (len blocks2)
                                             (len blocks1)))
                                      blocks2))
                   blocks2)
                  (block-list-fix blocks1)))
  :use ((:instance trim-blocks-for-round-of-append-yields-first
                   (blocks1 (take (- (len blocks2)
                                     (len blocks1))
                                  blocks2))
                   (blocks2 (nthcdr (- (len blocks2)
                                       (len blocks1))
                                    blocks2)))
        (:instance same-committees-list-extension-equivalences
                   (list1 blocks1)
                   (list2 blocks2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled trim-blocks-for-round-of-shorter
  :short "Result of trimming the shorter blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the counterpart of @(tsee trim-blocks-for-round-of-longer),
     but for the shorter blockchain.
     The result is the same, i.e. the shorter blockchain itself.
     The core theorem is @(tsee trim-blocks-for-round-no-change),
     which is expressed in terms of @(tsee append),
     so again we use the list equivalence theorem.
     We also need to appeal to the theorem that,
     in an ordered @('(append blocks1 blocks2)'),
     the oldest round of @('blocks1') is greater than
     the newest round of @('blocks2'),
     where we instantiate @('blocks1') and @('blocks2')
     with the appropriate extension and shorter block,
     as @('blocks1') and @('blocks2') have a different meaning
     in the theorem that we prove here.
     The appeal to that theorem is necessary to
     relieve the hypothesis of @(tsee trim-blocks-for-round-no-change).")
   (xdoc::p
    "The theorem says that the trimming of the shorter blockchain
     reduces to the shorter blockchain."))
  (implies (and (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (< (len blocks1) (len blocks2))
                (equal blocks1
                       (nthcdr (- (len blocks2)
                                  (len blocks1))
                               blocks2)))
           (equal (trim-blocks-for-round
                   (block->round (nth (1- (- (len blocks2)
                                             (len blocks1)))
                                      blocks2))
                   blocks1)
                  (block-list-fix blocks1)))
  :use
  ((:instance trim-blocks-for-round-no-change
              (round (block->round (nth (1- (- (len blocks2)
                                               (len blocks1)))
                                        blocks2)))
              (blocks blocks1))
   (:instance oldest-of-prefix-gt-newest-of-suffix-when-blocks-ordered-even-p
              (blocks1 (take (- (len blocks2)
                                (len blocks1))
                             blocks2))
              (blocks2 (nthcdr (- (len blocks2)
                                  (len blocks1))
                               blocks2)))
   (:instance same-committees-list-extension-equivalences
              (list1 blocks1)
              (list2 blocks2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-bonded-committees-longer-shorter
  :short "The longer and shorter blockchains calculate
          the same bonded committees, when they both do."
  :long
  (xdoc::topstring
   (xdoc::p
    "This proves most of what we need for our overall proof.
     The interesting case of the overall proof is when
     the two blockchains are not equal,
     but one is longer and the other is shorter.
     We express this relation using @(tsee nthcdr) here,
     as in @(tsee lists-noforkp).
     We make use of (two instances of)
     the theorem to expand the committee calculation
     to include a call of @(tsee trim-blocks-for-round),
     and the two theorems that simplify them
     (for longer and shorter blockchain).
     We also need, as a local lemma,
     the fact that the round of the oldest block of the extension
     is greater than the round of the newest block of the shorter blockchain,
     but expressed in terms of @(tsee nth) of the longer blockchain.
     We also need the fact that the rounds are not only ordered, but even:
     this ensures that there is a gap of at least 2
     between two block rounds where one is greater.")
   (xdoc::p
    "This proof, and its hints, is a bit more complex than ideal.
     Perhaps it can be simplified and streamlined a bit."))
  (implies (and (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (< (len blocks1) (len blocks2))
                (equal blocks1
                       (nthcdr (- (len blocks2)
                                  (len blocks1))
                               blocks2))
                (bonded-committee-at-round round blocks1)
                (bonded-committee-at-round round blocks2))
           (equal (bonded-committee-at-round round blocks1)
                  (bonded-committee-at-round round blocks2)))
  :use ((:instance bonded-committee-at-round-to-trim-blocks-for-round
                   (blocks blocks1)
                   (round1 (block->round (nth (1- (- (len blocks2)
                                                     (len blocks1)))
                                              blocks2))))
        (:instance bonded-committee-at-round-to-trim-blocks-for-round
                   (blocks blocks2)
                   (round1 (block->round (nth (1- (- (len blocks2)
                                                     (len blocks1)))
                                              blocks2))))
        trim-blocks-for-round-of-longer
        trim-blocks-for-round-of-shorter
        lemma
        (:instance evenp-of-nth-when-blocks-ordered-even-p
                   (blocks blocks2)
                   (i (1- (- (len blocks2)
                             (len blocks1)))))
        (:instance evenp-of-car-when-blocks-ordered-even-p
                   (blocks blocks1)))
  :enable (bonded-committee-at-round
           blocks-last-round
           nfix
           evenp)
  :prep-lemmas
  ((defruled lemma
     (implies (and (blocks-ordered-even-p blocks1)
                   (blocks-ordered-even-p blocks2)
                   (< (len blocks1) (len blocks2))
                   (equal blocks1
                          (nthcdr (- (len blocks2)
                                     (len blocks1))
                                  blocks2)))
              (> (block->round (nth (1- (- (len blocks2)
                                           (len blocks1)))
                                    blocks2))
                 (blocks-last-round blocks1)))
     :use ((:instance
            same-committees-list-extension-equivalences
            (list1 blocks1)
            (list2 blocks2))
           (:instance
            oldest-of-prefix-gt-newest-of-suffix-when-blocks-ordered-even-p
            (blocks1 (take (- (len blocks2)
                              (len blocks1))
                           blocks2))
            (blocks2 (nthcdr (- (len blocks2)
                                (len blocks1))
                             blocks2)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-active-committees-longer-shorter
  :short "The longer and shorter blockchains calculate
          the same active committees, when they both do."
  :long
  (xdoc::topstring
   (xdoc::p
    "So far we have dealt with bonded committees,
     because those have a more direct correspondence
     with the rounds of the blocks.
     But the validators really use active committees.")
   (xdoc::p
    "Transferring the proof to active committees is easy,
     because those are defined in terms of bonded committees.
     The theorem formulation is the same."))
  (implies (and (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (< (len blocks1) (len blocks2))
                (equal blocks1
                       (nthcdr (- (len blocks2)
                                  (len blocks1))
                               blocks2))
                (active-committee-at-round round blocks1)
                (active-committee-at-round round blocks2))
           (equal (active-committee-at-round round blocks1)
                  (active-committee-at-round round blocks2)))
  :enable (active-committee-at-round
           same-bonded-committees-longer-shorter))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-active-committees-when-nofork
  :short "Two non-forking blockchains calculate the same active committees,
          when they both do."
  :long
  (xdoc::topstring
   (xdoc::p
    "While @(tsee same-active-committees-longer-shorter)
     takes care of the interesting case of our overall proof,
     we need a proof for all cases, which we do here,
     using @(tsee lists-noforkp),
     whose expansion splits into three cases.
     The case of equal blockchains is trivial.
     The other two cases are symmetric,
     and handled by two firings of
     @(tsee same-active-committees-longer-shorter),
     one with @('blocks1') and @('blocks2') as in that theorem,
     and one with their roles swapped.")
   (xdoc::p
    "Instead of @('(equal A B)'),
     we phrase this theorem as @('(equal (equal A B) t)')
     so it can fire as a rewrite rule in the main theorem
     @(tsee same-committees-p-implied)."))
  (implies (and (lists-noforkp blocks1 blocks2)
                (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (active-committee-at-round round blocks1)
                (active-committee-at-round round blocks2))
           (equal (equal (active-committee-at-round round blocks1)
                         (active-committee-at-round round blocks2))
                  t))
  :enable (lists-noforkp
           same-active-committees-longer-shorter))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-committees-p-implied
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the proof of our invariant,
     from the other two invariants.
     The rewrite rules enabled in the hints take care of everything;
     also see the observation in @(tsee same-active-committees-when-nofork)
     about the particular form of that rewrite rule."))
  (implies (and (nonforking-blockchains-p systate)
                (ordered-even-p systate))
           (same-committees-p systate))
  :enable (same-committees-p
           same-active-committees-p
           nonforking-blockchains-p-necc
           ordered-even-p-necc
           same-active-committees-when-nofork))
