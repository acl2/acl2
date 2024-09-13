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

(include-book "elections")
(include-book "dags")

(local (include-book "std/lists/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ blockchains
  :parents (transitions)
  :short "Blockchains."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined in @(tsee validator-state),
     we model a blockchain as a list of blocks,
     growing from right to left (i.e. via @(tsee cons)).")
   (xdoc::p
    "Here we introduce operations on blockchains,
     specifically operations to extend blockchains.
     These operations are used to define what happens
     when a validator commits one or more anchors,
     each of which results in a block."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-anchors ((current-anchor certificatep)
                         (previous-round natp)
                         (last-committed-round natp)
                         (dag certificate-setp)
                         (blockchain block-listp)
                         (all-vals address-setp))
  :guard (and (evenp previous-round)
              (> (certificate->round current-anchor) previous-round)
              (or (zp previous-round)
                  (active-committee-at-round previous-round
                                             blockchain
                                             all-vals)))
  :returns (anchors certificate-listp)
  :short "Collect all the anchor certificates to commit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The starting point is an anchor, @('current-anchor')
     and an even round, @('previous-round'), that precedes the anchor.
     The recursion terminates when @('previous-round')
     reaches the last committed round:
     we return a singleton list with the current anchor.
     The last committed round is passed as input @('last-committed-round');
     it is initially 0, when there is no committed round yet.
     If @('previous-round') is larger than the @('last-committed-round'),
     we find the leader at @('previous-round'),
     and we use @(tsee path-to-author+round) to find the anchor, if any,
     at @('previous-round') reachable from the current anchor.
     If there is no such reachable previous anchor,
     we recursively examine the even round
     just before @('previous-round'),
     with the same @('current-anchor');
     in the recursion, we will be looking for longer paths,
     from the same @('current-anchor') to a round further behind.
     If there is an anchor at @('previous-round'),
     it becomes the new @('current-anchor'),
     and we recursively examine its previous even round,
     but since we changed @('current-anchor'),
     in the recursion DAG paths will be from the new @('current-anchor').
     The recursive call will return a list of anchors
     that includes the anchor passed as first argument.
     thus, when that anchor changes (i.e. when the previous anchor is found),
     we add the old @('current-anchor') to the list.
     The resulting list of anchors is in inverse chronological order:
     the leftmost anchor is the newest one (i.e. greatest round number);
     the rightmost anchor is the oldest one (i.e. smallest round number).")
   (xdoc::p
    "Since @('previous-round') eventually reaches @('last-committed-round')
     (at the end of the recursion),
     which is a natural number (i.e. a round number or 0),
     the @('previous-round') input of this ACL2 function
     is also a natural number (i.e. a round number or 0).")
   (xdoc::p
    "In order to calculate the leader at @('previous-round'),
     as it may also change during the recursion,
     we need to know the active committee at that round.
     So we pass the blockchain so far as an input to this function,
     and we require in the guard that the active committee
     is known at @('previous-round'),
     which implies that it is also known at smaller rounds.
     Note that this @('blockchain') input does not change in the recursion:
     it is simply the current blockchain,
     which this operation is not extending;
     this operation is just collecting the anchors
     with which the blockchain is (elsewhere) extended.
     It should be an invariant (not captured here)
     that @('last-committed-round') is in fact the round of the latest block
     (or 0 if the blockchain is empty);
     we plan to prove this invariant, as done for
     the model of AleoBFT with static committees.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "The returned list of anchors is never empty,
     and it always starts with (i.e. its @(tsee car) is)
     the @('current-anchor') input,
     as we prove below.")
   (xdoc::p
    "we also prove that the returned list of anchors has even,
     strictly increasing (right to left) round numbers,
     under suitable assumptions on some of the inputs.")
   (xdoc::p
    "We also show that the rounds of the returned anchors
     are all above the last committed round,
     provided that the round of the input anchor is.
     More precisely, we say that the lowest-numbered anchor round
     (i.e. the @(tsee car) of @(tsee last), i.e. the rightmost one)
     is above the last committed round.
     This assumption is satisfied when this function is called.
     Note that, since we also proved that rounds are strictly increasing,
     proving that the rightmost anchor has round above the last committed one
     implies that all the other anchors do as well;
     but in any case we need the theorem in this form,
     with @(tsee car) of @(tsee last),
     so it can be used to relieve the hypothesis
     in a theorem about @(tsee extend-blockchain)."))
  (b* (((unless (and (mbt (and (natp previous-round)
                               (evenp previous-round)
                               (natp last-committed-round)
                               (or (zp previous-round)
                                   (active-committee-at-round previous-round
                                                              blockchain
                                                              all-vals))
                               t))
                     (> previous-round last-committed-round)))
        (list (certificate-fix current-anchor)))
       (commtt (active-committee-at-round previous-round
                                          blockchain
                                          all-vals))
       (previous-leader (leader-at-round previous-round commtt))
       (previous-anchor? (path-to-author+round current-anchor
                                               previous-leader
                                               previous-round
                                               dag)))
    (if previous-anchor?
        (cons (certificate-fix current-anchor)
              (collect-anchors previous-anchor?
                               (- previous-round 2)
                               last-committed-round
                               dag
                               blockchain
                               all-vals))
      (collect-anchors current-anchor
                       (- previous-round 2)
                       last-committed-round
                       dag
                       blockchain
                       all-vals)))
  :measure (nfix previous-round)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix)))
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-earlier-round-when-at-later-round)))

  ///

  (more-returns
   (anchors consp :rule-classes :type-prescription))

  (defret car-of-collect-anchors
    (equal (car anchors)
           (certificate-fix current-anchor))
    :hints (("Goal" :induct t)))

  (in-theory (disable car-of-collect-anchors))

  (defret certificates-ordered-even-p-of-collect-anchors
    (certificates-ordered-even-p anchors)
    :hyp (and (evenp (certificate->round current-anchor))
              (evenp previous-round)
              (< previous-round
                 (certificate->round current-anchor)))
    :hints (("Goal"
             :induct t
             :in-theory (enable certificates-ordered-even-p
                                car-of-collect-anchors))))

  (in-theory (disable certificates-ordered-even-p-of-collect-anchors))

  (defret collect-anchors-above-last-committed-round
    (> (certificate->round (car (last anchors)))
       last-committed-round)
    :hyp (> (certificate->round current-anchor)
            last-committed-round)
    :hints (("Goal"
             :induct t
             :in-theory (enable last))))

  (in-theory (disable collect-anchors-above-last-committed-round)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transactions-from-certificates ((certs certificate-setp))
  :returns (transs transaction-listp)
  :short "Collect all the transactions from a set of certficates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When an anchor is committed,
     a new block is added to the blockchain,
     containing all the transactions from the anchor's causal history
     (which includes the anchor itself),
     except for the certificates whose transactions
     have already been added to the blockchain.
     After computing the set of certificates
     whose transactions must be included in a block,
     we call this function to put all those transactions together.
     We put them together according to the ACL2 total order on certificates;
     the exact order does not matter,
     so long as all validators use the same order."))
  (cond ((set::emptyp certs) nil)
        (t (append (certificate->transactions (set::head certs))
                   (transactions-from-certificates (set::tail certs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-blockchain ((anchors certificate-listp)
                           (dag certificate-setp)
                           (blockchain block-listp)
                           (committed-certs certificate-setp))
  :returns (mv (new-blockchain block-listp)
               (new-committed-certs certificate-setp))
  :short "Extend the blockchain with one or more anchors."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of anchors passed to this function
     is calculated via @(tsee collect-anchors).
     Thus, it is ordered from newest (left) to oldest (right),
     and so we extend the blockchain from right to left,
     by @(tsee cdr)ing down the list of anchors and
     processing the @(tsee cdr) before the @(tsee car).
     This function also takes and returns
     the set of all the committed certificates,
     which we need to filter out, from the causal history of each anchor,
     the certificates that have already been committed.")
   (xdoc::p
    "When we reach the end of the list of anchors,
     we return the blockchain and committed certificates unchanged.
     Otherwise, we first extend them with the anchors in the @(tsee cdr).
     Then we take the anchor at the @(tsee car),
     we calculate its causal history,
     and we subtract the already committed certificates:
     the result is the set of certificate to commit in this block.
     So we collect all the transactions from the certificates,
     we form a block, and we add it to the blockchain.
     The round of the block is the one of the anchor.
     We also update the set of committed certificates,
     and return it along with the blockchain.")
   (xdoc::p
    "We show that if the initial blockchain has
     even, strictly increasing (right to left) rounds,
     and the anchors have even, strictly increasing (right to left) rounds,
     and the newest block of the original blockchain
     has a round below the last anchor in the list
     (unless the original blockchain is empty),
     then the new blockchain has even, strictly increasing rounds.
     The theorem assumes that the list of anchors is not empty,
     which is always the case when this function is called.
     This is an important property,
     which serves to show the preservation of
     the invariant that blockchains always have
     even, strictly increasing rounds.
     Note that the hypothesis about
     the @(tsee car) of @(tsee last) having round above
     the newest block of the original blockchain
     matches a property we proved of @(tsee collect-anchors),
     as also mentioned there.")
   (xdoc::p
    "We show that extending the blockchain
     does not change the active committee at a round,
     if that committee can be calculated in the original blockchain."))
  (b* (((when (endp anchors))
        (mv (block-list-fix blockchain)
            (certificate-set-fix committed-certs)))
       ((mv blockchain committed-certs)
        (extend-blockchain (cdr anchors) dag blockchain committed-certs))
       (anchor (car anchors))
       (hist-certs (certificate-causal-history anchor dag))
       (certs-to-commit (set::difference hist-certs committed-certs))
       (transs (transactions-from-certificates certs-to-commit))
       (block (make-block :transactions transs
                          :round (certificate->round anchor)))
       (blockchain (cons block blockchain))
       (committed-certs (set::union committed-certs certs-to-commit)))
    (mv blockchain committed-certs))
  :verify-guards :after-returns

  ///

  (defret consp-of-extend-blockchain
    (equal (consp new-blockchain)
           (or (consp blockchain)
               (consp anchors)))
    :hints (("Goal" :induct t)))

  (in-theory (disable consp-of-extend-blockchain))

  (defret round-of-car-of-extend-blockchain
    (equal (block->round (car new-blockchain))
           (certificate->round (car anchors)))
    :hyp (consp anchors))

  (in-theory (disable round-of-car-of-extend-blockchain))

  (defret blocks-ordered-even-p-of-extend-blockchain
    (blocks-ordered-even-p new-blockchain)
    :hyp (and (certificates-ordered-even-p anchors)
              (blocks-ordered-even-p blockchain)
              (consp anchors)
              (or (endp blockchain)
                  (> (certificate->round (car (last anchors)))
                     (block->round (car blockchain)))))
    :hints (("Goal"
             :induct t
             :in-theory (enable blocks-ordered-even-p
                                certificates-ordered-even-p
                                last))))

  (in-theory (disable blocks-ordered-even-p-of-extend-blockchain))

  (defruled extend-blockchain-as-append
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (equal new-blockchain
             (append (take (- (len new-blockchain)
                              (len blockchain))
                           new-blockchain)
                     (block-list-fix blockchain))))
    :induct t
    :enable (len
             fix))

  (defruled active-committee-at-round-of-extend-blockchain-no-change
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain)
                    (active-committee-at-round round blockchain all-vals))
               (equal (active-committee-at-round round new-blockchain all-vals)
                      (active-committee-at-round round blockchain all-vals))))
    :disable extend-blockchain
    :use (extend-blockchain-as-append
          (:instance active-committee-at-round-of-append
                     (blocks1 (b* (((mv new-blockchain &)
                                    (extend-blockchain anchors
                                                       dag
                                                       blockchain
                                                       committed-certs)))
                                (take (- (len new-blockchain)
                                         (len blockchain))
                                      new-blockchain)))
                     (blocks blockchain)))))
