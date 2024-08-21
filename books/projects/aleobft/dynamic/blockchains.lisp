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
                         (blockchain block-listp))
  :guard (and (evenp previous-round)
              (> (certificate->round current-anchor) previous-round)
              (or (zp previous-round)
                  (active-committee-at-round previous-round blockchain)))
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
     the model of AleoBFT with static committees."))
  (b* (((unless (and (mbt (and (natp previous-round)
                               (evenp previous-round)
                               (natp last-committed-round)
                               (or (zp previous-round)
                                   (active-committee-at-round previous-round
                                                              blockchain))
                               t))
                     (> previous-round last-committed-round)))
        (list (certificate-fix current-anchor)))
       (commtt (active-committee-at-round previous-round blockchain))
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
                               blockchain))
      (collect-anchors current-anchor
                       (- previous-round 2)
                       last-committed-round
                       dag
                       blockchain)))
  :measure (nfix previous-round)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix)))
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-earlier-round-when-at-later-round))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     and return it along with the blockchain."))
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
  :verify-guards :after-returns)
