; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-dags")
(include-book "operations-leaders")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-blockchain
  :parents (operations)
  :short "Operations on the blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce operations to extend the blockchain,
     based on the anchors in the DAG."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-anchors ((current-anchor certificatep)
                         (previous-round natp)
                         (last-committed-round natp)
                         (dag certificate-setp)
                         (vals address-setp))
  :guard (and (evenp previous-round)
              (> (certificate->round current-anchor) previous-round)
              (not (set::emptyp vals)))
  :returns (anchors certificate-listp)
  :short "Collect all the anchor certificates to commit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The starting point is an anchor, @('current-anchor')
     and an even round, @('previous-round'), that precedes the anchor.
     The recursion terminates when this previous round
     reaches the last committed round:
     we return a singleton list with the current anchor.
     If the recursion does not terminate,
     we find the leader at the previous round under examination,
     and we use @(tsee path-to-author+round) to find the anchor, if any,
     at the previous round under examination reachable from the current anchor.
     If there is no such reachable previous anchor,
     we recursively examine the even round
     just before the previous one just examined,
     with the same current anchor;
     in the recursion, we will be looking for longer paths,
     from the same current anchor to a round further behind.
     If there is an anchor,
     it becomes the new current anchor,
     and we recursively examine its previous even round,
     but since we changed the current anchor,
     in the recursion DAG paths will be from the new current anchor.
     The recursive call will return a list of anchors
     that includes the anchor passed as first argument.
     thus, when that anchor changes (i.e. when the previous anchor is found),
     we add the old current anchor to the list.
     The resulting list of anchors is in inverse chronological order:
     the leftmost anchor is the newest one (i.e. greatest round number);
     the rightmost anchor is the oldest one (i.e. smallest round number).")
   (xdoc::p
    "Note that the last committed round is a natural number,
     not necessarily a positive one,
     because it is initially 0.
     Since the previous round eventually reaches the last committed round
     (at the end of the recursion),
     the previous round input of this ACL2 function is also a natural number,
     not necessarily positive."))
  (b* (((unless (and (mbt (and (natp previous-round)
                               (evenp previous-round)
                               (natp last-committed-round)))
                     (> previous-round last-committed-round)))
        (list (certificate-fix current-anchor)))
       (previous-leader (leader-at-round previous-round vals))
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
                               vals))
      (collect-anchors current-anchor
                       (- previous-round 2)
                       last-committed-round
                       dag
                       vals)))
  :measure (nfix previous-round)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix)))
  :guard-hints
  (("Goal" :in-theory (enable natp
                              evenp
                              certificate->round-of-path-to-author+round)))

  ///

  (defruled car-of-collect-anchors
    (equal (car (collect-anchors current-anchor
                                 previous-round
                                 last-committed-round
                                 dag
                                 vals))
           (certificate-fix current-anchor))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transactions-from-certificates ((certs certificate-setp))
  :returns (transs transaction-listp)
  :short "Collect all the transactions from a set of certficates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When an anchor is committed,
     a new block is added to the blockchain,
     containing all the transactions from the anchor
     and from its preceding certificates
     (in the sense that there are DAG paths from the anchor to them),
     except for the certificates whose transactions
     have already been added to the blockchain.
     After computing the set of certificates
     whose transactions must be included in a block,
     we call this function to put all those transactions together.
     We put them together according to the ACL2 total order on certificates;
     the exact order does not matter,
     so long as all validators use the same order.
     The Bullshark paper postulates a consistent but unspecified order."))
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
     by @(tsee cdr)ing down the list and
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
       (block (make-block :transactions transs))
       (blockchain (cons block blockchain))
       (committed-certs (set::union committed-certs certs-to-commit)))
    (mv blockchain committed-certs))
  :verify-guards :after-returns

  ///

  (defret len-of-extend-blockchain
    (equal (len new-blockchain)
           (+ (len blockchain)
              (len anchors)))
    :hints (("Goal"
             :induct t
             :in-theory (enable len fix))))
  (in-theory (disable len-of-extend-blockchain))

  (defruled extend-blockchain-of-nil
    (equal (extend-blockchain nil dag blockchain committed-certs)
           (mv (block-list-fix blockchain)
               (certificate-set-fix committed-certs))))

  (defruled extend-blockchain-of-append
    (b* (((mv blocks comms)
          (extend-blockchain (append anchors2 anchors1) dag blocks0 comms0))
         ((mv blocks1 comms1)
          (extend-blockchain anchors1 dag blocks0 comms0))
         ((mv blocks2 comms2)
          (extend-blockchain anchors2 dag blocks1 comms1)))
      (and (equal blocks blocks2)
           (equal comms comms2)))
    :induct t
    :enable append)

  (defruled nthcdr-of-extend-blockchain
    (implies
     (<= n (len anchors))
     (equal (nthcdr n (mv-nth 0 (extend-blockchain anchors dag blocks comms)))
            (mv-nth 0 (extend-blockchain (nthcdr n anchors) dag blocks comms))))
    :induct t
    :enable (nthcdr
             len)))
