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

(include-book "anchors")

(local (include-book "arithmetic/top" :dir :system))
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
     if that committee can be calculated in the original blockchain.
     As a consequence, collecting anchors is not affected
     by the extension of the blockchain,
     as proved for @(tsee collect-anchors) and @(tsee collect-all-anchors)."))
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
              (> (certificate->round (car (last anchors)))
                 (blocks-last-round blockchain)))
    :hints (("Goal"
             :induct t
             :in-theory (enable blocks-ordered-even-p
                                blocks-last-round
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
                     (blocks blockchain))))

  (defruled collect-anchors-of-extend-blockchain-no-change
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain)
                    (or (zp previous-round)
                        (active-committee-at-round previous-round
                                                   blockchain
                                                   all-vals)))
               (equal (collect-anchors current-anchor
                                       previous-round
                                       last-committed-round
                                       dag
                                       new-blockchain
                                       all-vals)
                      (collect-anchors current-anchor
                                       previous-round
                                       last-committed-round
                                       dag
                                       blockchain
                                       all-vals))))
    :induct (collect-anchors current-anchor
                             previous-round
                             last-committed-round
                             dag
                             blockchain
                             all-vals)
    :enable (collect-anchors
             active-committee-at-round-of-extend-blockchain-no-change
             active-committee-at-previous2-round-when-at-round)
    :disable extend-blockchain)

  (defruled collect-all-anchors-of-extend-blockchain-no-change
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain)
                    (active-committee-at-round (certificate->round last-anchor)
                                               blockchain
                                               all-vals))
               (equal (collect-all-anchors last-anchor
                                           dag
                                           new-blockchain
                                           all-vals)
                      (collect-all-anchors last-anchor
                                           dag
                                           blockchain
                                           all-vals))))
    :enable (collect-all-anchors
             collect-anchors-of-extend-blockchain-no-change
             active-committee-at-previous2-round-when-at-round)))
