; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "anchors")

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
  (cond ((set::emptyp (certificate-set-fix certs)) nil)
        (t (append (certificate->transactions (set::head certs))
                   (transactions-from-certificates (set::tail certs)))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-blockchain ((anchors certificate-listp)
                           (dag certificate-setp)
                           (blockchain block-listp)
                           (committed-certs certificate-setp))
  :guard (cert-list-evenp anchors)
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
     since we need to exclude, from the causal history of each anchor,
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
     strictly increasing rounds (right to left),
     and the anchors have even, strictly increasing rounds (right to left),
     and the newest block of the original blockchain
     has a round below the last anchor in the list
     (unless the original blockchain is empty),
     then the new blockchain has strictly increasing rounds as well.
     This theorem expresses an important property,
     which serves to show the preservation of
     the invariant that blockchains always have strictly increasing rounds.
     Note that the hypothesis about
     the @(tsee car) of @(tsee last) having round above
     the newest block of the original blockchain
     matches a property we proved of @(tsee collect-anchors),
     i.e. @('collect-anchors-above-last-committed-round')."))
  (b* (((when (endp anchors))
        (mv (block-list-fix blockchain)
            (certificate-set-fix committed-certs)))
       ((mv blockchain committed-certs)
        (extend-blockchain (cdr anchors) dag blockchain committed-certs))
       (anchor (car anchors))
       (hist-certs (cert-causal-history anchor dag))
       (certs-to-commit (set::difference hist-certs committed-certs))
       (transs (transactions-from-certificates certs-to-commit))
       (block (make-block :transactions transs
                          :round (certificate->round anchor)))
       (blockchain (cons block blockchain))
       (committed-certs (set::union committed-certs certs-to-commit)))
    (mv blockchain committed-certs))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret consp-of-extend-blockchain
    (equal (consp new-blockchain)
           (or (consp blockchain)
               (consp anchors)))
    :hints (("Goal" :induct t)))
  (in-theory (disable consp-of-extend-blockchain))

  (defruled extend-blockchain-as-append
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (equal new-blockchain
             (append (take (- (len new-blockchain)
                              (len blockchain))
                           new-blockchain)
                     (block-list-fix blockchain))))
    :induct t
    :enable (len fix))

  (defret blocks-last-round-of-extend-blockchain
    (equal (blocks-last-round new-blockchain)
           (certificate->round (car anchors)))
    :hyp (and (consp anchors)
              (cert-list-evenp anchors))
    :hints (("Goal" :in-theory (enable blocks-last-round
                                       consp-of-extend-blockchain))))
  (in-theory (disable blocks-last-round-of-extend-blockchain))

  (defret blocks-orderedp-of-extend-blockchain
    (blocks-orderedp new-blockchain)
    :hyp (and (cert-list-orderedp anchors)
              (cert-list-evenp anchors)
              (blocks-orderedp blockchain)
              (> (certificate->round (car (last anchors)))
                 (blocks-last-round blockchain)))
    :hints (("Goal"
             :induct t
             :in-theory (enable blocks-orderedp
                                blocks-last-round
                                cert-list-orderedp
                                last))))
  (in-theory (disable blocks-orderedp-of-extend-blockchain)))
