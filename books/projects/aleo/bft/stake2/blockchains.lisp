; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

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
     even, strictly increasing (right to left) rounds,
     and the anchors have even, strictly increasing (right to left) rounds,
     and the newest block of the original blockchain
     has a round below the last anchor in the list
     (unless the original blockchain is empty),
     then the new blockchain has even, strictly increasing rounds.
     The theorem assumes that the list of anchors is not empty,
     which is always the case when this function is called.
     This theorem expresses an important property,
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
     as proved for @(tsee collect-anchors) and @(tsee collect-all-anchors).
     Furthermore, if the predicates
     @(tsee dag-has-committees-p) and @(tsee dag-in-committees-p) hold,
     they continue holding if the blockchain is extended.")
   (xdoc::p
    "We show that if a blockchain is extended using anchors
     that are all in the DAG and connected by paths
     (i.e. satisfying @(tsee certificates-dag-paths-p),
     the set of all new committed certificates is the union of
     the old ones with the causal history of the latest anchor.
     Based on just the definition of @('extend-blockchain'),
     we should take the union of the causal histories of all the anchors,
     but since they are all connected by paths,
     the causal history of the latest anchor (the @(tsee car))
     includes the causal history of all the other anchors,
     and therefore the final set of committed certificates is
     the union of that latest causal history
     with the previous committed certificates.
     But this theorem also covers the case of an empty list of anchors,
     in which case there is no change in the set of committed certificates.")
   (xdoc::p
    "The extension of a blockchain with some anchors
     in a backward-closed subset of an unequivocal DAG
     is the same in the superset.
     This is because causal histories satisfy a similar property.")
   (xdoc::p
    "The extensions of a blockchain with some anchors
     in two backward-closed, individualy and mutually unequivocal DAGs
     are the same in the two DAGs.
     This is because causal histories satisfy a similar property."))
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

  (defret len-of-extend-blockchain
    (equal (len new-blockchain)
           (+ (len blockchain)
              (len anchors)))
    :hints (("Goal"
             :induct t
             :in-theory (enable len fix))))

  (defrule extend-blockchain-of-nil
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

  (defruled nthcdr-of-extend-blockchain
    (implies
     (<= n (len anchors))
     (equal (nthcdr n (mv-nth 0 (extend-blockchain anchors dag blocks comms)))
            (mv-nth 0 (extend-blockchain (nthcdr n anchors) dag blocks comms))))
    :induct t
    :enable (nthcdr len))

  (defret blocks-last-round-of-extend-blockchain
    (equal (blocks-last-round new-blockchain)
           (certificate->round (car anchors)))
    :hyp (consp anchors)
    :hints (("Goal" :in-theory (enable blocks-last-round
                                       consp-of-extend-blockchain))))
  (in-theory (disable blocks-last-round-of-extend-blockchain))

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

  (defruled active-committee-at-round-of-extend-blockchain-no-change
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain)
                    (active-committee-at-round round blockchain))
               (equal (active-committee-at-round round new-blockchain)
                      (active-committee-at-round round blockchain))))
    :disable extend-blockchain
    :use (extend-blockchain-as-append
          (:instance active-committee-at-round-of-append-no-change
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
                        (active-committee-at-round previous-round blockchain)))
               (equal (collect-anchors current-anchor
                                       previous-round
                                       last-committed-round
                                       dag
                                       new-blockchain)
                      (collect-anchors current-anchor
                                       previous-round
                                       last-committed-round
                                       dag
                                       blockchain))))
    :induct (collect-anchors current-anchor
                             previous-round
                             last-committed-round
                             dag
                             blockchain)
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
                                               blockchain))
               (equal (collect-all-anchors last-anchor dag new-blockchain)
                      (collect-all-anchors last-anchor dag blockchain))))
    :enable (collect-all-anchors
             collect-anchors-of-extend-blockchain-no-change
             active-committee-at-previous2-round-when-at-round))

  (defruled dag-has-committees-p-of-extend-blockchain
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain))
               (implies (dag-has-committees-p dag blockchain)
                        (dag-has-committees-p dag new-blockchain))))
    :enable (dag-has-committees-p
             dag-has-committees-p-necc-bind-dag
             active-committee-at-round-of-extend-blockchain-no-change))

  (defruled dag-in-committees-p-of-extend-blockchain
    (b* (((mv new-blockchain &)
          (extend-blockchain anchors dag blockchain committed-certs)))
      (implies (and (block-listp blockchain)
                    (blocks-ordered-even-p new-blockchain))
               (implies (and (dag-in-committees-p dag blockchain)
                             (dag-has-committees-p dag blockchain))
                        (dag-in-committees-p dag new-blockchain))))
    :enable (dag-in-committees-p
             dag-has-committees-p-necc-bind-dag
             dag-in-committees-p-necc-bind-dag
             active-committee-at-round-of-extend-blockchain-no-change))

  (defruled new-committed-certs-of-extend-blockchain
    (implies (and (certificate-setp dag)
                  (certificate-set-unequivocalp dag)
                  (certificates-dag-paths-p anchors dag)
                  (certificate-setp committed-certs))
             (b* (((mv & new-committed-certs)
                   (extend-blockchain anchors dag blockchain committed-certs)))
               (equal new-committed-certs
                      (if (consp anchors)
                          (set::union
                           (certificate-causal-history (car anchors) dag)
                           committed-certs)
                        committed-certs))))
    :induct t
    :enable (certificates-dag-paths-p
             nil-not-in-certificate-set
             set::expensive-rules)
    :hints ('(:use (:instance certificate-causal-history-subset-when-path
                              (cert (car anchors))
                              (author (certificate->author (cadr anchors)))
                              (round (certificate->round (cadr anchors)))))))

  (defruled extend-blockchain-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::list-in anchors dag0))
             (equal (extend-blockchain
                     anchors dag blockchain committed-certs)
                    (extend-blockchain
                     anchors dag0 blockchain committed-certs)))
    :induct t
    :enable certificate-causal-history-of-unequivocal-superdag)

  (defruled extend-blockchain-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (set::list-in anchors dag1)
                  (set::list-in anchors dag2))
             (equal (extend-blockchain
                     anchors dag1 blockchain committed-certs)
                    (extend-blockchain
                     anchors dag2 blockchain committed-certs)))
    :induct t
    :enable certificate-causal-history-of-unequivocal-dags))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define calculate-blockchain ((anchors certificate-listp)
                              (dag certificate-setp))
  :returns (blockchain block-listp)
  :short "Calculate a blockchain from a sequence of anchors and a DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee extend-blockchain)
     starting with the empty blockchain and no committed certificates.
     We only returns the blockchain,
     discarding the committed certificate set.")
   (xdoc::p
    "The blockchain calculated from a sequence of anchors
     in a backward-closed subset of an unequivocal DAG
     is the same in the superset.
     This is based on the analogous property of @(tsee extend-blockchain).")
   (xdoc::p
    "The blockchains calculated from a sequence of anchors
     in two backward-closed, individually and mutually unequivocal DAGs
     are the same in the two DAGs.
     This is based on the analogous property of @(tsee extend-blockchain)."))
  (b* (((mv blockchain &) (extend-blockchain anchors dag nil nil)))
    blockchain)

  ///

  (defret len-of-calculate-blockchain
    (equal (len blockchain)
           (len anchors))
    :hints (("Goal" :in-theory (enable fix len-of-extend-blockchain))))

  (defrule calculate-blockchain-of-nil
    (equal (calculate-blockchain nil dag)
           nil)
    :enable extend-blockchain-of-nil)

  (defruled nthcdr-of-calculate-blockchain
    (implies (<= n (len anchors))
             (equal (nthcdr n (calculate-blockchain anchors dag))
                    (calculate-blockchain (nthcdr n anchors) dag)))
    :enable nthcdr-of-extend-blockchain)

  (defruled calculate-blockchain-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::list-in anchors dag0))
             (equal (calculate-blockchain anchors dag)
                    (calculate-blockchain anchors dag0)))
    :enable extend-blockchain-of-unequivocal-superdag)

  (defruled calculate-blockchain-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (set::list-in anchors dag1)
                  (set::list-in anchors dag2))
             (equal (calculate-blockchain anchors dag1)
                    (calculate-blockchain anchors dag2)))
    :enable extend-blockchain-of-unequivocal-dags))
