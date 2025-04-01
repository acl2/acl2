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

(include-book "operations-blockchain")
(include-book "operations-blockchain-additional")
(include-book "operations-anchors")
(include-book "operations-dags-additional")
(include-book "operations-unequivocal-certificates")
(include-book "properties-dags")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ properties-blockchain
  :parents (correctness)
  :short "Some properties of the operations on blockchains."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some of these come in two forms,
     analogous to properties proved elsewhere:
     one form about the consistency of the growing DAG of a single validator,
     and one form about the consistency across DAGs of different validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-list-pathp-of-collect-anchors
  :short "The anchors returned by @(tsee collect-anchors)
          are all in the DAG and are all connected by paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee certificate-list-pathp) for details on the property."))
  (implies (and (certificate-setp dag)
                (set::in current-anchor dag)
                (> (certificate->round current-anchor)
                   previous-round))
           (certificate-list-pathp (collect-anchors current-anchor
                                                    previous-round
                                                    last-committed-round
                                                    dag
                                                    vals)
                                   dag))
  :induct t
  :enable (collect-anchors
           certificate-list-pathp
           certificate->author-of-path-to-author+round
           certificate->round-of-path-to-author+round
           car-of-collect-anchors)
  :hints ('(:use (:instance path-to-author+round-in-dag
                            (cert current-anchor)
                            (author (leader-at-round previous-round vals))
                            (round previous-round))))
  :disable path-to-author+round-in-dag)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-list-pathp-of-collect-all-anchors
  :short "The anchors returned by @(tsee collect-all-anchors)
          are all in the DAG and are all connected by paths."
  (implies (and (certificate-setp dag)
                (set::in last-anchor dag))
           (certificate-list-pathp (collect-all-anchors last-anchor dag vals)
                                   dag))
  :enable (collect-all-anchors
           certificate-list-pathp-of-collect-anchors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-list-pathp-of-committed-anchors
  :short "The anchors returned by @(tsee committed-anchors)
          are all in the DAG and are all connected by paths."
  (implies (or (equal (validator-state->last vstate) 0)
               (set::in (last-anchor vstate vals)
                        (validator-state->dag vstate)))
           (certificate-list-pathp (committed-anchors vstate vals)
                                   (validator-state->dag vstate)))
  :enable (committed-anchors
           certificate-list-pathp-of-nil
           certificate-list-pathp-of-collect-all-anchors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled new-committed-certs-of-extend-blockchain
  :short "If a blockchain is extended by anchors
          that are all in the DAG and connected by paths,
          the set of all new committed certificates is the union of
          the old ones with the causal history of the latest anchor."
  :long
  (xdoc::topstring
   (xdoc::p
    "As proved in @(tsee certificate-list-pathp-of-collect-anchors),
     when the blockchain is extended,
     the new anchors are in the DAG and connected by paths.
     So, the causal history of the latest anchor (the @(tsee car))
     includes the causal history of all the others,
     and therefore the final set of committed certificates is
     the union of that latest causal history
     with the previous committed certificates.
     This theorem covers the general case of an empty list of anchors,
     in which case there is no change in the set of committed certificates."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (certificate-list-pathp anchors dag)
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
  :enable (extend-blockchain
           certificate-list-pathp
           nil-not-in-certificate-set
           set::expensive-rules)
  :hints ('(:use (:instance certificate-causal-history-subset-when-path
                            (cert (car anchors))
                            (author (certificate->author (cadr anchors)))
                            (round (certificate->round (cadr anchors))))))

  :prep-lemmas
  ((defrule set-lemma
     (implies (set::subset b a)
              (equal (set::union b
                                 (set::union c
                                             (set::difference a
                                                              (set::union b
                                                                          c))))
                     (set::union a c)))
     :enable set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled extend-blockchain-of-unequivocal-dag-superset
  :short "The extension of a blockchain with some anchors
          in a backward-closed subset of an unequivocal DAG
          is the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is because causal histories satisfy a similar property."))
  (implies (and (certificate-setp dag)
                (certificate-setp dag2)
                (set::subset dag dag2)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag)
                (set::list-in anchors dag))
           (equal (extend-blockchain anchors dag2 blocks comms)
                  (extend-blockchain anchors dag blocks comms)))
  :induct t
  :enable (extend-blockchain
           certificate-causal-history-of-unequivocal-dag-superset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled extend-blockchain-of-unequivocal-dags
  :short "The extensions of a blockchain with some anchors
          in two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is because causal histories satisfy a similar property."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::list-in anchors dag1)
                (set::list-in anchors dag2))
           (equal (extend-blockchain anchors dag1 blocks comm)
                  (extend-blockchain anchors dag2 blocks comm)))
  :induct t
  :enable (extend-blockchain
           certificate-causal-history-of-unequivocal-dags))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled calculate-blockchain-of-unequivocal-dag-superset
  :short "The blockchain calculated from a sequence of anchors
          in a backward-closed subset of an unequivocal DAG
          is the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from @(tsee extend-blockchain-of-unequivocal-dag-superset)."))
  (implies (and (certificate-setp dag)
                (certificate-setp dag2)
                (set::subset dag dag2)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag)
                (set::list-in anchors dag))
           (equal (calculate-blockchain anchors dag2)
                  (calculate-blockchain anchors dag)))
  :enable (calculate-blockchain
           extend-blockchain-of-unequivocal-dag-superset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled calculate-blockchain-of-unequivocal-dags
  :short "The blockchains calculated from a sequence of anchors
          in two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from @(tsee extend-blockchain-of-unequivocal-dags)."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::list-in anchors dag1)
                (set::list-in anchors dag2))
           (equal (calculate-blockchain anchors dag1)
                  (calculate-blockchain anchors dag2)))
  :enable (calculate-blockchain
           extend-blockchain-of-unequivocal-dags))
