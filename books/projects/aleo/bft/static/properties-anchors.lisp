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

(include-book "operations-anchors")
(include-book "properties-dags")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ properties-anchors
  :parents (correctness)
  :short "Some properties of operations on anchors."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to some "
    (xdoc::seetopic "properties-certificate-retrieval"
                    "properties about certificate retrieval operations")
    " and to some "
    (xdoc::seetopic "properties-dags"
                    "properties about DAG operations")
    ", some of the properties of anchor operations
     come in two flavors:
     one on single DAGs, pertaining to the growing DAG of a single validators,
     and one on two DAGs, pertaining to DAGs of different validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-anchors-of-unequivocal-dag-superset
  :short "The anchors collected, starting from an anchor,
          from a backward-closed subset of a DAG of unequivocal certificates
          are the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "The anchor collection in question is the one
     expressed by the @(tsee collect-anchors) operation,
     which collects anchors starting from a given one
     down to a given round (or 0 for all rounds).
     If the starting anchor is in the subset,
     it must also be in the superset of course,
     and collecting the anchors in the superset
     yields the same result as collecting the anchors in the subset.
     That is, the collection of anchors is stable under DAG growth.")
   (xdoc::p
    "This builds on the stability property of paths under DAG growth.
     The collection of anchors is based on the paths,
     both present and absent paths,
     which have been previously proved to be stable under DAG growth.")
   (xdoc::p
    "If this property did not hold,
     a validator could collect different anchors,
     starting from the same anchor,
     at different times,
     resulting in different blockchains.
     This property guarantees that the exact time does not matter.")
   (xdoc::p
    "See @(tsee collect-anchors-of-unequivocal-dags)
     for an analogous theorem involving DAGs across different validators."))
  (implies (and (certificate-setp dag)
                (certificate-setp dag2)
                (set::subset dag dag2)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag)
                (set::in current-anchor dag))
           (equal (collect-anchors current-anchor
                                   previous-round
                                   last-committed-round
                                   dag2
                                   vals)
                  (collect-anchors current-anchor
                                   previous-round
                                   last-committed-round
                                   dag
                                   vals)))
  :induct t
  :enable (collect-anchors
           path-to-author+round-of-unequivocal-dag-superset
           path-to-author+round-in-dag))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-anchors-of-unequivocal-dags
  :short "The anchors collected, starting from a common anchor,
          from two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGS."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee collect-anchors-of-unequivocal-dag-superset),
     but for two validator and their DAGs
     instead of one validator and its growing DAG.")
   (xdoc::p
    "This is an important property to guarantee
     consistency of blockchains across validators,
     which depend on the anchors being committed.")
   (xdoc::p
    "This theorem is again proved using
     the closure of backward closure under intersection."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::in current-anchor dag1)
                (set::in current-anchor dag2))
           (equal (collect-anchors current-anchor
                                   previous-round
                                   last-committed-round
                                   dag1
                                   vals)
                  (collect-anchors current-anchor
                                   previous-round
                                   last-committed-round
                                   dag2
                                   vals)))
  :use ((:instance collect-anchors-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag1))
        (:instance collect-anchors-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-all-anchors-of-unequivocal-dag-superset
  :short "All the anchors collected, starting from an anchor,
          from a backward-closed subset of a DAG of unequivocal certificates
          are the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee collect-anchors-of-unequivocal-dag-superset),
     but for @(tsee collect-all-anchors) instead of @(tsee collect-anchors).
     This theorem is easily proved using the other one,
     which is more general and proved by induction,
     using the recursive structure of @(tsee collect-anchors).")
   (xdoc::p
    "This shows that, as the DAG of a validator grows,
     the complete sequence of anchors from an existing anchor
     is stabled under the growth of the DAG."))
  (implies (and (certificate-setp dag)
                (certificate-setp dag2)
                (set::subset dag dag2)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag)
                (set::in last-anchor dag))
           (equal (collect-all-anchors last-anchor dag2 vals)
                  (collect-all-anchors last-anchor dag vals)))
  :enable (collect-all-anchors
           collect-anchors-of-unequivocal-dag-superset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-all-anchors-of-unequivocal-dags
  :short "All the anchors collected, starting from a common anchor,
          from two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGS."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee collect-anchors-of-unequivocal-dags),
     but for @(tsee collect-all-anchors) instead of @(tsee collect-anchors).
     This theorem is easily proved using the other one,
     which is more general and proved by induction,
     using the recursive structure of @(tsee collect-anchors).")
   (xdoc::p
    "This shows that two different validators will collect
     the same total sequence of anchors,
     and therefore the same total sequence of blocks,
     given that causal histories have been also proved consistent,
     from the same common anchor.
     More is needed to show the non-forking of blockchains,
     but this property here is a critical one for that."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::in last-anchor dag1)
                (set::in last-anchor dag2))
           (equal (collect-all-anchors last-anchor dag1 vals)
                  (collect-all-anchors last-anchor dag2 vals)))
  :enable (collect-all-anchors
           collect-anchors-of-unequivocal-dags))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-last-anchor-if-same-last
  :short "If two validator states have unequivocal DAGs,
          the same last committed round,
          and anchors present when that last committed round if not 0,
          then their last anchors are the same."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows mainly from the theorem
     @(tsee cert-with-author+round-of-unequivocal-sets)."))
  (implies (and (certificate-sets-unequivocalp (validator-state->dag vstate1)
                                               (validator-state->dag vstate2))
                (or (equal (validator-state->last vstate1) 0)
                    (last-anchor vstate1 vals))
                (or (equal (validator-state->last vstate2) 0)
                    (last-anchor vstate2 vals))
                (equal (validator-state->last vstate1)
                       (validator-state->last vstate2)))
           (equal (last-anchor vstate1 vals)
                  (last-anchor vstate2 vals)))
  :enable last-anchor
  :use ((:instance cert-with-author+round-of-unequivocal-sets
                   (certs1 (validator-state->dag vstate1))
                   (certs2 (validator-state->dag vstate2))
                   (author (leader-at-round
                            (validator-state->last vstate1) vals))
                   (round (validator-state->last vstate2)))))
