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

(include-book "certificates")
(include-book "dags")
(include-book "committees")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ successor-predecessor-intersection
  :parents (correctness)
  :short "Intersection of successors and predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the second key intersection argument
     for the correctness of AleoBFT,
     besides "
    (xdoc::seetopic "quorum-intersection" "quorum intersection")
    ". However, this second argument is very different:
     it has nothing to do with correct and faulty validators;
     it only has to do with paths in DAGs.
     When an anchor @($A$) at a round @($r$)
     has enough voting stake from the successors at round @($r+1$),
     then if there is a certificate @($C$) at round @($r+2$)
     then there must be a certificate @($B$) at round @($r+1$)
     that is both a successor (i.e. voter) of @($A$)
     and a predecessor of @($C$).
     This actually also applies across differnt DAGs:
     @($A$) is in DAG 1,
     @($C$) is in DAG 2,
     and @($B$) is in both DAG 1 and DAG 2.
     The case in which DAGs 1 and 2 are the same is a special case.")
   (xdoc::p
    "Here we prove the non-emptiness of the intersection,
     and we introduce a function to pick
     a common certificate from the intersection.
     This is then used in further proofs.")
   (xdoc::p
    "Here we talk about successors and predecessors,
     not specifically voters and anchors,
     because the argument is more general."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-empty-successor-predecessor-author-intersection
  :short "Non-empty intersection of successor and predecessor authors."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here @('n') and @('f') are
     the @($n$) and @($f$) mentioned in @(tsee max-faulty-for-total).
     Here @('successors-vals') represents
     the authors of the successors of @($A$),
     while @('predecessors') represents
     the authors of the predecessors of @($C$),
     with reference to @(see successor-predecessor-intersection).")
   (xdoc::p
    "If (i) the total stake of successor and predecessor authors
     is bounded by @('n'),
     (ii) the total stake of the successor authors
     is more than @('f'),
     and (iii) the total stake of the predecessor authors
     is at least @('n - f'),
     then in order for the two sets to have no intersection
     their total stake would have to be more than @('n'),
     which contradicts the first hypothesis.
     So there must be at least one in the intersection."))
  (implies (and (address-setp successor-vals)
                (address-setp predecessor-vals)
                (<= (committee-members-stake (set::union successor-vals
                                                         predecessor-vals)
                                             commtt)
                    n)
                (> (committee-members-stake successor-vals commtt)
                   f)
                (>= (committee-members-stake predecessor-vals commtt)
                    (- n f)))
           (not (set::emptyp (set::intersect successor-vals
                                             predecessor-vals))))
  :enable committee-members-stake-of-intersect
  :use (:instance committee-members-stake-0-to-emptyp-members
                  (members (set::intersect successor-vals predecessor-vals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled successors+predecessors-same-round
  :short "Successors and predecessors have all the same round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to establish
     a hypothesis of @(tsee not-empty-successor-predecessor-intersection).
     If (again with reference to @(see successor-predecessor-intersection))
     @($A$) and @($C$) are two rounds apart,
     then the successors of @($A$) and the predecessors of @($C$)
     are all in the round between those two rounds."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1))))
           (<= (set::cardinality
                (cert-set->round-set
                 (set::union (successors cert1 dag1)
                             (predecessors cert2 dag2))))
               1))
  :rule-classes :linear
  :enable (set::cardinality
           cert-set->round-set-of-successors
           cert-set->round-set-of-predecessors
           cert-set->round-set-of-union))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-empty-successor-predecessor-intersection
  :short "Non-empty intersection of successors and predecessors"
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee not-empty-successor-predecessor-author-intersection)
     from the authors,
     over which stake is calculated,
     to the certificates,
     which are the ones whose non-empty intersection we need to show.
     With reference to @(see successor-predecessor-intersection),
     here @('cert1') is @($A$) and @('cert2') is @($C$);
     we show that the successors of @($A$) and the predecessors of @($C$)
     have a non-empty intersection.
     The key theorem used in the proof is
     @('certs-same-round-unequiv-intersect-when-authors-intersect')."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1)))
                (set::subset (cert-set->author-set
                              (successors cert1 dag1))
                             (committee-members commtt))
                (set::subset (cert-set->author-set
                              (predecessors cert2 dag2))
                             (committee-members commtt))
                (> (committee-members-stake
                    (cert-set->author-set
                     (successors cert1 dag1))
                    commtt)
                   (committee-max-faulty-stake commtt))
                (>= (committee-members-stake
                     (cert-set->author-set
                      (predecessors cert2 dag2))
                     commtt)
                    (committee-quorum-stake commtt)))
           (not (set::emptyp (set::intersect (successors cert1 dag1)
                                             (predecessors cert2 dag2)))))
  :enable (committee-quorum-stake
           committee-total-stake
           committee-members-stake-monotone
           certificate-set-unequivocalp-of-union
           certificate-set-unequivocalp-when-subset
           certificate-sets-unequivocalp-when-subsets
           successors+predecessors-same-round
           certs-same-round-unequiv-intersect-when-authors-intersect)
  :use (:instance not-empty-successor-predecessor-author-intersection
                  (successor-vals (cert-set->author-set
                                   (successors cert1 dag1)))
                  (predecessor-vals (cert-set->author-set
                                     (predecessors cert2 dag2)))
                  (n (committee-total-stake commtt))
                  (f (committee-max-faulty-stake commtt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pick-successor/predecessor ((dag1 certificate-setp)
                                    (dag2 certificate-setp)
                                    (cert1 certificatep)
                                    (cert2 certificatep))
  :guard (and (set::in cert1 dag1)
              (set::in cert2 dag2)
              (equal (certificate->round cert2)
                     (+ 2 (certificate->round cert1))))
  :returns (cert? certificate-optionp)
  :short "Pick a certificate in the successor-predecessor intersection."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick the first one, but the exact choice does not matter.
     We show that, under the assumptions in
     @(tsee not-empty-successor-predecessor-intersection),
     this function returns a certificate that is
     in the successors, in the predecessors, and in both DAGs."))
  (b* ((common (set::intersect (successors cert1 dag1)
                               (predecessors cert2 dag2))))
    (if (set::emptyp common)
        nil
      (set::head common)))

  ///

  (defruled pick-successor/predecessor-in-successors
    (implies (pick-successor/predecessor dag1 dag2 cert1 cert2)
             (set::in (pick-successor/predecessor dag1 dag2 cert1 cert2)
                      (successors cert1 dag1)))
    :enable set::head-of-intersect-member-when-not-emptyp)

  (defruled pick-successor/predecessor-in-predecessors
    (implies (pick-successor/predecessor dag1 dag2 cert1 cert2)
             (set::in (pick-successor/predecessor dag1 dag2 cert1 cert2)
                      (predecessors cert2 dag2)))
    :enable set::head-of-intersect-member-when-not-emptyp)

  (defruled pick-successor/predecessor-in-dag1
    (implies (and (certificate-setp dag1)
                  (pick-successor/predecessor dag1 dag2 cert1 cert2))
             (set::in (pick-successor/predecessor dag1 dag2 cert1 cert2)
                      dag1))
    :use (:instance successors-subset-of-dag (cert cert1) (dag dag1))
    :enable (pick-successor/predecessor-in-successors
             set::expensive-rules)
    :disable (pick-successor/predecessor
              successors-subset-of-dag))

  (defruled pick-successor/predecessor-in-dag2
    (implies (and (certificate-setp dag2)
                  (pick-successor/predecessor dag1 dag2 cert1 cert2))
             (set::in (pick-successor/predecessor dag1 dag2 cert1 cert2)
                      dag2))
    :use (:instance predecessors-subset-of-dag (cert cert2) (dag dag2))
    :enable (pick-successor/predecessor-in-predecessors
             set::expensive-rules)
    :disable (pick-successor/predecessor
              predecessors-subset-of-dag))

  (defruled pick-successor/predecessor-not-nil
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (equal (certificate->round cert2)
                         (+ 2 (certificate->round cert1)))
                  (set::subset (cert-set->author-set
                                (successors cert1 dag1))
                               (committee-members commtt))
                  (set::subset (cert-set->author-set
                                (predecessors cert2 dag2))
                               (committee-members commtt))
                  (> (committee-members-stake
                      (cert-set->author-set
                       (successors cert1 dag1))
                      commtt)
                     (committee-max-faulty-stake commtt))
                  (>= (committee-members-stake
                       (cert-set->author-set
                        (predecessors cert2 dag2))
                       commtt)
                      (committee-quorum-stake commtt)))
             (pick-successor/predecessor dag1 dag2 cert1 cert2))
    :use (not-empty-successor-predecessor-intersection
          (:instance consp-when-certificatep
                     (x (pick-successor/predecessor dag1 dag2 cert1 cert2))))
    :disable consp-when-certificatep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pick-successor/predecessor-properties
  :short "Key properties of @(tsee pick-successor/predecessor)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This combines and generalizes
     the theorems proved in @(tsee pick-successor/predecessor),
     by using stronger hypotheses on the DAGs
     that imply the specific properties used in those previous theorems.
     The hypotheses on the DAGs are all invariants, as proved elsewhere.
     The key properties are that the picked certificate
     is among the successors of @('cert1') in the first DAG,
     among the precedessors of @('cert2') in the second DAG,
     and also in both DAGs.")
   (xdoc::p
    "We prove four lemmas that serve to establish
     hypotheses in the theorems in @(tsee pick-successor/predecessor)
     from the more general hypothesis in this theorem."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (set::in cert2 dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1)))
                (dag-has-committees-p dag1 blockchain1)
                (dag-has-committees-p dag2 blockchain2)
                (dag-in-committees-p dag1 blockchain1)
                (dag-in-committees-p dag2 blockchain2)
                (same-active-committees-p blockchain1 blockchain2)
                (dag-predecessor-quorum-p dag2 blockchain2)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert1 dag1))
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))))
           (b* ((cert (pick-successor/predecessor dag1 dag2 cert1 cert2)))
             (and (set::in cert (successors cert1 dag1))
                  (set::in cert (predecessors cert2 dag2))
                  (set::in cert dag1)
                  (set::in cert dag2))))
  :use ((:instance pick-successor/predecessor-not-nil
                   (commtt (active-committee-at-round
                            (1+ (certificate->round cert1))
                            blockchain2)))
        pick-successor/predecessor-in-successors
        pick-successor/predecessor-in-predecessors
        pick-successor/predecessor-in-dag1
        pick-successor/predecessor-in-dag2
        lemma1
        lemma2
        lemma3
        lemma4)

  :prep-lemmas

  ((defruled lemma1
     (implies (and (certificate-setp dag1)
                   (dag-in-committees-p dag1 blockchain1))
              (set::subset (cert-set->author-set
                            (successors cert1 dag1))
                           (committee-members
                            (active-committee-at-round
                             (1+ (certificate->round cert1)) blockchain1))))
     :use ((:instance round-in-committee-when-dag-in-committees-p
                      (dag dag1)
                      (blockchain blockchain1)
                      (round (1+ (certificate->round cert1))))
           (:instance set::emptyp-subset-2
                      (x (successors cert1 dag1))
                      (y (certs-with-round (1+ (certificate->round cert1))
                                           dag1))))
     :enable (cert-set->author-set-monotone
              set::expensive-rules)
     :disable set::emptyp-subset-2)

   (defruled lemma2
     (implies (and (certificate-setp dag2)
                   (dag-in-committees-p dag2 blockchain2)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1))))
              (set::subset (cert-set->author-set
                            (predecessors cert2 dag2))
                           (committee-members
                            (active-committee-at-round
                             (1- (certificate->round cert2)) blockchain2))))
     :use ((:instance round-in-committee-when-dag-in-committees-p
                      (dag dag2)
                      (blockchain blockchain2)
                      (round (1- (certificate->round cert2))))
           (:instance set::emptyp-subset-2
                      (x (predecessors cert2 dag2))
                      (y (certs-with-round (1- (certificate->round cert2))
                                           dag2))))
     :enable (cert-set->author-set-monotone
              set::expensive-rules)
     :disable set::emptyp-subset-2)

   (defruled lemma3
     (implies (and (certificate-setp dag1)
                   (dag-has-committees-p dag1 blockchain1)
                   (dag-has-committees-p dag2 blockchain2)
                   (dag-in-committees-p dag1 blockchain1)
                   (dag-in-committees-p dag2 blockchain2)
                   (same-active-committees-p blockchain1 blockchain2)
                   (set::in cert2 dag2)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1)))
                   (> (committee-members-stake
                       (cert-set->author-set (successors cert1 dag1))
                       (active-committee-at-round
                        (1+ (certificate->round cert1))
                        blockchain1))
                      (committee-max-faulty-stake
                       (active-committee-at-round
                        (1+ (certificate->round cert1))
                        blockchain1))))
              (equal (active-committee-at-round
                      (1+ (certificate->round cert1)) blockchain1)
                     (active-committee-at-round
                      (1+ (certificate->round cert1)) blockchain2)))
     :use ((:instance same-active-committees-p-necc
                      (round (1+ (certificate->round cert1)))
                      (blocks1 blockchain1)
                      (blocks2 blockchain2))
           (:instance dag-has-committees-p-necc
                      (dag dag1)
                      (blockchain blockchain1)
                      (cert (set::head (successors cert1 dag1))))
           (:instance dag-has-committees-p-necc
                      (dag dag2)
                      (blockchain blockchain2)
                      (cert cert2))
           (:instance dag-in-committees-p-necc
                      (dag dag1)
                      (blockchain blockchain1)
                      (cert (set::head (successors cert1 dag1))))
           (:instance dag-in-committees-p-necc
                      (dag dag2)
                      (blockchain blockchain2)
                      (cert cert2))
           (:instance set::in-head
                      (x (successors cert1 dag1)))
           (:instance active-committee-at-previous-round-when-at-round
                      (blocks blockchain2)
                      (round (certificate->round cert2)))
           (:instance set::cardinality-zero-emptyp
                      (x (successors cert1 dag1))))
     :enable (set::expensive-rules
              certificate->round-of-element-of-successors)
     :disable (set::in-head
               set::cardinality-zero-emptyp))

   (defruled lemma4
     (implies (and (set::in cert2 dag2)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1)))
                   (dag-predecessor-quorum-p dag2 blockchain2))
              (>= (committee-members-stake
                   (cert-set->author-set
                    (predecessors cert2 dag2))
                   (active-committee-at-round (1+ (certificate->round cert1))
                                              blockchain2))
                  (committee-quorum-stake
                   (active-committee-at-round (1+ (certificate->round cert1))
                                              blockchain2))))
     :use (:instance dag-predecessor-quorum-p-necc
                     (dag dag2)
                     (blockchain blockchain2)
                     (cert cert2)))))
