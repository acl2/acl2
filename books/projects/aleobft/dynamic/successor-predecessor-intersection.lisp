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
     has enough votes (i.e. successors) at round @($r+1$),
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

(defruled cardinality-of-successor-predecessor-intersection
  :short "Abstract form of the intersection theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here @('n') and @('f') are
     the @($n$) and @($f$) mentioned in @(tsee max-faulty-for-total).
     Here @('successors') represents the successors of @($A$),
     while @('predecessors') represents the predecessors of @($C$),
     with reference to @(see successor-predecessor-intersection).")
   (xdoc::p
    "If the total number of successors and predecessors is bounded by @('n'),
     there are at least @('f + 1') successors,
     and there are @('n - f') predecessors,
     then in order for them to have no intersection
     there should be @('n + 1') of them,
     which contradicts the first hypothesis.
     So there must be at least one in the intersection."))
  (implies (and (<= (set::cardinality (set::union successors predecessors))
                    n)
                (>= (set::cardinality successors)
                    (1+ f))
                (equal (set::cardinality predecessors)
                       (- n f)))
           (>= (set::cardinality (set::intersect successors predecessors))
               1))
  :rule-classes :linear
  :enable set::expand-cardinality-of-intersect
  :disable (set::expand-cardinality-of-union
            set::cardinality-zero-emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled successors+predecessors-same-round
  :short "Successors and predecessors have all the same round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to establish
     a hypothesis of @(tsee cardinality-of-successors+predecessors).
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

(defruled cardinality-of-successors+predecessors
  :short "Relation between the number of successor and predecessor certificates
          and the number of their authors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in
     the proof of @(tsee cardinality-of-successors+predecessors-bound).
     Because of non-equivocation,
     specifically that the two DAGs are individually and mutually unequivocal,
     their union is also unequivocal.
     So the union of successors and predecessors is unequivocal,
     and since these certificates all have the same round,
     there is a bijection between these certificates and their authors."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1))))
           (equal (set::cardinality
                   (set::union (successors cert1 dag1)
                               (predecessors cert2 dag2)))
                  (set::cardinality
                   (cert-set->author-set
                    (set::union (successors cert1 dag1)
                                (predecessors cert2 dag2))))))
  :enable (cardinality-of-authors-when-unequiv-and-all-same-rounds
           successors+predecessors-same-round
           certificate-set-unequivocalp-of-union
           certificate-set-unequivocalp-when-subset
           certificate-sets-unequivocalp-when-subsets
           successors-subset-of-dag
           predecessors-subset-of-dag)
  :disable set::expand-cardinality-of-union)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-successors+predecessors-bound
  :short "Bound on the cardinality of successors and predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to establish the first hypothesis of
     @(tsee cardinality-of-successor-predecessor-intersection)
     in its instantiation in
     @(tsee successor-predecessor-intersection-not-empty).
     Assuming that the authors of the successor and predecessor certificates
     are all members of a committee
     (this fact can be established from other facts,
     when this successor-predecessor intersection property is used),
     then clearly the total number of authors
     is bounded by the committee size.
     But we know from @(tsee cardinality-of-successors+predecessors)
     that the number of authors is the same as the number of certificates,
     and thus we obtain the desired bound on certificates."))
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
                             (committee-members commtt)))
           (<= (set::cardinality
                (set::union (successors cert1 dag1)
                            (predecessors cert2 dag2)))
               (committee-total commtt)))
  :enable (committee-total
           cardinality-of-successors+predecessors
           cert-set->author-set-of-union)
  :disable set::expand-cardinality-of-union)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled successor-predecessor-intersection-not-empty
  :short "The intersection of successors and predecessors is not empty."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the main intersection theorem.
     Mainly, we instantiate the abstract one,
     i.e. @(tsee cardinality-of-successor-predecessor-intersection),
     and we use @(tsee cardinality-of-successors+predecessors-bound)
     to establish the bound hypothesis."))
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
                (>= (set::cardinality (successors cert1 dag1))
                    (1+ (committee-max-faulty commtt)))
                (equal (set::cardinality (predecessors cert2 dag2))
                       (committee-quorum commtt)))
           (not (set::emptyp (set::intersect (successors cert1 dag1)
                                             (predecessors cert2 dag2)))))
  :use ((:instance cardinality-of-successor-predecessor-intersection
                   (successors (successors cert1 dag1))
                   (predecessors (predecessors cert2 dag2))
                   (n (committee-total commtt))
                   (f (committee-max-faulty commtt)))
        (:instance set::cardinality-zero-emptyp
                   (x (set::intersect (successors cert1 dag1)
                                      (predecessors cert2 dag2)))))
  :enable (committee-quorum
           cardinality-of-successors+predecessors-bound)
  :disable (set::expand-cardinality-of-union
            set::cardinality-zero-emptyp))

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
     @(tsee successor-predecessor-intersection-not-empty),
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
    :disable pick-successor/predecessor)

  (defruled pick-successor/predecessor-in-dag2
    (implies (and (certificate-setp dag2)
                  (pick-successor/predecessor dag1 dag2 cert1 cert2))
             (set::in (pick-successor/predecessor dag1 dag2 cert1 cert2)
                      dag2))
    :use (:instance predecessors-subset-of-dag (cert cert2) (dag dag2))
    :enable (pick-successor/predecessor-in-predecessors
             set::expensive-rules)
    :disable pick-successor/predecessor)

  (defruled pick-successor/predecessor-when-cardinalities
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
                  (>= (set::cardinality (successors cert1 dag1))
                      (1+ (committee-max-faulty commtt)))
                  (equal (set::cardinality (predecessors cert2 dag2))
                         (committee-quorum commtt)))
             (pick-successor/predecessor dag1 dag2 cert1 cert2))
    :use (successor-predecessor-intersection-not-empty
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
     The hypotheses on the DAGs are all invariants, proved elsewhere.
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
                (dag-committees-p dag1 blocks1 all-vals)
                (dag-committees-p dag2 blocks2 all-vals)
                (same-active-committees-p blocks1 blocks2 all-vals)
                (dag-rounds-in-committees-p dag1 blocks1 all-vals)
                (dag-rounds-in-committees-p dag2 blocks2 all-vals)
                (dag-predecessor-cardinality-p dag2 blocks2 all-vals)
                (>= (set::cardinality (successors cert1 dag1))
                    (1+ (committee-max-faulty
                         (active-committee-at-round
                          (1+ (certificate->round cert1))
                          blocks1
                          all-vals)))))
           (b* ((cert (pick-successor/predecessor dag1 dag2 cert1 cert2)))
             (and (set::in cert (successors cert1 dag1))
                  (set::in cert (predecessors cert2 dag2))
                  (set::in cert dag1)
                  (set::in cert dag2))))
  :use ((:instance pick-successor/predecessor-when-cardinalities
                   (commtt (active-committee-at-round
                            (1+ (certificate->round cert1))
                            blocks2
                            all-vals)))
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
     (implies (dag-rounds-in-committees-p dag1 blocks1 all-vals)
              (set::subset (cert-set->author-set
                            (successors cert1 dag1))
                           (committee-members
                            (active-committee-at-round
                             (1+ (certificate->round cert1)) blocks1 all-vals))))
     :use ((:instance dag-rounds-in-committees-p-necc
                      (dag dag1)
                      (blocks blocks1)
                      (round (1+ (certificate->round cert1))))
           (:instance set::emptyp-subset-2
                      (x (successors cert1 dag1))
                      (y (certificates-with-round (1+ (certificate->round cert1))
                                                  dag1))))
     :enable (successors-subset-of-next-round
              cert-set->author-set-monotone
              set::expensive-rules)
     :disable set::emptyp-subset-2)

   (defruled lemma2
     (implies (and (certificate-setp dag2)
                   (dag-rounds-in-committees-p dag2 blocks2 all-vals)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1))))
              (set::subset (cert-set->author-set
                            (predecessors cert2 dag2))
                           (committee-members
                            (active-committee-at-round
                             (1- (certificate->round cert2)) blocks2 all-vals))))
     :use ((:instance dag-rounds-in-committees-p-necc
                      (dag dag2)
                      (blocks blocks2)
                      (round (1- (certificate->round cert2))))
           (:instance set::emptyp-subset-2
                      (x (predecessors cert2 dag2))
                      (y (certificates-with-round (1- (certificate->round cert2))
                                                  dag2))))
     :enable (predecessors-subset-of-previous-round
              cert-set->author-set-monotone
              set::expensive-rules)
     :disable set::emptyp-subset-2)

   (defruled lemma3
     (implies (and (certificate-setp dag1)
                   (dag-committees-p dag1 blocks1 all-vals)
                   (dag-committees-p dag2 blocks2 all-vals)
                   (same-active-committees-p blocks1 blocks2 all-vals)
                   (set::in cert2 dag2)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1)))
                   (>= (set::cardinality (successors cert1 dag1))
                       (1+ (committee-max-faulty
                            (active-committee-at-round
                             (1+ (certificate->round cert1))
                             blocks1
                             all-vals)))))
              (equal (active-committee-at-round
                      (1+ (certificate->round cert1)) blocks1 all-vals)
                     (active-committee-at-round
                      (1+ (certificate->round cert1)) blocks2 all-vals)))
     :use ((:instance same-active-committees-p-necc
                      (round (1+ (certificate->round cert1))))
           (:instance dag-committees-p-necc
                      (dag dag1)
                      (blocks blocks1)
                      (cert (set::head (successors cert1 dag1))))
           (:instance dag-committees-p-necc
                      (dag dag2)
                      (blocks blocks2)
                      (cert cert2))
           (:instance set::in-head
                      (x (successors cert1 dag1)))
           (:instance active-committee-at-previous-round-when-at-round
                      (blocks blocks2)
                      (round (certificate->round cert2)))
           (:instance set::cardinality-zero-emptyp
                      (x (successors cert1 dag1))))
     :enable (successors-subset-of-dag
              set::expensive-rules
              certificate->round-of-element-of-successors)
     :disable (set::in-head
               set::cardinality-zero-emptyp))

   (defruled lemma4
     (implies (and (set::in cert2 dag2)
                   (equal (certificate->round cert2)
                          (+ 2 (certificate->round cert1)))
                   (dag-predecessor-cardinality-p dag2 blocks2 all-vals))
              (equal (set::cardinality (predecessors cert2 dag2))
                     (committee-quorum
                      (active-committee-at-round
                       (1+ (certificate->round cert1))
                       blocks2
                       all-vals))))
     :use (:instance dag-predecessor-cardinality-p-necc
                     (dag dag2)
                     (blocks blocks2)
                     (cert cert2)))))
