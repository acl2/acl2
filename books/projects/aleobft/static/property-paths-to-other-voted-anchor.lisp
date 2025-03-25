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

(include-book "property-paths-to-voted-anchor")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-paths-to-other-voted-anchor
  :parents (correctness)
  :short "Property that if an anchor in a DAG has enough votes
          then all the certificates in any other DAG
          that are at leaast two rounds after the anchor
          have some path to the anchor, which is also in the other DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(see property-paths-to-voted-anchor),
     but concerns two DAGs of different validators.
     The same intersection argument applies across validators:
     given a certificate (anchor) @($A$) in DAG 1 at round @($r$),
     with at least @($F+1$) voters for @($A$) in DAG 1 at round @($r+1$),
     and @($N-F$) certificates in DAG 2 at round @($r+1$),
     every certificate @($C$) in DAG 2 at round @($r+2$) or later
     has a path to @($A$), which must be also in DAG 2.
     The reason is that there must be a certificate @($B$)
     that is both in the @($F+1$) or more voters in DAG 1
     and in the @($N-F$) certificates in DAG 2.
     In DAG 1, it has an edge to @($A$).
     Because of the backward closure of DAG 2,
     @($A$) must be in DAG 2 too, with an edge to it from @($B$).
     Since @($B$) is a predecessor of @($C$),
     there is a path from @($C$) to @($A$).
     This holds for every @($C$) in DAG 2 in round @($r+2$),
     so every @($D$) in DAG 2 at round @($r+3$)
     has a predecessor @($C$) with a path to @($A$)
     and so @($D$) has a path to @($A$) too.
     And so on for the rest of the rounds of DAG2."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file includes property-paths-to-voted-anchor.lisp,
; and makes use of some functions and theorems defined there:
; - dag-all-path-to-p
; - dag-round-all-path-to-p
; - dag-all-path-to-p-alt
; - dag-all-path-to-p-alt-def
; - cardinality-of-voters/previous-intersection
; See their documentation in that file.

; The purpose of dag-all-path-to-p is to capture the property of interest,
; which in this case will be applied to DAG 2, with assumptions involving DAG 1.
; Since the property is proved by induction on rounds,
; we make use of the equivalent dag-round-all-path-to-p formulation,
; just like in the other file.

; The cardinality-of-voters/previous-intersection is the intersection argument,
; in abstract form, which is the same in this and the other file.
; But in this file we use it differently.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is similar to the homonymous theorem for the single-DAG property
; (in property-paths-to-voted-anchor.lisp), but it involves two DAGs.
; It serves to establish one of the hypotheses of the intersection theorem
; cardinality-of-voters/previous-intersection (defined in the other file),
; namely the hypothesis that the certificates being intersected
; are in the same round.

(defruledl incoming+outgoing-same-round
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1))))
           (<= (set::cardinality
                (certificate-set->round-set
                 (set::union (incoming cert1 dag1)
                             (outgoing cert2 dag2))))
               1))
  :rule-classes :linear
  :enable (set::cardinality
           round-set-of-incoming
           round-set-of-outgoing
           certificate-set->round-set-of-union))

; This is similar to the homonymous theorem for the single-DAG property
; (in property-paths-to-voted-anchor.lisp), but it involves two DAGs.
; It serves to establish one of the hypotheses of the intersection theorem
; cardinality-of-voters/previous-intersection (defined in the other file),
; namely the hypothesis that the total number of certificates has bound n,
; with n being the total number of validators in the DAGs here.

(defruledl incoming+outgoing-upper-bound
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1))))
           (<= (set::cardinality (set::union (incoming cert1 dag1)
                                             (outgoing cert2 dag2)))
               (set::cardinality vals)))
  :rule-classes :linear
  :enable (cardinality-bound-when-same-round-and-unequiv
           certificate-sets-unequivocalp-when-subsets
           incoming+outgoing-same-round
           certificate-set-unequivocalp-when-subset
           cert-set->author-set-of-union
           cert-set->author-set-monotone
           certificate-set-unequivocalp-of-union
           incoming-subset
           outgoing-subset
           set::expensive-rules)
  :disable (set::expand-cardinality-of-union
            certificate-set->round-set-of-union))

; This is similar to the homonymous theorem for the single-DAG property
; (in property-paths-to-voted-anchor.lisp), but it involves two DAGs.
; It instantiates the abstract intersection theorem,
; cardinality-of-voters/previous-intersection,
; to the situation of interest, with the certificates from the two DAGs.

(defruledl not-emptyp-intersect-of-incoming-and-outgoing
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1)))
                (>= (set::cardinality (incoming cert1 dag1))
                    (1+ f))
                (equal (set::cardinality (outgoing cert2 dag2))
                       (- (set::cardinality vals) f)))
           (not (set::emptyp (set::intersect (incoming cert1 dag1)
                                             (outgoing cert2 dag2)))))
  :enable (incoming+outgoing-upper-bound
           incoming+outgoing-same-round
           certificate-set-unequivocalp-when-subset
           certificate-sets-unequivocalp-when-subsets)
  :use ((:instance cardinality-of-voters/previous-intersection
                   (certs1 (incoming cert1 dag1))
                   (certs2 (outgoing cert2 dag2))
                   (n (set::cardinality vals)))
        (:instance set::cardinality-zero-emptyp
                   (x (set::intersect (incoming cert1 dag1)
                                      (outgoing cert2 dag2)))))
  :disable (set::cardinality-zero-emptyp
            certificate-set->round-set-of-union))

; Similarly to the proof of the single-DAG property,
; having shown the non-empty intersection,
; we define a function that picks an element from that intersection,
; and we show that it is indeed common to the two DAGs
; and to the incoming and outgoing sets of certificates.
; The theorem is similar to the homonymous one for the single-DAG property.

(local
 (defund common (anchor witness dag1 dag2)
   (set::head (set::intersect (incoming anchor dag1)
                              (outgoing witness dag2)))))

(defruledl common-in-incoming-and-outgoing-and-dags
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (set::in witness dag2)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (and (set::in (common anchor witness dag1 dag2)
                         (incoming anchor dag1))
                (set::in (common anchor witness dag1 dag2)
                         (outgoing witness dag2))
                (set::in (common anchor witness dag1 dag2)
                         dag1)
                (set::in (common anchor witness dag1 dag2)
                         dag2)))
  :enable (common
           anchorp
           not-emptyp-intersect-of-incoming-and-outgoing
           cardinality-of-outgoing-quorum
           set::head-of-intersect-member-when-not-emptyp)
  :use ((:instance incoming-in-dag
                   (cert anchor)
                   (cert1 (common anchor witness dag1 dag2))
                   (dag dag1))
        (:instance outgoing-in-dag
                   (cert witness)
                   (cert1 (common anchor witness dag1 dag2))
                   (dag dag2))))

; There is a path from the common certificate to the anchor, in DAG2.
; This is not as obvious as in the single-DAG example,
; where there is obviously a path from an incoming certificate.
; Here we need to use the property that, across unequivocal certificates,
; paths from common certificates are the same.

(defruledl path-from-common-to-anchor
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (set::in witness dag2)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (equal (path-to-author+round (common anchor witness dag1 dag2)
                                        (certificate->author anchor)
                                        (certificate->round anchor)
                                        dag2)
                  anchor))
  :enable (anchorp
           path-from-incoming)
  :use (common-in-incoming-and-outgoing-and-dags
        (:instance path-to-author+round-of-unequivocal-dags
                   (author (certificate->author anchor))
                   (round (certificate->round anchor))
                   (cert (common anchor witness dag1 dag2)))))

; Fron the previous theorem,
; and the fact that something satisfying ANCHORP is not NIL,
; it follows that the anchor is also in DAG 2, besides DAG 1.

(defruledl anchor-also-in-dag2
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (set::in witness dag2)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (set::in anchor dag2))
  :use (common-in-incoming-and-outgoing-and-dags
        path-from-common-to-anchor
        (:instance path-to-author+round-in-dag
                   (dag dag2)
                   (author (certificate->author anchor))
                   (round (certificate->round anchor))
                   (cert (common anchor witness dag1 dag2))))
  :enable not-anchorp-of-nil
  :disable path-to-author+round-in-dag)

; This is similar to the homonymous theorem in the single-DAG proof,
; but it says that there is a path from a witness in round + 2
; to the anchor in round r, in DAG 2,
; under assumptions involving DAG 1.
; The witness nomenclature is the same as in the single-DAG proof:
; it arises from a proof about DEFUN-SK, below.

(defruledl path-from-witness-to-anchor
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (set::in witness dag2)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (equal (path-to-author+round witness
                                        (certificate->author anchor)
                                        (certificate->round anchor)
                                        dag2)
                  anchor))
  :use ((:instance path-to-author+round-transitive
                   (cert witness)
                   (cert1 (common anchor witness dag1 dag2))
                   (cert2 anchor)
                   (dag dag2))
        path-from-common-to-anchor
        anchor-also-in-dag2
        common-in-incoming-and-outgoing-and-dags)
  :enable path-to-outgoing)

; This is similar to the homonymous theorem in the single-DAG proof,
; but it involves the two DAGs.
; It's the base case of our induction,
; It uses the theorem just above,
; instantiating the witness with the one arising from the DEFUN-SK.

(defruledl dag-round-all-path-to-p-base-case
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f)))
           (dag-round-all-path-to-p (+ 2 (certificate->round anchor))
                                    anchor
                                    dag2))
  :enable (dag-round-all-path-to-p)
  :use (:instance path-from-witness-to-anchor
                  (witness (dag-round-all-path-to-p-witness
                            (+ 2 (certificate->round anchor))
                            anchor
                            dag2))))

; For the step case of the induction, we need to pick predecessors,
; which we do with the following function, identical to the one defined
; in the proof for the single DAG.
; We show that this is indeed a predecessor,
; it is in one round less than the input,
; and there is a path to it from the input.

(local
 (defund predecessor (cert dag)
   (set::head (outgoing cert dag))))

(defruledl predecessor-in-outgoing
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (not (zp quorum))
                (set::in cert dag)
                (not (equal (certificate->round cert) 1)))
           (set::in (predecessor cert dag)
                    (outgoing cert dag)))
  :enable (predecessor
           set::emptyp)
  :use cardinality-of-outgoing-quorum)

(defruledl round-of-predecessor
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (not (zp quorum))
                (set::in cert dag)
                (not (equal (certificate->round cert) 1)))
           (equal (certificate->round (predecessor cert dag))
                  (1- (certificate->round cert))))
  :use (:instance round-in-outgoing-is-one-less
                  (cert1 (predecessor cert dag)))
  :enable predecessor-in-outgoing)

(defruledl path-to-predecessor
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (not (zp quorum))
                (set::in cert dag)
                (not (equal (certificate->round cert) 1)))
           (equal (path-to-author+round
                   cert
                   (certificate->author (predecessor cert dag))
                   (certificate->round (predecessor cert dag))
                   dag)
                  (predecessor cert dag)))
  :enable (predecessor-in-outgoing
           path-to-outgoing))

; This is similar to the homonymous theorem in the single-DAG proof,
; but with a slightly weaker assumption, namely that CERT is not NIL,
; as opposed to CERT being in the DAG.
; This facilitates the final proof by induction,
; because the theorem ANCHOR-ALSO-IN-DAG2 includes hypotheses
; about the witness certificate in round r+2,
; which are not readily available during the induction step.
; Indeed, note that the anchor is also in DAG 2
; only if there is some certificate at round r+2 or later;
; otherwise, the anchor may not be in DAG 2 at all.
; But by using the weaker hypothesis that CERT is not NIL,
; we can easily relieve this hypothesis from the fact that
; the anchor is in DAG 1, which implies that it is not NIL.

(defruledl dag-round-all-path-to-p-of-next-round
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (not (zp quorum))
                cert ; weaker than (set::in cert dag)
                (posp round)
                (dag-round-all-path-to-p round cert dag))
           (dag-round-all-path-to-p (1+ round) cert dag))
  :expand (dag-round-all-path-to-p (1+ round) cert dag)
  :use ((:instance path-to-author+round-transitive
                   (cert (dag-round-all-path-to-p-witness
                          (+ 1 round) cert dag))
                   (cert1 (predecessor (dag-round-all-path-to-p-witness
                                        (+ 1 round) cert dag)
                                       dag))
                   (cert2 cert))
        (:instance path-to-predecessor
                   (cert (dag-round-all-path-to-p-witness
                          (+ 1 round) cert dag)))
        (:instance dag-round-all-path-to-p-necc
                   (cert1 (predecessor (dag-round-all-path-to-p-witness
                                        (+ 1 round) cert dag)
                                       dag)))
        (:instance predecessor-in-outgoing
                   (cert (dag-round-all-path-to-p-witness
                          (+ 1 round) cert dag)))
        (:instance round-of-predecessor
                   (cert (dag-round-all-path-to-p-witness
                          (+ 1 round) cert dag)))
        (:instance path-to-author+round-in-dag
                   (cert (predecessor (dag-round-all-path-to-p-witness
                                       (+ 1 round) cert dag)
                                      dag))
                   (author (certificate->author cert))
                   (round (certificate->round cert))))
  :disable path-to-author+round-in-dag
  :enable (outgoing-subset
           set::expensive-rules))

; This is the same as the homonymous theorem in the single-DAG proof.

(defruledl f-below-cardinality-of-vals
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::subset (cert-set->author-set dag) vals)
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f)))
           (> (set::cardinality vals) f))
  :rule-classes :linear
  :enable (set::expensive-rules
           certificate-set-unequivocalp-when-subset
           incoming-subset
           incoming-same-round)
  :use ((:instance cardinality-of-authors-when-same-round-and-unequiv
                   (certs (incoming anchor dag)))
        (:instance cert-set->author-set-monotone
                   (certs1 (incoming anchor dag))
                   (certs2 dag)))
  :disable (cardinality-of-authors-when-same-round-and-unequiv
            cert-set->author-set-monotone))

; This is almost the same as the homonymous theorem in the single-DAG proof,
; but with the weaker hypothesis that ANCHOR is not NIL,
; as opposed to satisfying ANCHORP.
; The motivation is the same as for the theorem
; DAG-ROUND-ALL-PATH-TO-P-OF-NEXT-ROUND explained above.

(defruledl dag-round-all-path-to-p-step-case
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                anchor ; weaker than (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag) vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag (- (set::cardinality vals) f))
                (> (set::cardinality vals) f)
                (natp round-delta)
                (natp f)
                (dag-round-all-path-to-p (+ round-delta
                                            (+ 2 (certificate->round anchor)))
                                         anchor
                                         dag))
           (dag-round-all-path-to-p (+ (1+ round-delta)
                                       (+ 2 (certificate->round anchor)))
                                    anchor
                                    dag))
  :use ((:instance dag-round-all-path-to-p-of-next-round
                   (cert anchor)
                   (quorum (- (set::cardinality vals) f))
                   (round (+ round-delta
                             (certificate->round anchor)
                             2))))
  :enable anchorp)

; This is similar to the homonymous theorem in the single-DAG proof,
; also proved by induction on ROUND-DELTA.

(defruledl dag-round-all-path-to-p-of-round-delta
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (natp round-delta)
                (natp f))
           (dag-round-all-path-to-p (+ round-delta
                                       (+ 2 (certificate->round anchor)))
                                    anchor
                                    dag2))
  :induct (acl2::dec-induct round-delta)
  :enable (f-below-cardinality-of-vals
           not-anchorp-of-nil)
  :hints ('(:use (dag-round-all-path-to-p-base-case
                  (:instance dag-round-all-path-to-p-step-case
                             (round-delta (1- round-delta))
                             (dag dag2))))))

; This is similar to the homonymous theorem in the single-DAG proof.
; It is just a rephrasing of the previous one
; in the form we need for the final proof,
; while the previous one was tailored to induction.

(defruledl dag-round-all-path-to-p-holds
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (natp f)
                (natp round)
                (>= round
                    (+ 2 (certificate->round anchor))))
           (dag-round-all-path-to-p round anchor dag2))
  :use (:instance dag-round-all-path-to-p-of-round-delta
                  (round-delta (- round (+ 2 (certificate->round anchor)))))
  :enable (fix natp))

; This is the final theorem,
; similar to DAG-ALL-PATH-TO-P-HOLDS in the single-DAG file.

(defruled dag-all-path-to-p-other-holds
  :short "This is the property
          described in @(see property-paths-to-voted-anchor)."
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (anchorp anchor dag1 vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag1) vals)
                (set::subset (cert-set->author-set dag2) vals)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (dag-previous-are-quorum-p dag2
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag1))
                    (1+ f))
                (natp f))
           (dag-all-path-to-p anchor dag2))
  :enable (dag-all-path-to-p-alt-def
           dag-all-path-to-p-alt)
  :use (:instance dag-round-all-path-to-p-holds
                  (round (dag-all-path-to-p-alt-witness anchor dag2))))
