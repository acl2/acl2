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

(include-book "operations-unequivocal-certificates")
(include-book "operations-anchors")
(include-book "properties-dags")

(include-book "std/basic/inductions" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-paths-to-voted-anchor
  :parents (correctness)
  :short "Property that if an anchor in a DAG has enough votes
          then all the certificates in the DAG
          that are at least two rounds after the anchor
          have some path to the anchor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a core property of AleoBFT.
     Take an anchor @($A$) (or any certificate, for that matter) in a DAG,
     with at least @($F+1$) votes
     (where @($F$) is introduced in @(tsee max-faulty-for-total)),
     i.e. at least @($F+1$) incoming edges from certificates
     in the round just after @($A$).
     Then if there is a(ny) certificate @($C$) two rounds after @($A$),
     it must have edges to @($N-F$) certificates in the round just before,
     which is the round just after @($A$).
     Since there can be at most @($N$) certificates in that round
     (the one just after @($A$) and just before @($C$)),
     an intersection argument shows that there must be a certificate @($B$)
     between @($A$) and @($C$).
     That is, there is a path from @($C$) to @($A$).
     The intersection argument is similar to quorum intersection,
     but it has a very different purpose:
     it has nothing to do with correct or faulty validators;
     it is just about paths in DAGs.
     Note that the above holds for every @($C$) two rounds after @($A$).
     Any certificate @($D$) in the round after @($C$)
     must have predecessors in the previous round,
     which, as argued, all have paths to @($A$),
     and therefore every @($D$) has a path to @($A$) as well.
     Thus, every certificate at least two rounds after @($A$)
     has a path to @($A$).")
   (xdoc::p
    "Here we prove this property on DAGs, not as an system invariant,
     since it is easier to understand just on DAGs first,
     and there are generally advantages in more modularity.
     In particular, we use a generic @('f')
     for the @($F$) of the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-all-path-to-p ((cert certificatep) (dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if all the certificates
          that are at least two rounds after a given certificate
          have a path to that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the predicate expressing the key property that we prove here,
     where @('cert') is the anchor,
     but in fact it could be any certificate, not necessarily an anchor.
     We universally quantify over a generic certificate @('cert1')
     whose round is greater than or equal to
     two plus the round of the given certificate @('cert').
     The existence of the path is expressed by saying that
     @(tsee path-to-author+round) applied to @('cert1')
     with the author and round of @('cert') as targets
     yields exactly @('cert')."))
  (forall (cert1)
          (implies (and (set::in cert1 dag)
                        (>= (certificate->round cert1)
                            (+ 2 (certificate->round cert))))
                   (equal (path-to-author+round cert1
                                                (certificate->author cert)
                                                (certificate->round cert)
                                                dag)
                          cert)))

  ///

  ;; If the DAG has at least one certificate at least two rounds after CERT,
  ;; then CERT must be in the DAG, because there is at least a path to it.

  (defruled dag-all-path-to-p-in-dag
    (implies (and (certificate-setp dag)
                  (dag-all-path-to-p cert dag)
                  (set::in cert1 dag)
                  (>= (certificate->round cert1)
                      (+ 2 (certificate->round cert)))
                  cert)
             (set::in cert dag))
    :enable path-to-author+round-in-dag
    :disable (dag-all-path-to-p
              dag-all-path-to-p-necc)
    :use dag-all-path-to-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As hinted at in :DOC PROPERTY-PATHS-TO-VOTED-ANCHOR,
; our property of interest is proved by induction on rounds,
; starting from two rounds after the anchor.
; For this purpose, it is convenient to rephrase
; the definition of DAG-ALL-PATH-TO-P
; so that it is amenable to induction.
; This is done in DAG-ROUND-ALL-PATH-TO-P-ALT below,
; which makes use of DAG-ROUND-ALL-PATH-TO-P,
; which is similar to DAG-ROUND-ALL-PATH-TO-P
; but it restricts the quantified certificate to a given round.
; We put in the guard the restriction that
; the round is at least two more than the anchor,
; even though we do not really need a guard here,
; since we use this function purely as a vehicle for a proof.

(define-sk dag-round-all-path-to-p ((round posp)
                                    (cert certificatep)
                                    (dag certificate-setp))
  :guard (>= round (+ 2 (certificate->round cert)))
  :returns (yes/no booleanp)
  (forall (cert1)
          (implies (and (set::in cert1 dag)
                        (equal (certificate->round cert1) round))
                   (equal (path-to-author+round cert1
                                                (certificate->author cert)
                                                (certificate->round cert)
                                                dag)
                          cert))))

; This is the alternative definition of DAG-ALL-PATH-TO-P mentioned above.
; This universally quantifies the restricted DAG-ROUND-ALL-PATH-TO-P
; over the rounds that are at least two after the given certificate.

(define-sk dag-all-path-to-p-alt ((cert certificatep) (dag certificate-setp))
  :returns (yes/no booleanp)
  (forall (round)
          (implies (and (posp round)
                        (>= round (+ 2 (certificate->round cert))))
                   (dag-round-all-path-to-p round cert dag))))

; Equivalence between DAG-ALL-PATH-TO-P and DAG-ALL-PATH-TO-P-ALT.
; The proof is conceptually simple,
; but it takes a few steps to deal with the quantifiers.

(defruled dag-all-path-to-p-alt-def
  (equal (dag-all-path-to-p cert dag)
         (dag-all-path-to-p-alt cert dag))
  :use (dag-all-path-to-p-alt-when-dag-all-path-to-p
        dag-all-path-to-p-when-dag-all-path-to-p-alt)

  :prep-lemmas

  ((defruled dag-round-all-path-to-p-when-dag-all-path-to-p
     (implies (and (dag-all-path-to-p cert dag)
                   (posp round)
                   (>= round (+ 2 (certificate->round cert))))
              (dag-round-all-path-to-p round cert dag))
     :enable (dag-round-all-path-to-p
              dag-all-path-to-p-necc))

   (defruled dag-all-path-to-p-alt-when-dag-all-path-to-p
     (implies (dag-all-path-to-p cert dag)
              (dag-all-path-to-p-alt cert dag))
     :enable (dag-all-path-to-p-alt
              dag-round-all-path-to-p-when-dag-all-path-to-p))

   (defruled dag-all-path-to-p-when-dag-all-path-to-p-alt
     (implies (dag-all-path-to-p-alt cert dag)
              (dag-all-path-to-p cert dag))
     :use (:instance dag-all-path-to-p-alt-necc
                     (round (certificate->round
                             (dag-all-path-to-p-witness cert dag))))
     :enable (dag-all-path-to-p
              dag-round-all-path-to-p-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove the intersection argument
; sketched in :DOC PROPERTY-PATHS-TO-VOTED-ANCHOR,
; via a number of theorems.

; Consider two sets of certificates, all in the same round r.
; The first set represents the f+1 or more votes for an anchor at round r-1.
; The second set represents the n-f predecessors of a certificate in round r+1.
; The total number of certificate is n or less.
; Then the intersection of the two certificates must be non-empty.
; This is the abstract fact, but we need further theorems
; to properly instantiate the abstract entities in this fact.

; We make this theorem non-local (unlike the subsequent ones),
; because we re-use it in property-paths-to-other-voted-anchor.lisp.

(defruled cardinality-of-voters/previous-intersection
  (implies (and (<= (set::cardinality (set::union certs1 certs2)) n)
                (>= (set::cardinality certs1) (1+ f))
                (equal (set::cardinality certs2) (- n f)))
           (>= (set::cardinality (set::intersect certs1 certs2)) 1))
  :rule-classes :linear
  :enable set::expand-cardinality-of-intersect
  :disable (set::expand-cardinality-of-union
            set::cardinality-zero-emptyp))

; Given two certificates CERT and CERT1 two rounds apart,
; the incoming certificates of CERT
; and the outgoing certificates of CERT
; are all in the same round, between the two rounds.
; This follows mainly from facts about INCOMING and OUTGOING proved elsewhere.

(defruledl incoming+outgoing-subset-same-round
  (implies (and (certificate-setp dag)
                (equal (certificate->round cert1)
                       (+ 2 (certificate->round cert))))
           (set::subset
            (set::union (incoming cert dag)
                        (outgoing cert1 dag))
            (certs-with-round (1+ (certificate->round cert)) dag)))
  :enable set::expensive-rules
  :use ((:instance incoming-subset-of-next-round)
        (:instance outgoing-subset-of-previous-round (cert cert1)))
  :disable (incoming-subset-of-next-round
            outgoing-subset-of-previous-round))

; This says eseentially the same as the previous theorem,
; but in a different form, which is more usable elsewhere.

(defruledl incoming+outgoing-same-round
  (implies (and (certificate-setp dag)
                (equal (certificate->round cert1)
                       (+ 2 (certificate->round cert))))
           (<= (set::cardinality
                (cert-set->round-set
                 (set::union (incoming cert dag)
                             (outgoing cert1 dag))))
               1))
  :rule-classes :linear
  :enable (cardinality-of-subset-of-round-set-of-round
           cert-set->author-set-monotone)
  :use incoming+outgoing-subset-same-round
  :disable (incoming+outgoing-subset-same-round
            cert-set->round-set-of-union))

; We show that, given again certificates CERT and CERT1 two rounds apart,
; the number of incoming certificates of CERT and outgoing certificates of CERT1
; is bounded by the number of validators, generically represented as VALS here.

(defruledl incoming+outgoing-upper-bound
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::subset (cert-set->author-set dag)
                             vals)
                (equal (certificate->round cert1)
                       (+ 2 (certificate->round cert))))
           (<= (set::cardinality (set::union (incoming cert dag)
                                             (outgoing cert1 dag)))
               (set::cardinality vals)))
  :rule-classes :linear
  :enable (incoming+outgoing-same-round
           cardinality-bound-when-same-round-and-unequiv
           certificate-set-unequivocalp-when-subset
           cert-set->author-set-monotone
           incoming-subset
           outgoing-subset
           set::expensive-rules)
  :disable (set::expand-cardinality-of-union
            cert-set->round-set-of-union))

; Finally, we instantiate the abstract fact proved earlier,
; namely CARDINALITY-OF-VOTERS/PREVIOUS-INTERSECTION.
; Given certificates CERT and CERT1 two rounds apart,
; the intersection of the incoming certificates of CERT
; with the outgoing certificates of CERT1 is not empty.
; The theorems proved above are used to establish and instantiate
; the hypotheses in the abstract fact.

(defruledl not-emptyp-intersect-of-incoming-and-outgoing
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (set::in cert1 dag)
                (equal (certificate->round cert1)
                       (+ 2 (certificate->round cert)))
                (set::subset (cert-set->author-set dag)
                             vals)
                (>= (set::cardinality (incoming cert dag))
                    (1+ f))
                (equal (set::cardinality (outgoing cert1 dag))
                       (- (set::cardinality vals) f)))
           (not (set::emptyp (set::intersect (incoming cert dag)
                                             (outgoing cert1 dag)))))
  :enable (incoming+outgoing-upper-bound
           incoming+outgoing-same-round
           certificate-set-unequivocalp-when-subset)
  :use ((:instance cardinality-of-voters/previous-intersection
                   (certs1 (incoming cert dag))
                   (certs2 (outgoing cert1 dag))
                   (n (set::cardinality vals)))
        (:instance set::cardinality-zero-emptyp
                   (x (set::intersect (incoming cert dag)
                                      (outgoing cert1 dag)))))
  :disable (set::cardinality-zero-emptyp
            cert-set->round-set-of-union))

; Above we have shown that there is an intersection between
; the incoming and outgoing certificates of two certificates two rounds apart.
; We define a local function that picks a certificate from that intersection,
; i.e. a common certificate between the two sets.
; The first certificate is the anchor at round r.
; The second certificate is called WITNESS because it will be the witness
; in a proof about a DEFUN-SK below;
; regardless of what it is called, it is the certificate at round r+2.
; The function returns a certificate at round r+1.

(local
 (defund common (anchor witness dag)
   (set::head (set::intersect (incoming anchor dag)
                              (outgoing witness dag)))))

; We show that the function COMMON just defined returns,
; under the appropriate conditions, a certificate that is
; in the DAG,
; in the incoming certificates of the anchor,
; and in the outgoing certificates of the witness.

(defruledl common-in-incoming-and-outgoing-and-dag
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f))
                (set::in witness dag)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (and (set::in (common anchor witness dag)
                         (incoming anchor dag))
                (set::in (common anchor witness dag)
                         (outgoing witness dag))
                (set::in (common anchor witness dag)
                         dag)))
  :enable (common
           anchorp
           not-emptyp-intersect-of-incoming-and-outgoing
           cardinality-of-outgoing-quorum
           set::head-of-intersect-member-when-not-emptyp)
  :use (:instance incoming-in-dag
                  (cert anchor)
                  (cert1 (common anchor witness dag))))

; Under the same conditions as the above,
; there is a path from the witness to the anchor,
; via the common certificate returned by COMMON.
; We use the theorems about
; paths between certificates and their incoming and outgoing certificates,
; and of course the transitivity of paths.

(defruledl path-from-witness-to-anchor
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f))
                (set::in witness dag)
                (equal (certificate->round witness)
                       (+ 2 (certificate->round anchor))))
           (equal (path-to-author+round witness
                                        (certificate->author anchor)
                                        (certificate->round anchor)
                                        dag)
                  anchor))
  :use ((:instance path-to-author+round-transitive
                   (cert witness)
                   (cert1 (common anchor witness dag))
                   (cert2 anchor))
        common-in-incoming-and-outgoing-and-dag)
  :enable (path-to-outgoing
           path-from-incoming
           anchorp))

; The previous theorem essentially proves the base case of our induction.
; The next theorem is the actual base case:
; we prove DAG-ROUND-ALL-PATH-TO-P for round r+2,
; where r is the round of the anchor.
; When we open DAG-ROUND-ALL-PATH-TO-P,
; that exposes the witness,
; which corresponds to the variable WITNESS in the theorems above.
; With reference to :DOC PROPERTY-PATHS-TO-VOTED-ANCHOR,
; this base case shows that there is a path from C to A,
; via B, which is returned by COMMON.

(defruledl dag-round-all-path-to-p-base-case
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f)))
           (dag-round-all-path-to-p (+ 2 (certificate->round anchor))
                                    anchor
                                    dag))
  :enable (dag-round-all-path-to-p)
  :use (:instance path-from-witness-to-anchor
                  (witness (dag-round-all-path-to-p-witness
                            (+ 2 (certificate->round anchor))
                            anchor
                            dag))))

; Now we need to prove the step case of the induction.
; Here is where we take a certificate from a round after r+2,
; and obtain a predecessor, which has a path to A by induction hypothesis.
; We define a local function to obtain such predecessor.

(local
 (defund predecessor (cert dag)
   (set::head (outgoing cert dag))))

; We show that, under suitable conditions,
; PREDECESSOR returns a certificate in OUTGOING,
; the returned certificate is the round just before the input certificate,
; and there is a path from the input certificate to the output certificate.

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

; Now we prove the essence of the induction step.
; If DAG-ROUND-ALL-PATH-TO-P holds on a round r,
; it also holds on a round r+1.
; We use the properties of PREDECESSOR proved above,
; and path transitivity of course.

(defruledl dag-round-all-path-to-p-of-next-round
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (not (zp quorum))
                (set::in cert dag)
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
                          (+ 1 round) cert dag))))
  :enable (outgoing-subset
           set::expensive-rules))

; To prove the actual induction step below,
; we need the fact that n-f > 0, i.e. f < n.
; Here n is the number of validators VALS.
; The inequality derives from the fact that
; there are at least f+1 certificates in a round, and at most n,
; and therefore f+1 <= n, i.e. f < n.

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

; The following is the actual step case,
; where instead of a generic round r and r+1
; we use a+2+d and a+2+d+1,
; where a is the round of the anchor and d is a generic 'delta' from a+2.

(defruledl dag-round-all-path-to-p-step-case
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
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

; We prove by induction that DAG-ROUND-ALL-PATH-TO-P holds
; for every round of the form a+2+d,
; where a is the round of the anchor, and d >= 0.

(defruledl dag-round-all-path-to-p-of-round-delta
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f))
                (natp round-delta)
                (natp f))
           (dag-round-all-path-to-p (+ round-delta
                                       (+ 2 (certificate->round anchor)))
                                    anchor
                                    dag))
  :induct (acl2::dec-induct round-delta)
  :enable f-below-cardinality-of-vals
  :hints ('(:use (dag-round-all-path-to-p-base-case
                  (:instance dag-round-all-path-to-p-step-case
                             (round-delta (1- round-delta)))))))

; This is essentially the same as the previous theorem,
; for a generic round r >= a+2.

(defruledl dag-round-all-path-to-p-holds
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f))
                (natp f)
                (natp round)
                (>= round
                    (+ 2 (certificate->round anchor))))
           (dag-round-all-path-to-p round anchor dag))
  :use (:instance dag-round-all-path-to-p-of-round-delta
                  (round-delta (- round (+ 2 (certificate->round anchor)))))
  :enable (fix natp))

; Finally, we show that DAG-ALL-PATH-TO-P holds,
; using its equivalence with DAG-ALL-PATH-TO-P-ALT.

(defruled dag-all-path-to-p-holds
  :short "This is the property
          described in @(see property-paths-to-voted-anchor)."
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (anchorp anchor dag vals)
                (not (set::emptyp vals))
                (set::subset (cert-set->author-set dag)
                             vals)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag
                                           (- (set::cardinality vals) f))
                (>= (set::cardinality (incoming anchor dag))
                    (1+ f))
                (natp f))
           (dag-all-path-to-p anchor dag))
  :enable (dag-all-path-to-p-alt-def
           dag-all-path-to-p-alt)
  :use (:instance dag-round-all-path-to-p-holds
                  (round (dag-all-path-to-p-alt-witness anchor dag))))
