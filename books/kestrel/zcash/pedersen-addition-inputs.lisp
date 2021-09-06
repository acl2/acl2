; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/zcash/pedersen-hash" :dir :system)
(include-book "kestrel/fty/nat-set" :dir :system)

(local (include-book "std/basic/inductions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a proof of Theorem A.3.5 from [ZPS].
; This file currently uses short and generic names for functions and theorems,
; and therefore it should only be included locally in other books.

; Theorem A.3.5 is critical to the correctness of the Pedersen gadget.
; Here we formulate and prove this theorem slightly differently from [ZPS]:
; the reason is that our formulation and proof is more appropriate for ACL2
; (while the formulation and proof in [ZPS] are appropriate for that document).

; [ZPS] formulates Theorem A.3.5 in terms of
; summations over sets S and S' of indices in {1,...,c} with c = 63,
; reasoning about them directly, without induction;
; it also makes a shift from enc to enc',
; with a final argument in terms of hex digits.
; Here instead we prove the theorem by induction over more general summations,
; i.e. for sets S and S' of indices in {1,...,c} for arbitrary c.
; Roughly speaking, the key to the induction step is that,
; as we add an index c+1 to S or S', say S for concreteness,
; the term of the summation corresponding to c+1 is so large that
; adding the previous summation over S keeps it
; larger that the summation over S',
; and therefore the summation over S plus c+1
; must be different from the summation over S'.
; In order for this argument to work,
; we need to show first that each summation is not too large;
; more precisely, we prove, by induction, that it is below a certain limit.
; Here 'large' and 'small' and 'limit' refer to absolute values:
; the summations may be negative.
; All of this is explained more precisely in the development below.

; The functions defined in this file are currently only used in proofs.
; Thus, they do not need to be guard-verified.
; Nevertheless, we guard-verify them as validation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; [ZPS] uses indices that start with 1,
; but here we use indices that start with 0 instead,
; which seem more natural in an ACL2 proof.
; [ZPS] uses sets S and S' of indices in {1,...,c}.
; Here we use sets of indices in {0,...,n-1},
; characterized by the following predicate,
; which says whether all the elements of a set of naturals are below n.
; We prove some theorems about this predicate,
; which we need for subsequent proofs.

(define belowp ((indices nat-setp) (n natp))
  :returns (yes/no booleanp)
  (or (set::empty indices)
      (and (< (set::head indices) n)
           (belowp (set::tail indices) n)))
  ///

  (defruled head-below-when-belowp
    (implies (and (belowp indices n)
                  (not (set::empty indices)))
             (< (set::head indices) n))
    :rule-classes :linear)

  (defruled belowp-of-tail
    (implies (belowp indices n)
             (belowp (set::tail indices) n)))

  (defruled belowp-of-larger
    (implies (and (belowp indices n)
                  (>= m n))
             (belowp indices m)))

  (defruled belowp-of-n-minus-1-when-not-in-set
    (implies (and (posp n)
                  (nat-setp indices)
                  (belowp indices n)
                  (not (set::in (1- n) indices)))
             (belowp indices (1- n))))

  (defruled belowp-of-delete
    (implies (belowp indices n)
             (belowp (set::delete index indices) n))
    :enable set::delete)

  (defrule belowp-of-0
    (implies (nat-setp indices)
             (equal (belowp indices 0)
                    (set::empty indices)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we define the summations over sets of indices.
; Consistently with our formalization of Pedersen hash,
; we use lists of bits of length multiple of 3 as the m's.
; The indices are multiplied by 3 and index chunks of 3 bits.
; The guard ensures that the list of bits is long enough
; that the indices in the set are valid.
; We prove some theorems about this function,
; which we need for subsequent proofs.

(define sum ((indices nat-setp) (bits bit-listp))
  :guard (and (integerp (/ (len bits) 3))
              (belowp indices (/ (len bits) 3)))
  :returns (sum integerp :rule-classes (:rewrite :type-prescription))
  (cond ((set::empty indices) 0)
        (t (b* ((index (acl2::lnfix (set::head indices))))
             (+ (* (pedersen-enc (take 3 (nthcdr (* 3 index) bits)))
                   (expt 16 index))
                (sum (set::tail indices) bits)))))
  :prepwork
  ((local (include-book "arithmetic/top" :dir :system))) ; for :returns

  :verify-guards nil ; done below
  ///
  (encapsulate ()
    (local (include-book "std/lists/nthcdr" :dir :system))
    (verify-guards sum
      :hints (("Goal" :in-theory (enable belowp-of-tail
                                         head-below-when-belowp)))))

  (defruled sum-of-insert
    (implies (and (natp index)
                  (not (set::in index indices)))
             (equal (sum (set::insert index indices) bits)
                    (+ (sum indices bits)
                       (* (pedersen-enc (take 3 (nthcdr (* 3 index) bits)))
                          (expt 16 index)))))
    :induct (set::weak-insert-induction index indices))

  (defruled sum-to-sum-of-delete
    (implies (and (natp index)
                  (set::in index indices))
             (equal (sum indices bits)
                    (+ (sum (set::delete index indices) bits)
                       (* (pedersen-enc (take 3 (nthcdr (* 3 index) bits)))
                          (expt 16 index)))))
    :use (:instance sum-of-insert (indices (set::delete index indices))))

  (defrule sum-of-0
    (implies (set::empty indices)
             (equal (sum indices bits)
                    0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Since pedersen-enc always returns an integer between -4 and +4,
; each addend in SUM above is between -4 * 16^i and +4 * 16^i,
; where i is the index of the addend.
; If i is the largest index of the set of indices that the summation is over,
; the total sum may of course go beyond that interval,
; as we add other addends (which may be positive or negative).
; However, it does not got too much beyond that interval,
; as the addends for lower indices are smaller.
; A little experimentation and thought suggests that
; the total sum is always between -8 * 16^i and +8 * 16^i,
; which the proofs below confirm to be correct.
; That is, we double the limits of the interval.
; It may be possible to use smaller intervals,
; but this suffices to prove Theorem A.3.5;
; it is important, though, that the interval is open,
; i.e. that -8 * 16^i and +8 * 16^i are excluded.
; We start by defining a predicate expressing that
; something is in that open interval:
; the argument n describes the interval between -8 * 16^(n-1) and +8 * 16^(n-1).
; We also prove a theorem, which we need in subsequent proofs.

(define rangep ((x integerp) (n natp))
  :returns (yes/no booleanp)
  (and (< (- (* 8 (expt 16 (1- n))))
          x)
       (< x
          (* 8 (expt 16 (1- n)))))
  ///

  (defruled rangep-of-larger
    (implies (and (natp n)
                  (posp m)
                  (rangep x n)
                  (>= m n))
             (rangep x m))
    :enable rangep
    :use (lemma)
    :prep-lemmas
    ((defrule lemma
       (implies (and (posp m)
                     (natp n)
                     (>= m n))
                (>= (* 8 (expt 16 (1- m)))
                    (* 8 (expt 16 (1- n)))))
       :rule-classes nil
       :prep-books ((include-book "arithmetic/top" :dir :system))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove that a summation over indices all below n,
; i.e. a set of indices taken from {0,...,n-1},
; yields a result in the range from -8 * 16^(n-1) to +8 * 16^(n-1).
; We prove that by induction on n.
; If we merely have the set of indices of the summation
; universally quantified in the theorem,
; the induction hypothesis will use the same set of indices as the conclusion.
; This does not work, as the proof may need the induction hypothesis
; on a different set of indices (see below).
; That is, the induction hypothesis must be universally quantifier
; over all sets of indices that are all below n-1.
; Thus, we introduce a predicate over n that captures what we want to prove;
; the predicate universally quantifies the set of indices.

(define-sk range-thm ((n natp) (bits bit-listp))
  :guard (and (integerp (/ (len bits) 3))
              (>= (len bits) (* 3 n)))
  :returns (yes/no booleanp)
  (forall (indices)
          (implies (and (nat-setp indices)
                        (belowp indices n))
                   (rangep (sum indices bits) n)))
  :guard-hints (("Goal" :use (:instance belowp-of-larger
                              (indices (range-thm-witness n bits))
                              (n n)
                              (m (/ (len bits) 3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With the predicate just above in hand,
; our task is essentially prove (range-thm n) by induction on n.
; We start with the base case, which is easy because
; in order for the set of indices to have elements all below 0,
; the set must be 0, and therefore the summation must be 0,
; which fits in the range.
; Note that, in this case, the range is between -1/2 and 1/2,
; while in all other cases (i.e. if n > 0) the range limits are integers;
; anyways, the range with non-integer liimts for n = 0 causes no issues,
; and provides a perfectly valid base case.

(defruled range-thm-base
  (range-thm 0 bits)
  :enable range-thm)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For the induction step, we need to prove (range-thm n)
; given (range-thm (1- n)) and that n is a non-zero natural number.
; Expanding (range-thm n), we obtain a formula to prove
; that involves the witness predicate, which is a bit hard to read.
; Thus, we prove the induction step over more general and readable variables,
; which we then instantiate to prove the induction step proper.
; More precisely, we prove the conclusion of the implication in range-thm
; given the premises of that implication
; and the induction hypothesis (range-thm (1- n)).

; The conclusion of the induction step involves a set of indices below n,
; which leads to two main cases, depending on whether n-1 is in the set or not.
; We prove the two cases separately, over generic variables.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If n-1 is not in the set of indices,
; then the induction hypothesis tells us that
; the summation is in the interval defined by n-1,
; which is therefore also in the larger interval defined by n.

; Instead of the Isar proof below,
; this could be proved as a DEFRULE
; with a single :USE with the lemma instances in the steps of the Isar proof.
; However, the Isar proof is more readable, do we leave it like this.

(defisar range-thm-step-when-not-in-set
  (implies (and (not (set::in (1- n) indices))
                (posp n)
                (range-thm (1- n) bits)
                (nat-setp indices)
                (belowp indices n))
           (rangep (sum indices bits)
                   n))
  :proof
  ((:assume (:not-in-set (not (set::in (1- n) indices))))
   (:assume (:pos (posp n)))
   (:assume (:ind-hyp (range-thm (1- n) bits)))
   (:assume (:nat-set (nat-setp indices)))
   (:assume (:below-n (belowp indices n)))
   (:derive (:below-n-1 (belowp indices (1- n)))
    :from (:pos :nat-set :below-n :not-in-set)
    :hints (("Goal" :use belowp-of-n-minus-1-when-not-in-set)))
   (:derive (:range-n-1 (rangep (sum indices bits) (1- n)))
    :from (:ind-hyp :nat-set :below-n-1)
    :hints (("Goal" :use (:instance range-thm-necc (n (1- n))))))
   (:derive (:range-n (rangep (sum indices bits) n))
    :from (:range-n-1 :pos)
    :hints (("Goal" :use (:instance rangep-of-larger
                          (x (sum indices bits))
                          (n (1- n))
                          (m n)))))
   (:qed))
  :disable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If n-1 is in the set of indices,
; we decompose the summation into the added for n-1
; and the summation over the set of other indices.
; We instantiate the induction hypothesis to the set of other indices,
; obtaining that their summation is
; between -8 * 16^(n-2) and +8 * 16^(n-2).
; Since pedersen-enc is between -4 and 4,
; we know that the addend for n-1 is
; between -4 * 16^(n-1) and +4 * 16^(n-1),
; which is the same as -64 * 16^(n-2) and +64 * 16^(n-2).
; Thus, the total summation is
; between (-8-64) * 16^(n-2) and (+8+64) * 16^(n-2),
; i.e. between -72 * 16^(n-2) and +72 * 16^(n-2),
; which is clearly also between -128 * 16^(n-2) and +128 * 16^(n-2),
; which is the same as between -8 * 16^(n-1) and +8 * 16^(n-1),
; which is the desired interval.

; The Isar proof clearly shows all these steps.
; We prove two arithmetic lemmas first, which we use in the Isar proof

(defruled pedersen-enc-times-expt-16-n
  (and (<= (- (* 4 (expt 16 n)))
           (* (pedersen-enc x) (expt 16 n)))
       (<= (* (pedersen-enc x) (expt 16 n))
           (* 4 (expt 16 n))))
  :rule-classes :linear
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled addition-range-from-two-ranges
  (implies (posp n)
           (< (+ (* 8 (expt 16 (1- (1- n))))
                 (* 4 (expt 16 (1- n))))
              (* 8 (expt 16 (1- n)))))
  :rule-classes :linear
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defisar range-thm-step-when-in-set
  (implies (and (set::in (1- n) indices)
                (posp n)
                (range-thm (1- n) bits)
                (nat-setp indices)
                (belowp indices n))
           (rangep (sum indices bits)
                   n))
  :proof
  ((:assume (:in-set (set::in (1- n) indices)))
   (:assume (:pos (posp n)))
   (:assume (:ind-hyp (range-thm (1- n) bits)))
   (:assume (:nat-set (nat-setp indices)))
   (:assume (:below-n (belowp indices n)))
   (:let (indices-1 (set::delete (1- n) indices)))
   (:derive (:not-in-set (not (set::in (1- n) indices-1)))
    :from ())
   (:derive (:nat-set-1 (nat-setp indices-1))
    :from (:nat-set))
   (:derive (:below-n-1 (belowp indices-1 n))
    :from (:below-n)
    :hints (("Goal" :in-theory (enable belowp-of-delete))))
   (:derive (:below-1 (belowp indices-1 (1- n)))
    :from (:below-n-1 :pos :nat-set-1 :below-n-1 :not-in-set)
    :hints (("Goal" :use (:instance belowp-of-n-minus-1-when-not-in-set
                          (indices (set::delete (1- n) indices))))))
   (:derive (:range-1 (rangep (sum indices-1 bits) (1- n)))
    :from (:ind-hyp :nat-set-1 :below-1)
    :hints (("Goal" :use (:instance range-thm-necc
                          (n (1- n))
                          (indices (set::delete (1- n) indices))))))
   (:derive (:decompose-sum
             (equal (sum indices bits)
                    (+ (sum indices-1 bits)
                       (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                          (expt 16 (1- n))))))
    :from (:in-set :pos)
    :hints (("Goal" :use (:instance sum-to-sum-of-delete (index (1- n))))))
   (:derive (:sum-1-bounds (and (< (- (* 8 (expt 16 (1- (1- n)))))
                                   (sum indices-1 bits))
                                (< (sum indices-1 bits)
                                   (* 8 (expt 16 (1- (1- n)))))))
    :from (:range-1)
    :hints (("Goal" :in-theory (enable rangep))))
   (:derive (:enc-bounds
             (and (<= (- (* 4 (expt 16 (1- n))))
                      (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                         (expt 16 (1- n))))
                  (<= (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                         (expt 16 (1- n)))
                      (* 4 (expt 16 (1- n))))))
    :from (:pos)
    :hints (("Goal"
             :use ((:instance pedersen-enc-times-expt-16-n
                    (x (take 3 (nthcdr (* 3 (1- n)) bits)))
                    (n (1- n)))))))
   (:derive (:sum-bounds
             (and (< (- (+ (* 8 (expt 16 (1- (1- n))))
                           (* 4 (expt 16 (1- n)))))
                     (sum indices bits))
                  (< (sum indices bits)
                     (+ (* 8 (expt 16 (1- (1- n))))
                        (* 4 (expt 16 (1- n)))))))
    :from (:decompose-sum :sum-1-bounds :enc-bounds))
   (:derive (:larger-bounds
             (and (< (- (* 8 (expt 16 (1- n))))
                     (sum indices bits))
                  (< (sum indices bits)
                     (* 8 (expt 16 (1- n))))))
    :from (:sum-bounds :pos)
    :hints (("Goal" :use addition-range-from-two-ranges)))
   (:derive (:conclusion (rangep (sum indices bits) n))
    :from (:larger-bounds)
    :hints (("Goal" :in-theory (enable rangep))))
   (:qed))
  :disable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The step case of the desired theorem is easily proved
; by instantiating the theorems for the two cases above.

(defruled range-thm-step
  (implies (and (posp n)
                (range-thm (1- n) bits))
           (range-thm n bits))
  :expand (range-thm n bits)
  :cases ((set::in (1- n) (range-thm-witness n bits)))
  :use ((:instance range-thm-step-when-in-set
         (indices (range-thm-witness n bits)))
        (:instance range-thm-step-when-not-in-set
         (indices (range-thm-witness n bits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem follows from base and step cases.

(defruled range-thm-holds
  (implies (natp n)
           (range-thm n bits))
  :induct (acl2::dec-induct n)
  :enable (range-thm-base range-thm-step))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Since range-thm was only a way to abstract the formula to prove,
; we can expand it to have a theorem in more explicit form.

(defruled rangep-of-sum
  (implies (and (natp n)
                (nat-setp indices)
                (belowp indices n))
           (rangep (sum indices bits) n))
  :use range-thm-holds
  :enable range-thm-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we turn to formulating and proving Theorem A.3.5.
; This is also proved by induction on n,
; where we need the sets of indices S and S' to be universally quantified.
; So we introduce a predicate with the quantifier,
; similarly to the theorem above about the range.
; Instead of an explicit theta as in [ZPS],
; we just spell out the two equalities.

(define-sk main-thm ((n natp) (bits bit-listp))
  :guard (and (integerp (/ (len bits) 3))
              (>= (len bits) (* 3 n)))
  :returns (yes/no booleanp)
  (forall (indices1 indices2)
          (implies (and (nat-setp indices1)
                        (nat-setp indices2)
                        (belowp indices1 n)
                        (belowp indices2 n)
                        (not (set::empty indices1))
                        (not (set::empty indices2))
                        (set::empty (set::intersect indices1 indices2)))
                   (and (not (equal (sum indices1 bits)
                                    (sum indices2 bits)))
                        (not (equal (sum indices1 bits)
                                    (- (sum indices2 bits)))))))
  :guard-hints (("Goal" :use ((:instance belowp-of-larger
                               (indices (mv-nth 0 (main-thm-witness n bits)))
                               (n n)
                               (m (/ (len bits) 3)))
                              (:instance belowp-of-larger
                               (indices (mv-nth 1 (main-thm-witness n bits)))
                               (n n)
                               (m (/ (len bits) 3)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The base case is easily proved: if n = 0,
; there cannot be two disjoint non-empty subsets S and S' of {0,...,n-1}.

(defruled main-thm-base
  (main-thm 0 bits)
  :enable main-thm)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Similarly to the range theorem proved earlier,
; we first prove the induction step over generic variables;
; we assume n > 1 and (main-thm (1- n)),
; along with the antecedent in the implication in main-thm,
; and prove the consequent of the implication in main-thm.

; There are four cases to consider here,
; depending on whether n-1 is in each of the two sets of indices.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The case in which n-1 is in both sets is easy to prove,
; because it contradicts the disjointness assumption.
; This does not even need the induction hypothesis,
; and can be proved with fewer hypotheses for that matter,
; but we leave all of them (except the induction hypothesis) for uniformity.

(defruled main-thm-step-when-in-both-sets
  (implies (and (set::in (1- n) indices1)
                (set::in (1- n) indices2)
                (nat-setp indices1)
                (nat-setp indices2)
                (belowp indices1 n)
                (belowp indices2 n)
                (not (set::empty indices1))
                (not (set::empty indices2))
                (set::empty (set::intersect indices1 indices2)))
           (and (not (equal (sum indices1 bits)
                            (sum indices2 bits)))
                (not (equal (sum indices1 bits)
                            (- (sum indices2 bits))))))
  :use (:instance set::intersect-in (a (1- n)) (x indices1) (y indices2))
  :disable set::intersect-in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The case in which n-1 is in neither set is fairly easy to prove.
; One just needs to recognize that the sets are also in {0,...,n-2},
; and thus the induction hypothesis readily applies.

; It may be possible to prove this theorem with a single :use hint
; with all the lemma instances from the Isar steps below.
; However, the Isar proof seems more clear and readable.

(defisar main-thm-step-when-in-neither-sets
  (implies (and (not (set::in (1- n) indices1))
                (not (set::in (1- n) indices2))
                (posp n)
                (main-thm (1- n) bits)
                (nat-setp indices1)
                (nat-setp indices2)
                (belowp indices1 n)
                (belowp indices2 n)
                (not (set::empty indices1))
                (not (set::empty indices2))
                (set::empty (set::intersect indices1 indices2)))
           (and (not (equal (sum indices1 bits)
                            (sum indices2 bits)))
                (not (equal (sum indices1 bits)
                            (- (sum indices2 bits))))))
  :proof
  ((:assume (:not-in-set1 (not (set::in (1- n) indices1))))
   (:assume (:not-in-set2 (not (set::in (1- n) indices2))))
   (:assume (:pos (posp n)))
   (:assume (:ind-hyp (main-thm (1- n) bits)))
   (:assume (:nat-set1 (nat-setp indices1)))
   (:assume (:nat-set2 (nat-setp indices2)))
   (:assume (:below1 (belowp indices1 n)))
   (:assume (:below2 (belowp indices2 n)))
   (:assume (:nonempty1 (not (set::empty indices1))))
   (:assume (:nonempty2 (not (set::empty indices2))))
   (:assume (:disjoint (set::empty (set::intersect indices1 indices2))))
   (:derive (:below1-n-1 (belowp indices1 (1- n)))
    :from (:below1 :pos :nat-set1 :not-in-set1)
    :hints (("Goal" :use (:instance belowp-of-n-minus-1-when-not-in-set
                          (indices indices1)))))
   (:derive (:below2-n-1 (belowp indices2 (1- n)))
    :from (:below2 :pos :nat-set2 :not-in-set2)
    :hints (("Goal" :use (:instance belowp-of-n-minus-1-when-not-in-set
                          (indices indices2)))))
   (:derive (:conclusion (and (not (equal (sum indices1 bits)
                                          (sum indices2 bits)))
                              (not (equal (sum indices1 bits)
                                          (- (sum indices2 bits))))))
    :from (:ind-hyp :nat-set1 :nat-set2 :below1-n-1 :below2-n-1
           :nonempty1 :nonempty2 :disjoint)
    :hints (("Goal" :use (:instance main-thm-necc (n (1- n))))))
   (:qed))
  :disable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The case in which n-1 is in the first set but not in the second set
; is proved without actually the need for the induction hypothesis.
; We decompose the summation over the first set into
; the summation over the set minus n-1 plus the addend for n-1.
; From the previously proved theorem about the range of the summations,
; we know that the summation over the set minus n-1 is
; between -8 * 16^(n-2) and +8 * 16^(n-2), exclusive of the limits.
; From the fact that pedersen-enc is not 0,
; we also know that the addend for n-1 is
; outside the interval from -16^(n-1) and +16^(n-1).
; Adding them up, we obtain something that must be
; outside the interval from -8 * 16^(n-2) and +8 * 16^(n-2),
; because in the worst case
; either we are adding 8 * 16^(n-2) to -16^(n-1) = -16 * 16^(n-2),
; which yields -8 * 16^(n-2),
; or we are subtracting 8 * 16^(n-2) from +16^(n-1) = +16 * 16^(n-2),
; which yields +8 * 16^(n-2).
; So the total summation for the first set of indices
; must be outside the interval from
; -8 * 16^(n-2) and +8 * 16^(n-2).
; If we now look at the summation over the second set indices,
; we use the theorem about the range to show that this second summation is
; between -8 * 16^(n-2) and +8 * 16^(n-2),
; and so is its negation of course.
; Thus, the two summations cannot possibly be equal.

; In other words, the addend for index n-1 is so large (relatively speaking)
; that it makes the first summation always different from the second,
; because the second summation and the rest of the fist summation
; are comparatively small.
; This is expressed by the separate auxiliary theorem below,
; where x stands for the added for index n-1
; and y stands for the summation of the rest of the indices.

; We also prove an auxiliary theorem saying that
; pedersen-enc, mutliplied by 16^n, is outside the interval from -16^n to 16^n.

(defruled pedersen-enc-times-expt-16-n-outside-interval
  (or (<= (* (pedersen-enc x) (expt 16 n))
          (- (expt 16 n)))
      (<= (expt 16 n)
          (* (pedersen-enc x) (expt 16 n))))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruled from-outside-larger-to-outside-smaller
  (implies (and (posp n)
                (or (<= x
                        (- (expt 16 (1- n))))
                    (<= (expt 16 (1- n))
                        x))
                (and (<= (- (* 8 (expt 16 (1- (1- n)))))
                         y)
                     (<= y
                         (* 8 (expt 16 (1- (1- n)))))))
           (or (<= (+ x y)
                   (- (* 8 (expt 16 (1- (1- n))))))
               (<= (* 8 (expt 16 (1- (1- n))))
                   (+ x y))))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defisar main-thm-step-when-in-1st-not-2nd
  (implies (and (set::in (1- n) indices1)
                (not (set::in (1- n) indices2))
                (posp n)
                (nat-setp indices1)
                (nat-setp indices2)
                (belowp indices1 n)
                (belowp indices2 n)
                (not (set::empty indices1))
                (not (set::empty indices2))
                (set::empty (set::intersect indices1 indices2)))
           (and (not (equal (sum indices1 bits)
                            (sum indices2 bits)))
                (not (equal (sum indices1 bits)
                            (- (sum indices2 bits))))))
  :proof
  ((:assume (:in-set1 (set::in (1- n) indices1)))
   (:assume (:not-in-set2 (not (set::in (1- n) indices2))))
   (:assume (:pos (posp n)))
   (:assume (:nat-set1 (nat-setp indices1)))
   (:assume (:nat-set2 (nat-setp indices2)))
   (:assume (:below1 (belowp indices1 n)))
   (:assume (:below2 (belowp indices2 n)))
   (:assume (:nonempty1 (not (set::empty indices1))))
   (:assume (:nonempty2 (not (set::empty indices2))))
   (:assume (:disjoint (set::empty (set::intersect indices1 indices2))))
   (:let (indices1-1 (set::delete (1- n) indices1)))
   (:derive (:decompose
             (equal (sum indices1 bits)
                    (+ (sum indices1-1 bits)
                       (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                          (expt 16 (1- n))))))
    :from (:in-set1 :pos)
    :hints (("Goal" :use (:instance sum-to-sum-of-delete
                          (index (1- n))
                          (indices indices1)))))
   (:derive (:nat (natp (1- n)))
    :from (:pos))
   (:derive (:nat-set1-1 (nat-setp indices1))
    :from (:nat-set1))
   (:derive (:below1-1 (belowp indices1-1 (1- n)))
    :from (:pos :nat-set1 :below1)
    :hints (("Goal"
             :use (:instance belowp-of-n-minus-1-when-not-in-set
                   (indices (set::delete (1- n) indices1)))
             :in-theory (enable belowp-of-delete))))
   (:derive (:rangep-indices1-1 (rangep (sum indices1-1 bits) (1- n)))
    :from (:nat :nat-set1-1 :below1-1)
    :hints (("Goal" :use (:instance rangep-of-sum
                          (n (1- n))
                          (indices (set::delete (1- n) indices1))))))
   (:derive (:indices1-1-range
             (and (< (- (* 8 (expt 16 (1- (1- n)))))
                     (sum indices1-1 bits))
                  (< (sum indices1-1 bits)
                     (* 8 (expt 16 (1- (1- n)))))))
    :from (:rangep-indices1-1)
    :hints (("Goal" :in-theory (enable rangep))))
   (:derive (:addend-range
             (or (<= (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                        (expt 16 (1- n)))
                     (- (expt 16 (1- n))))
                 (<= (expt 16 (1- n))
                     (* (pedersen-enc (take 3 (nthcdr (* 3 (1- n)) bits)))
                        (expt 16 (1- n))))))
    :from ()
    :hints (("Goal"
             :use (:instance pedersen-enc-times-expt-16-n-outside-interval
                   (x (take 3 (nthcdr (* 3 (1- n)) bits)))
                   (n (1- n))))))
   (:derive (:first-summation-range
             (or (<= (sum indices1 bits)
                     (- (* 8 (expt 16 (1- (1- n))))))
                 (<= (* 8 (expt 16 (1- (1- n))))
                     (sum indices1 bits))))
    :from (:decompose :indices1-1-range :addend-range :pos)
    :hints (("Goal" :use (:instance from-outside-larger-to-outside-smaller
                          (x (* (pedersen-enc
                                 (take 3 (nthcdr (* 3 (1- n)) bits)))
                                (expt 16 (1- n))))
                          (y (sum (set::delete (1- n) indices1) bits))))))
   (:derive (:below2-n-1 (belowp indices2 (1- n)))
    :from (:below2 :pos :nat-set2 :not-in-set2)
    :hints (("Goal" :use (:instance belowp-of-n-minus-1-when-not-in-set
                          (indices indices2)))))
   (:derive (:second-summation-range
             (and (< (- (* 8 (expt 16 (1- (1- n)))))
                     (sum indices2 bits))
                  (< (sum indices2 bits)
                     (* 8 (expt 16 (1- (1- n)))))))
    :from (:nat :nat-set2 :below2-n-1)
    :hints (("Goal"
             :use (:instance rangep-of-sum (indices indices2) (n (1- n)))
             :in-theory (enable rangep))))
   (:derive (:conclusion
             (and (not (equal (sum indices1 bits)
                              (sum indices2 bits)))
                  (not (equal (sum indices1 bits)
                              (- (sum indices2 bits))))))
    :from (:first-summation-range :second-summation-range))
   (:qed))
  :disable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The case in which n-1 is in the second set but not in the first set
; is treated symmetrically to the previous one.
; Note that we need to enable a rule saying that set intersection commutes.

(defruled main-thm-step-when-in-2nd-not-1st
  (implies (and (not (set::in (1- n) indices1))
                (set::in (1- n) indices2)
                (posp n)
                (nat-setp indices1)
                (nat-setp indices2)
                (belowp indices1 n)
                (belowp indices2 n)
                (not (set::empty indices1))
                (not (set::empty indices2))
                (set::empty (set::intersect indices1 indices2)))
           (and (not (equal (sum indices1 bits)
                            (sum indices2 bits)))
                (not (equal (sum indices1 bits)
                            (- (sum indices2 bits))))))
  :use (:instance main-thm-step-when-in-1st-not-2nd
        (indices1 indices2)
        (indices2 indices1))
  :enable set::intersect-symmetric)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The induction step can now be proved by cases, as mentioned above.

(defruled main-thm-step
  (implies (and (posp n)
                (main-thm (1- n) bits))
           (main-thm n bits))
  :expand (main-thm n bits)
  :cases ((set::in (1- n) (mv-nth 0 (main-thm-witness n bits)))
          (set::in (1- n) (mv-nth 1 (main-thm-witness n bits))))
  :use ((:instance main-thm-step-when-in-both-sets
         (indices1 (mv-nth 0 (main-thm-witness n bits)))
         (indices2 (mv-nth 1 (main-thm-witness n bits))))
        (:instance main-thm-step-when-in-neither-sets
         (indices1 (mv-nth 0 (main-thm-witness n bits)))
         (indices2 (mv-nth 1 (main-thm-witness n bits))))
        (:instance main-thm-step-when-in-1st-not-2nd
         (indices1 (mv-nth 0 (main-thm-witness n bits)))
         (indices2 (mv-nth 1 (main-thm-witness n bits))))
        (:instance main-thm-step-when-in-2nd-not-1st
         (indices1 (mv-nth 0 (main-thm-witness n bits)))
         (indices2 (mv-nth 1 (main-thm-witness n bits))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Base case and step case suffice to prove the predicate main-thm for every n.

(defruled main-thm-holds
  (implies (natp n)
           (main-thm n bits))
  :induct (acl2::dec-induct n)
  :enable (main-thm-base main-thm-step))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Expanding main-thm,
; we obtain a formulation and proof of Theorem A.3.5 in [ZPS].

(defruled pedersen-addition-inputs
  (implies (and (natp n)
                (nat-setp indices1)
                (nat-setp indices2)
                (belowp indices1 n)
                (belowp indices2 n)
                (not (set::empty indices1))
                (not (set::empty indices2))
                (set::empty (set::intersect indices1 indices2)))
           (and (not (equal (sum indices1 bits)
                            (sum indices2 bits)))
                (not (equal (sum indices1 bits)
                            (- (sum indices2 bits))))))
  :use main-thm-holds
  :enable main-thm-necc)
