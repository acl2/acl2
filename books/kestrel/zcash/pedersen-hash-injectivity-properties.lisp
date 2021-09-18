; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "pedersen-hash-bound-properties")

(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two somewhat specific theorems, but more general than Pedersen hash.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel bit-listp-of-take-3
  (implies (and (bit-listp segment)
                (integerp (/ (len segment) 3))
                (consp segment))
           (bit-listp (take 3 segment)))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)
               (include-book "std/lists/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel len-of-nthcdr-multiple-of-3
  (implies (and (integerp (* 1/3 (len x)))
                (consp x))
           (integerp (* 1/3 (len (nthcdr 3 x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pedersen-hash-injectivity-properties
  :parents (pedersen-hash)
  :short "Injectivity of @(tsee pedersen-segment-scalar)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Theorem 5.4.1 in [ZPS:5.4.1.7] proves
     the injectivity of the encoding function @($\\langle\\cdot\\rangle$),
     which is @(tsee pedersen-segment-scalar) in our formalization.
     Theorem 5.4.1 also proves bounds of that function,
     which we prove in @(see pedersen-segment-scalar-bound)
     and in @(see pedersen-segment-scalar-not-zero-proof).")
   (xdoc::p
    "Since @(tsee pedersen-segment-scalar)
     is defined via @('pedersen-segment-scalar-loop'),
     so we need to prove injectivity properties for the latter first.")
   (xdoc::p
    "The proof is explained in the comments in this file."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove the injectivity of pedersen-segment-scalar-loop by induction.
; Since injectivity involves two calls of the function
; on two different (generic) segments,
; we introduce a local function that defines the needed induction scheme.
; The two calls share the same j, because our goal is
; really to prove the injectivity of pedersen-segment-scalar,
; which calls pedersen-segment-scalar-loop with j = 1.
; The induction function below simultaneously decreases the two segments
; in the same way as pedersen-segment-scalar-loop does.

(local
 (defun induction (j segment1 segment2)
   (cond ((endp segment1) j)
         ((endp segment2) j)
         (t (induction (1+ j)
                       (nthcdr 3 segment1)
                       (nthcdr 3 segment2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following local predicate captures
; the injectivity of pedersen-segment-scalar-loop that we want to prove.
; We package it into a predicate because
; the proof involves some explcit steps
; that may or may not be amenable to be carried out
; via generic rules in a way that does not compromise proof clarity.
; By having an explicit predicate,
; we have more control on formulating base cases and step case,
; and on carrying out the step case proof.

(local
 (defund pred (j segment1 segment2)
   (implies (and (posp j)
                 (bit-listp segment1)
                 (bit-listp segment2)
                 (integerp (/ (len segment1) 3))
                 (integerp (/ (len segment2) 3))
                 (equal (pedersen-segment-scalar-loop j segment1)
                        (pedersen-segment-scalar-loop j segment2)))
            (equal segment1 segment2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The two base cases are easy to prove.
; If a segment is empty, its pedersen-segment-scalar-loop value is 0.
; Given the assumption that the other segment has the same value, i.e. 0,
; and given that pedersen-segment-scalar-loop is outside a certain internal
; if the segment were not empty (as asserted by the theorem in the :use hint),
; then the other segment must be empty as well.
; So the two segments are equal (both empty).

(defruledl base-case-1
  (implies (endp segment1)
           (pred j segment1 segment2))
  :enable (pred
           pedersen-segment-scalar-loop)
  :use (:instance pedersen-segment-scalar-loop-outside-interval
        (segment segment2))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruledl base-case-2
  (implies (and (not (endp segment1))
                (endp segment2))
           (pred j segment1 segment2))
  :enable (pred
           pedersen-segment-scalar-loop)
  :use (:instance pedersen-segment-scalar-loop-outside-interval
        (segment segment1))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The step case is more complicated.
; Let us abbreviate pedersen-segment-scalar-loop as PSSL,
; and pedersen-enc as PE.
; (Mixing prefix and infix below.)
; Given the assumption
;
; (PSSL j segment1) = (PSSL j segment2)
;
; we open up PSSL to obtain
;
; (PE (take 3 segment1)) * 16^(j-1) + (PSSL (j+1) (nthcdr 3 segment1))
; =
; (PE (take 3 segment2)) * 16^(j-1) + (PSSL (j+1) (nthcdr 3 segment2))
;
; which we re-arrange as
;
; ((PE (take 3 segment1)) - (PE (take 3 segment2))) * 16^(j-1)
; =
; (PSSL (j+1) (nthcdr 3 segment2)) - (PSSL (j+1) (nthcdr 3 segment1))
;
; Since PE is in {-4, -3, -2, -1, 1, 2, 3, 4},
; the first term is between -8 * 16^(j-1) and +8 * 16^(j-1).
; It is also the case that (PSSL j ...) is a multiple of 16^(j-1),
; because it is a sum of multiples of that.
; Thus, (PSSL (j+1) ...) is a multiple of 16^j,
; and so is the difference in the equality above,
; which has therefore the form
;
; <something between -8 * 16^(j-1) and +8 * 16^(j-1)>
; =
; <something multiple of 16^j>
;
; The only way for these to be equal is that they are both 0 then.
; From
;
; ((PE (take 3 segment1)) - (PE (take 3 segment2))) * 16^(j-1) = 0
;
; we get
;
; (PE (take 3 segment1)) = (PE (take 3 segment2))
;
; which implies
;
; (take 3 segment1) = (take 3 segment2)
;
; by the already proved injectivity of PE.
; From
;
; (PSSL (j+1) (nthcdr 3 segment2)) = (PSSL (j+1) (nthcdr 3 segment1))
;
; we get
;
; (nthcdr 3 segment2) = (nthcdr 3 segment1)
;
; by the induction hypothesis.
; Putting the two together, we have
;
; segment1 = segment2
;
; which concludes the injectivity proof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we show that (PE ...) - (PE ...) is in the interval mentioned above.
; This is the first difference (from left to right) in the equation.

(defruledl first-difference
  (b* ((d (- (* (pedersen-enc x) (expt 16 (1- j)))
             (* (pedersen-enc y) (expt 16 (1- j))))))
    (and (<= (- (* 8 (expt 16 (1- j))))
             d)
         (<= d
             (* 8 (expt 16 (1- j))))))
  :enable pedersen-enc
  :prep-books ((include-book "arithmetic/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The fact that PSSL is a multiple of 16^(j-1) is proved fairly automatically.
; Note the command to tell arithmetic-5 to scatter (vs. gather) exponents.
; We make this theorem non-local as it may be useful somewhere else;
; in fact, we may want to move it somewhere else.

(defruled pedersen-segment-scalar-loop-is-multiple-of-16^j-1
  (implies (posp j)
           (integerp (/ (pedersen-segment-scalar-loop j segment)
                        (expt 16 (1- j)))))
  :enable pedersen-segment-scalar-loop
  :prep-books ((include-book "arithmetic-5/top" :dir :system)
               (acl2::scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The difference of two multiples of something is a multiple of that too.
; This is used for the difference (PSSL ...) - (PSSL ...) mentioned above.

(defruledl difference-of-multiples-is-multiple
  (implies (and (integerp (/ x a))
                (integerp (/ y a)))
           (integerp (/ (- x y) a)))
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We use the two theorems above to show that the second difference
; (from left to right, in the equation) is a multiple of 16^j.

(defruledl second-difference
  (implies (posp j)
           (integerp
            (/ (- (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment2))
                  (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment1)))
               (expt 16 j))))
  :use ((:instance difference-of-multiples-is-multiple
         (x (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment2)))
         (y (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment1)))
         (a (expt 16 j)))
        (:instance pedersen-segment-scalar-loop-is-multiple-of-16^j-1
         (segment (nthcdr 3 segment2))
         (j (1+ j)))
        (:instance pedersen-segment-scalar-loop-is-multiple-of-16^j-1
         (segment (nthcdr 3 segment1))
         (j (1+ j)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here is the key lemma, saying that if two things are equal,
; one is between -a and +a, the other is a multiple of b,
; and b is larger than a,
; then the two things must be both 0.
; It is a more general form of the fact we need here,
; which follows easily by instantitation.

(defrulel key-lemma
  (implies (and (integerp x)
                (integerp y)
                (posp a)
                (posp b)
                (< a b)
                (<= (- a) x)
                (<= x a)
                (integerp (/ y b))
                (equal x y))
           (and (equal x 0)
                (equal y 0)))
  :rule-classes nil
  :use (:instance lemma3 (a b))

  :prep-lemmas

  ((defrule lemma1
     (implies (and (posp a)
                   (integerp x)
                   (integerp (/ x a)))
              (equal x (* a (/ x a))))
     :rule-classes nil
     :prep-books ((include-book "arithmetic/top" :dir :system)))

   (defrule lemma2
     (implies (and (posp a)
                   (integerp x)
                   (integerp k)
                   (equal x (* a k))
                   (not (equal x 0)))
              (or (<= x (- a))
                  (<= a x)))
     :rule-classes nil
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))

   (defrule lemma3
     (implies (and (posp a)
                   (integerp x)
                   (integerp (/ x a))
                   (not (equal x 0)))
              (or (<= x (- a))
                  (<= a x)))
     :rule-classes nil
     :use (lemma1 (:instance lemma2 (k (/ x a)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A few fairly generic theorems, needed in the step case proof.

(defruledl expt-of-2-to-4*x
  (implies (integerp x)
           (equal (expt 2 (* 4 x))
                  (expt 16 x)))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruledl posp-of-expt-16^j-1
  (implies (posp j)
           (posp (expt 16 (1- j))))
  :rule-classes :type-prescription
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruledl bounds-ordering
  (implies (posp j)
           (< (* 8 (expt 16 (1- j)))
              (expt 16 j)))
  :rule-classes :linear
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defruledl equal-of-times-same
  (implies (and (posp a)
                (integerp x)
                (integerp y))
           (equal (equal (* x a)
                         (* y a))
                  (equal x y)))
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(defrulel equal-when-same-take-and-nthcdr
  (implies (and (true-listp x)
                (true-listp y)
                (equal (take 3 x)
                       (take 3 y))
                (equal (nthcdr 3 x)
                       (nthcdr 3 y))
                (integerp (/ (len x) 3))
                (integerp (/ (len y) 3))
                (consp x)
                (consp y))
           (equal x y))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We use an Isar proof for the step case,
; since there are a number of steps involved.
; The proof works and is clear,
; but it should be possible to shorten it,
; provided that we do not compromise its clarity.

(local
 (defisar step-case-lemma
   (implies (and (not (endp segment1))
                 (not (endp segment2))
                 (pred (1+ j) (nthcdr 3 segment1) (nthcdr 3 segment2))
                 (posp j)
                 (bit-listp segment1)
                 (bit-listp segment2)
                 (integerp (/ (len segment1) 3))
                 (integerp (/ (len segment2) 3))
                 (equal (pedersen-segment-scalar-loop j segment1)
                        (pedersen-segment-scalar-loop j segment2)))
            (equal segment1 segment2))
   :proof
   ((:assume (:non-empty (and (not (endp segment1))
                              (not (endp segment2)))))
    (:assume (:ind-hyp (pred (1+ j) (nthcdr 3 segment1) (nthcdr 3 segment2))))
    (:assume (:pos (posp j)))
    (:assume (:bit-list-1 (bit-listp segment1)))
    (:assume (:bit-list-2 (bit-listp segment2)))
    (:assume (:three-1 (integerp (/ (len segment1) 3))))
    (:assume (:three-2 (integerp (/ (len segment2) 3))))
    (:assume (:equal (equal (pedersen-segment-scalar-loop j segment1)
                            (pedersen-segment-scalar-loop j segment2))))
    (:let (enc1 (pedersen-enc (take 3 segment1))))
    (:let (enc2 (pedersen-enc (take 3 segment2))))
    (:let (rec1 (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment1))))
    (:let (rec2 (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment2))))
    (:derive (:decompose1 (equal (pedersen-segment-scalar-loop j segment1)
                                 (+ (* enc1 (expt 16 (1- j)))
                                    rec1)))
     :from (:non-empty :pos)
     :hints (("Goal"
              :in-theory (disable distributivity)
              :use (:instance expt-of-2-to-4*x (x (1- j)))
              :expand (pedersen-segment-scalar-loop j segment1))))
    (:derive (:decompose2 (equal (pedersen-segment-scalar-loop j segment2)
                                 (+ (* enc2 (expt 16 (1- j)))
                                    rec2)))
     :from (:non-empty :pos)
     :hints (("Goal"
              :in-theory (disable distributivity)
              :use (:instance expt-of-2-to-4*x (x (1- j)))
              :expand (pedersen-segment-scalar-loop j segment2))))
    (:derive (:equal-diff (equal (- (* enc1 (expt 16 (1- j)))
                                    (* enc2 (expt 16 (1- j))))
                                 (- rec2 rec1)))
     :from (:equal :decompose1 :decompose2))
    (:derive (:first-diff (and (<= (- (* 8 (expt 16 (1- j))))
                                   (- (* enc1 (expt 16 (1- j)))
                                      (* enc2 (expt 16 (1- j)))))
                               (<= (- (* enc1 (expt 16 (1- j)))
                                      (* enc2 (expt 16 (1- j))))
                                   (* 8 (expt 16 (1- j))))))
     :hints (("Goal" :use (:instance first-difference
                           (x (take 3 segment1))
                           (y (take 3 segment2))))))
    (:derive (:second-diff (integerp (/ (- rec2 rec1) (expt 16 j))))
     :from (:pos)
     :hints (("Goal" :use second-difference)))
    (:derive (:both-0 (and (equal (- (* enc1 (expt 16 (1- j)))
                                     (* enc2 (expt 16 (1- j))))
                                  0)
                           (equal (- rec2 rec1)
                                  0)))
     :from (:equal-diff :first-diff :second-diff :pos)
     :hints (("Goal"
              :in-theory (enable posp-of-expt-16^j-1
                                 bounds-ordering)
              :use (:instance key-lemma
                    (x (- (* (pedersen-enc (take 3 segment1))
                             (expt 16 (1- j)))
                          (* (pedersen-enc (take 3 segment2))
                             (expt 16 (1- j)))))
                    (y (- (pedersen-segment-scalar-loop (1+ j)
                                                        (nthcdr 3 segment2))
                          (pedersen-segment-scalar-loop (1+ j)
                                                        (nthcdr 3 segment1))))
                    (a (* 8 (expt 16 (1- j))))
                    (b (expt 16 j))))))
    (:derive (:first-equal (equal (* enc1 (expt 16 (1- j)))
                                  (* enc2 (expt 16 (1- j)))))
     :from (:both-0))
    (:derive (:equal-enc1-enc2 (equal enc1 enc2))
     :from (:first-equal :pos)
     :hints (("Goal" :in-theory (enable posp-of-expt-16^j-1
                                        equal-of-times-same))))
    (:derive (:equal-take-3 (equal (take 3 segment1)
                                   (take 3 segment2)))
     :from (:equal-enc1-enc2
            :bit-list-1 :bit-list-2 :three-1 :three-2 :non-empty)
     :hints (("Goal" :in-theory (enable pedersen-enc-injectivity))))
    (:derive (:equal-rec1-rec2 (equal rec1 rec2))
     :from (:both-0))
    (:derive (:equal-nthcdr-3 (equal (nthcdr 3 segment1)
                                     (nthcdr 3 segment2)))
     :from (:equal-rec1-rec2 :ind-hyp
            :pos :bit-list-1 :bit-list-2 :three-1 :three-2)
     :hints (("Goal" :in-theory (enable pred))))
    (:derive (:goal (equal segment1 segment2))
     :from (:equal-take-3 :equal-nthcdr-3
            :bit-list-1 :bit-list-2 :three-1 :three-2 :non-empty)
     :hints (("Goal" :use (:instance equal-when-same-take-and-nthcdr
                           (x segment1) (y segment2)))))
    (:qed))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem above was proving the opened pred,
; which is why it was called a 'lemma'.
; Here we put it into a step case theorem that just involves pred.

(defruledl step-case
  (implies (and (not (endp segment1))
                (not (endp segment2))
                (pred (1+ j) (nthcdr 3 segment1) (nthcdr 3 segment2)))
           (pred j segment1 segment2))
  :enable pred
  :use step-case-lemma)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Base cases and step case prove that pred always holds.

(defruledl pred-holds
  (pred j segment1 segment2)
  :induct (induction j segment1 segment2)
  :enable (base-case-1 base-case-2 step-case))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The injectivity of pedersen-segment-scalar-loop is now easily proved.

(defrule pedersen-segment-scalar-loop-injectivity
  (implies (and (posp j)
                (bit-listp segment1)
                (bit-listp segment2)
                (integerp (/ (len segment1) 3))
                (integerp (/ (len segment2) 3))
                (equal (pedersen-segment-scalar-loop j segment1)
                       (pedersen-segment-scalar-loop j segment2)))
           (equal segment1 segment2))
  :rule-classes nil
  :use pred-holds
  :enable pred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The injectivity of pedersen-segment-scalar also easily follows.

(defrule pedersen-segment-scalar-injectivity
  (implies (and (bit-listp segment1)
                (bit-listp segment2)
                (integerp (/ (len segment1) 3))
                (integerp (/ (len segment2) 3))
                (equal (pedersen-segment-scalar segment1)
                       (pedersen-segment-scalar segment2)))
           (equal segment1 segment2))
  :rule-classes nil
  :enable pedersen-segment-scalar
  :use (:instance pedersen-segment-scalar-loop-injectivity (j 1)))
