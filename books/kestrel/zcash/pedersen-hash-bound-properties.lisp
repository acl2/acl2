; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "pedersen-hash")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A somewhat specific theorem, but more general than Pedersen hash.

(defrulel len-of-nthcdr-multiple-of-3
  (implies (and (integerp (* 1/3 (len x)))
                (consp x))
           (integerp (* 1/3 (len (nthcdr 3 x)))))
  :prep-books ((include-book "std/lists/nthcdr" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pedersen-hash-bound-properties
  :parents (pedersen-hash)
  :short "Some properties about bounds of @(tsee pedersen-segment-scalar)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the absolute value of this function
     has a certain inclusive upper bound
     (expressed by a function introduced here)
     and an exclusive lower bound of 0.
     Since @(tsee pedersen-segment-scalar)
     is defined via @('pedersen-segment-scalar-loop'),
     we also prove bounds about the latter."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-segment-scalar-bound ((segment bit-listp))
  :guard (integerp (/ (len segment) 3))
  :returns (bound natp)
  :short "Bound on the value of @(tsee pedersen-segment-scalar)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Theorem 5.4.1 in [ZPS:5.4.1.7] defines @$(\\Delta$) as
     a bound on the value of the encoding function @($\\langle\\cdot\\rangle$):
     the value of the function is between @($-\\Delta$) and @($\\Delta$).
     In [ZPS], @($\\Delta$) is a constant because @($\\langle\\cdot\\rangle$)
     is defined over segments of maximum size @($3c$).
     However, our @(tsee pedersen-segment-scalar) is more generally defined
     over segments of any length that is a multiple of 3.
     Accordingly, we define a function that expresses @($\\Delta$)
     in terms of (the length of) the segment.
     Since @(tsee pedersen-segment-scalar) is defined in terms of
     an auxiliary recursive function that is defined even more generally
     over not only a segment of length multiple of 3
     but also the index @($j$) of the chunk of 3 bits,
     we also introduce a function that expresses
     the bound on the recursive function.")
   (xdoc::p
    "Based on the summation that defines @($\\Delta$) in [ZPS],
     we define the bound for the recursive function
     by recursively adding @($4\\cdot2^{4\\cdot(j-1)}$)
     while @($j$) is incremented until there is no 3-bit chunk left.
     The bound for @(tsee pedersen-segment-scalar) is obtained from that
     by setting @($j$) to 1.")
   (xdoc::p
    "To prove that these are actual bounds,
     we start with a proof by induction for the recursive function and bound.
     We need a lemma about the length of @('(nthcdr 3 x)') being a multiple of 3
     when the length of @('x') is:
     this serves to relieve the hypothesis of the induction hypothesis.
     We also need a lemma saying that @('(take 3 segment)') is a list of bits
     under the hypothesis of the theorem:
     this is needed for the base case,
     to relieve the hypothesis of the bound rules of @(tsee pedersen-enc).
     (These two lemmas are at the beginning of this file.)
     We also need a few arithmetic lemmas
     to nudge the proof in the right direction.
     (These arithmetic lemmas are below.)
     With linear bound rules for the recursive function in hand,
     the bound proofs for @(tsee pedersen-segment-scalar) are automatic."))
  (pedersen-segment-scalar-loop-bound 1 segment)

  :prepwork
  ((define pedersen-segment-scalar-loop-bound ((j posp) (segment bit-listp))
     :guard (integerp (/ (len segment) 3))
     :returns (bound natp :hyp (posp j))
     :parents nil
     (if (consp segment)
         (+ (* 4 (expt 2 (* 4 (1- j))))
            (pedersen-segment-scalar-loop-bound (1+ j) (nthcdr 3 segment)))
       0)
     :measure (len segment)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system))
                (local (include-book "arithmetic-3/top" :dir :system)))))

  ///

  (defruledl arith-lemma1
    (implies (<= x y)
             (<= (* x (expt 2 a))
                 (* y (expt 2 a))))
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defruledl arith-lemma2
    (implies (and (<= a b)
                  (<= x y))
             (<= (+ a x)
                 (+ y b))))

  (defruledl arith-lemma3
    (equal (- (* 4 x))
           (* -4 x)))

  (defrule pedersen-segment-scalar-loop-upper-bound
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (pedersen-segment-scalar-loop j segment)
                 (pedersen-segment-scalar-loop-bound j segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar-loop
             pedersen-segment-scalar-loop-bound
             arith-lemma1 arith-lemma2))

  (defrule pedersen-segment-scalar-loop-lower-bound
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (- (pedersen-segment-scalar-loop-bound j segment))
                 (pedersen-segment-scalar-loop j segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar-loop
             pedersen-segment-scalar-loop-bound
             arith-lemma1 arith-lemma2 arith-lemma3))

  (defrule pedersen-segment-scalar-upper-bound
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (pedersen-segment-scalar segment)
                 (pedersen-segment-scalar-bound segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar pedersen-segment-scalar-bound))

  (defrule pedersen-segment-scalar-lower-bound
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (- (pedersen-segment-scalar-bound segment))
                 (pedersen-segment-scalar segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar pedersen-segment-scalar-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pedersen-segment-scalar-not-zero-proof
  :short "Proof that @(tsee pedersen-segment-scalar) is not 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by first proving that
     the loop function is outside the interval
     between @($-2^{4\\cdot(j-1)}$) to @($2^{4\\cdot(j-1)}$),
     both exclusive.
     Setting @($j=1$), we have that @(tsee pedersen-segment-scalar)
     is outside the interval from -1 to 1 exclusive, i.e. it is not 0.
     To prove the lemma about the loop function,
     to avoid dealing with a disjunction of inequalities,
     we introduce a predicate for being outside the interval
     and we prove some theorems about it.
     Some of these theorems are currently somewhat specific;
     perhaps there is a way to improve the form of the proof.")
   (xdoc::p
    "The fact, mentioned above, that
     the loop function is outside a certain interval
     is also useful to prove other properties.
     Thus, we export a theorem asserting that."))

  (local
   (define outsidep (x b)
     (or (<= x (- b))
         (<= b x))
     :verify-guards nil))

  (defruledl outsidep-lemma1
    (implies (posp c)
             (equal (outsidep (* c x) c)
                    (outsidep x 1)))
    :enable outsidep
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defruledl outsidep-lemma2
    (implies (and (posp c)
                  (outsidep x (* c b))
                  (integerp y)
                  (< (- c) y)
                  (< y c))
             (outsidep (+ x (* y b)) b))
    :enable outsidep
    :prep-books ((include-book "arithmetic-5/top" :dir :system)
                 (set-default-hints '((acl2::nonlinearp-default-hint
                                       stable-under-simplificationp
                                       hist
                                       pspv)))))

  (defruledl outsidep-lemma3
    (implies (and (posp j)
                  (outsidep x (expt 2 (* 4 j)))
                  (integerp y)
                  (< -16 y)
                  (< y 16))
             (outsidep (+ x (* y (expt 2 (+ -4 (* 4 j)))))
                       (expt 2 (+ -4 (* 4 j)))))
    :use (:instance outsidep-lemma2 (c 16) (b (expt 2 (+ -4 (* 4 j)))))
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defruledl posp-of-bound
    (implies (posp j)
             (posp (expt 2 (+ -4 (* 4 j)))))
    :rule-classes :type-prescription
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defruledl outsidep-of-pedersen-segment-scalar-loop
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (outsidep (pedersen-segment-scalar-loop j segment)
                       (expt 2 (+ -4 (* 4 j)))))
    :enable (pedersen-segment-scalar-loop
             outsidep-lemma1
             outsidep-lemma3
             posp-of-bound))

  (defrule pedersen-segment-scalar-loop-outside-interval
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (or (<= (pedersen-segment-scalar-loop j segment)
                     (- (expt 2 (+ -4 (* 4 j)))))
                 (<= (expt 2 (+ -4 (* 4 j)))
                     (pedersen-segment-scalar-loop j segment))))
    :use outsidep-of-pedersen-segment-scalar-loop
    :enable outsidep)

  (defrule pedersen-segment-scalar-not-zero
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (not (equal (pedersen-segment-scalar segment) 0)))
    :rule-classes :type-prescription
    :enable pedersen-segment-scalar
    :use (:instance outsidep-of-pedersen-segment-scalar-loop (j 1))))
