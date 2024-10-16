; Copyright (C) Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "IFP")
(include-book "fp-common")
(include-book "centaur/bitops/limited-shifts" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :Dir :system))
(local (in-theory (disable unsigned-byte-p
                           logmask
                           (tau-system))))

(local (std::add-default-post-define-hook :fix))



(defxdoc fp-add-core-specs
  :parents (fp-common)
  :short "Core specs for FP addition on @(see fp-arith-triple)s"
  :long "<p>We have a couple of levels of specification here:</p>

<p>@(see fp-add-core-naive) does a very simple and inefficient form of FP add.
It's no good for symbolic simulation and is even likely to be bad for concrete
execution, because it aligns by only leftshifting, so the length size of the
aligned mantissa is exponential in the size of the exponents.  But also because
of this, it can be proved correct relatively easily and it's easy to state the
correctness condition (the value of the result equals the sum of the values of
the inputs -- no truncation, no sticky).  This helps us prove other, more
practical specs correct by comparing to this.</p>

<p>@(see fp-add-core2) and @(see fp-add-core) are more
symbolic-simulation-friendly specs.  The former has a correctness proof that
shows that under certain conditions, @(see normalize-arith-triple) of its
result produces the same normalized mantissa/round/sticky as
normalize-arith-triple of fp-add-core-naive.</p>")


(define fp-add-core-naive ((prod fp-arith-triple-p)
                           (acc  fp-arith-triple-p)
                           (rc fp-rc-p)
                           &key
                           ((verbosep) 'verbosep))
  :parents (fp-add-core-specs)
  :short "Unoptimized function that aligns and adds/subtracts
  @('prod') and @('acc'). This function is intended to be simple
  enough to trust its correctness."
  :long "<p>However, we also prove that the value of its @(see fp-arith-triple)
result equals the sum of the values of its inputs, which is a pretty complete
correctness statement.</p>

<p>It isn't recommended to use this for symbolic simulation, and even for
concrete simulation it may be slow and produce lots of garbage, because it
aligns only by left-shifting.  See @(see fp-add-core2) for a spec that is more
friendly for symbolic simulation and concrete execution and is proved correct
with respect to this function.</p>
"
  :returns (sum fp-arith-triple-p)

  (b* (((fp-arith-triple prod))
       ((fp-arith-triple acc))
       ((when (eql 0 prod.man))
        (if (eql 0 acc.man)
            (make-fp-arith-triple
             :sign (if (eql prod.sign acc.sign)
                       prod.sign
                     (bool->bit (eql (rc->rounding-mode rc) :rmi)))
             :man 0 :exp 0)
          (fp-arith-triple-fix acc)))
       ((when (eql 0 acc.man)) (fp-arith-triple-fix prod))
       
       ;; (- (cw-verbose "~% Size: ~x0 ~%" size))

       ;; Pick big and small arith-triples, based solely on the
       ;; exponents.
       ((mv (fp-arith-triple big-init) (fp-arith-triple small))
        (if (< prod.exp acc.exp)
            (mv acc prod)
          (mv prod acc)))

       (- (cw-verbose "~% Big-Init:   ~x0 ~%" big-init))
       (- (cw-verbose "~% Small-Init: ~x0 ~%" small))

       ;; Adjust big so that big and small have the same exponents.
       (exp-diff (- big-init.exp small.exp))
       (- (cw-verbose "~% Exp-diff: ~x0 ~%" exp-diff))
       ((fp-arith-triple big)
        (fp-arith-leftshift big-init exp-diff))
       (- (cw-verbose "~% Shifted big: ~x0~%" big))

       (eff-sub (b-xor big.sign small.sign))

       ((mv sign sum-mantissa)
        (if (eql eff-sub 0)
            (mv big.sign (+ big.man small.man))
          (cond ((>= big.man small.man)
                 ;; Includes the case when prod and acc are exact
                 ;; opposites.
                 (mv big.sign (- big.man small.man)))

                (t ;; (< big.man small.man)
                 ;; Small is the bigger value.
                 (mv small.sign (- small.man big.man))))))
       (- (cw-verbose "~% Sum-mantissa: ~s0  ~%" (str::hexify sum-mantissa)))

       (sum (if (eql sum-mantissa 0)
                ;; sum-mantissa can only be zero either when prod and acc are
                ;; exact opposites of each other, or when they are both 0.
                ;; The result should be -0 when rounding down and +0 otherwise.
                (make-fp-arith-triple :sign (bool->bit (eql (rc->rounding-mode rc) :rmi))
                                      :exp 0
                                      :man 0)
              (make-fp-arith-triple :sign sign
                                    :exp big.exp
                                    :man sum-mantissa))))
    sum)

  ///

  (defret posp-<fn>.man
    (b* (((fp-arith-triple sum)))
      (implies (not (eql sum.exp 0))
               (posp sum.man))))


  (local (defthm multiply-through-equal-0
           (implies (and (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d)
                         (not (Equal 0 d)))
                    (and (equal (equal (+ a (* b c (/ d))) 0)
                                (equal (+ (* d a) (* b c)) 0))
                         (equal (equal (+ a (* b (/ d) c)) 0)
                                (equal (+ (* d a) (* b c)) 0))))
           :hints (("goal" :use ((:instance acl2::left-cancellation-for-*
                                  (z d)
                                  (x (+ a (* b c (/ d))))
                                  (y 0)))
                    :in-theory (disable acl2::left-cancellation-for-*)))))
  
  (defret <fn>-correct
    (equal (fp-arith-triple->rational sum)
           (+ (fp-arith-triple->rational prod)
              (fp-arith-triple->rational acc)))
    :hints(("Goal" :in-theory (enable fp-arith-triple->rational
                                      fp-arith-leftshift))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x)
                  :cases ((equal (fp-arith-triple->sign prod) 1))))
           (and stable-under-simplificationp
                '(:nonlinearp t))))


  
  ;; (local (defthm integer-length-bound-of-add-nonneg
  ;;          (implies (and (natp x) (natp y))
  ;;                   (and (<= (integer-length x) (integer-length (+ x y)))





  (local (defthmd integer-length-gte
           (implies (and (<= (expt 2 (+ -1 n)) (ifix x))
                         (natp n))
                    (<= n (integer-length x)))
           :hints (("goal" :use ((:instance bitops::integer-length-monotonic
                                  (i (expt 2 (+ -1 n))) (j (ifix x))))
                    :in-theory (disable bitops::integer-length-monotonic)))))

  (local (defthmd integer-length-lte
           (implies (and (<= x (+ -1 (expt 2 (+ -1 n))))
                         (posp n)
                         (natp x))
                    (<= (integer-length x) n))
           :hints (("goal" :use ((:instance bitops::integer-length-monotonic
                                  (i (ifix x)) (j (+ -1 (expt 2  (+ -1 n))))))
                    :in-theory (disable bitops::integer-length-monotonic)))))

  (local (defthmd expt-2-monotonic
           (implies (and (< a b)
                         (integerp a)
                         (integerp b))
                    (< (expt 2 a)
                       (expt 2 b)))
           :rule-classes ((:rewrite) (:linear))))
  
  
  (local
   (defthm integer-length-of-subtract-by-integer-length-diff-minus1
     (implies (and (<= (+ 2 (integer-length a)) (integer-length b))
                   (natp a) (natp b))
              (and (<= (+ -1 (integer-length b)) (integer-length (+ -1 (- a) b)))
                   (<= (+ -1 (integer-length b)) (integer-length (+ -1 b (- a))))))
     :hints (("goal" :use ((:instance bitops::|2^{(integer-length n) - 1} <= n|
                            (n b))
                           (:instance bitops::integer-length-expt-upper-bound-n (n a))
                           (:instance integer-length-gte
                            (x (+ -1 (- a) b)) (n (+ -1 (integer-length b))))
                           (:instance expt-2-monotonic
                            (a (integer-length a)) (b (+ -2 (integer-length b)))))
              :in-theory (disable bitops::|2^{(integer-length n) - 1} <= n|
                                  bitops::integer-length-expt-upper-bound-n
                                  integer-length-gte
                                  acl2::exponents-add)
              :expand ((expt 2 (+ -1 (integer-length b))))))
     :rule-classes :linear))

  (local
   (defthm integer-length-of-subtract-by-integer-length-diff-minus
     (implies (and (<= (+ 2 (integer-length a)) (integer-length b))
                   (natp a) (natp b))
              (and (<= (+ -1 (integer-length b)) (integer-length (+ (- a) b)))
                   (<= (+ -1 (integer-length b)) (integer-length (+ b (- a))))))
     :hints (("goal" :use ((:instance bitops::|2^{(integer-length n) - 1} <= n|
                            (n b))
                           (:instance bitops::integer-length-expt-upper-bound-n (n a))
                           (:instance integer-length-gte
                            (x (+ (- a) b)) (n (+ -1 (integer-length b))))
                           (:instance expt-2-monotonic
                            (a (integer-length a)) (b (+ -2 (integer-length b)))))
              :in-theory (disable bitops::|2^{(integer-length n) - 1} <= n|
                                  bitops::integer-length-expt-upper-bound-n
                                  integer-length-gte
                                  acl2::exponents-add)
              :expand ((expt 2 (+ -1 (integer-length b))))))
     :rule-classes :linear))


  (local
   (defthm integer-length-of-add
     (implies (and (natp a) (natp b))
              (and (<= (integer-length a) (integer-length (+ a b)))
                   (<= (integer-length b) (integer-length (+ a b)))))
     :hints (("goal" :use ((:instance bitops::|2^{(integer-length n) - 1} <= n|
                            (n b))
                           (:instance bitops::|2^{(integer-length n) - 1} <= n|
                            (n a))
                           (:instance integer-length-gte
                            (x (+ a b)) (n (integer-length b)))
                           (:instance integer-length-gte
                            (x (+ a b)) (n (integer-length a))))
              :in-theory (disable bitops::|2^{(integer-length n) - 1} <= n|
                                  bitops::integer-length-expt-upper-bound-n
                                  integer-length-gte
                                  acl2::exponents-add)
              :expand ((expt 2 (+ -1 (integer-length b))))))
     :rule-classes :linear))
  

  (local (defthm left-shift-equal-0
           (implies (natp shift)
                    (equal (equal (ash x shift) 0)
                           (equal (ifix x) 0)))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))
  
  (defretd integer-length-lower-bound-of-<fn>-add
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum)))
      (and (implies (and (equal prod.sign acc.sign)
                         (not (equal acc.man 0))
                         (not (Equal prod.man 0)))
                    (<= (max (max (integer-length prod.man)
                                  (+ (integer-length acc.man)
                                     acc.exp (- prod.exp)))
                             (max (integer-length acc.man)
                                  (+ (integer-length prod.man)
                                     prod.exp (- acc.exp))))
                        (integer-length sum.man)))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))

  (local (defthm <-ash-by-integer-lengths
           (implies (and (< (integer-length x) (integer-length (ash y m)))
                         (natp x) (natp y))
                    (and (<= x (ash y m))
                         (< x (ash y m))
                         (not (equal x (ash y m)))
                         (not (equal 0 (+ (- x) (ash y m))))))
           :hints (("goal" :use ((:instance bitops::integer-length-monotonic
                                  (j x)
                                  (i (ash y m))))
                    :in-theory (disable bitops::integer-length-monotonic)))))


  (local (defthm sum-equal-0
           (equal (equal (+ (- x) y) 0)
                  (equal (fix x) (fix y)))))

  (local (include-book "centaur/bitops/integer-length" :dir :system))
  (local (defthm integer-length-compare-lemma
           (implies (and (natp x) (natp y)
                         (<= x y))
                    (<= (integer-length x) (+ 1 (integer-length y))))))
                    
  
  (defretd integer-length-lower-bound-of-<fn>-sub-far-1
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum)))
      (implies (and (not (equal 0 prod.man))
                    (not (equal 0 acc.man)))
               (and (implies (and (<= acc.exp prod.exp)
                                  (< (+ 1 (integer-length acc.man))
                                     (+ (integer-length prod.man) prod.exp (- acc.exp))))
                             (<= (+ -1 (integer-length prod.man) prod.exp (- acc.exp))
                                 (integer-length sum.man))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))
           (and stable-under-simplificationp
                '(:nonlinearp t))))

  (defretd integer-length-lower-bound-of-<fn>-sub-far-2
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum)))
      (implies (and (not (equal 0 prod.man))
                    (not (equal 0 acc.man)))
               (and (implies (and (<= acc.exp prod.exp)
                                  (< (+ 1 (integer-length prod.man) prod.exp (- acc.exp))
                                     (integer-length acc.man)))
                             (<= (+ -1 (integer-length acc.man))
                                 (integer-length sum.man))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))


  (defretd integer-length-lower-bound-of-<fn>-sub-far-3
    (b* (((fp-arith-triple acc))
         ((fp-arith-triple prod))
         ((fp-arith-triple sum)))
      (implies (and (not (equal 0 acc.man))
                    (not (equal 0 prod.man)))
               (and (implies (and (<= prod.exp acc.exp)
                                  (< (+ 1 (integer-length prod.man))
                                     (+ (integer-length acc.man) acc.exp (- prod.exp))))
                             (<= (+ -1 (integer-length acc.man) acc.exp (- prod.exp))
                                 (integer-length sum.man))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))


  (local (defthm equal-when-diff-0
           (equal (equal (+ (- x) y) 0)
                  (equal (fix x) (fix  y)))))

  (local (defthm mantissa-compare-by-integer-length
           (implies (< (integer-length (fp-arith-triple->man x))
                       (integer-length (fp-arith-triple->man y)))
                    (< (fp-arith-triple->man x) (fp-arith-triple->man y)))))

  (local (defthm mantissa-<=-by-integer-length
           (implies (< (integer-length (fp-arith-triple->man x))
                       (integer-length (fp-arith-triple->man y)))
                    (<= (fp-arith-triple->man x) (fp-arith-triple->man y)))
           :hints (("goal" :use mantissa-compare-by-integer-length
                    :in-theory (disable mantissa-compare-by-integer-length
                                        bitops::integer-length-monotonic)))))

  (local (defthm <-+-1-forward
           (implies (< (+ 1 x) y)
                    (< x y))
           :rule-classes :forward-chaining))
  
  (defretd integer-length-lower-bound-of-<fn>-sub-far-4
    (b* (((fp-arith-triple acc))
         ((fp-arith-triple prod))
         ((fp-arith-triple sum)))
      (implies (and (not (equal 0 acc.man))
                    (not (equal 0 prod.man)))
               (and (implies (and (<= prod.exp acc.exp)
                                  (< (+ 1 (integer-length acc.man) acc.exp (- prod.exp))
                                     (integer-length prod.man)))
                             (<= (+ -1 (integer-length prod.man))
                                 (integer-length sum.man))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))

  (defthm normalize-verbosep-of-<fn>
    (implies (syntaxp (not (Equal verbosep ''nil)))
             (Equal (fp-add-core-naive a b rc)
                    (fp-add-core-naive a b rc :verbosep nil))))


  (local (defthm b-xor-id
           (equal (b-xor b (b-xor a b))
                  (bfix a))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (defretd <fn>-mantissa-normalize-sign-exponent
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum))
         ((fp-arith-triple norm-sum)
          (fp-add-core-naive (change-fp-arith-triple prod :exp 0 :sign 0)
                             (change-fp-arith-triple acc :exp (- acc.exp prod.exp) :sign (b-xor prod.sign acc.sign))
                             rc)))
      (implies (syntaxp (not (case-match prod
                               (('fp-arith-triple ''0 ''0 &) t)
                               (('quote ('(sign . 0) '(exp . 0) &)) t))))
               (and (equal sum.man norm-sum.man)
                    (equal sum.sign
                           (if (equal norm-sum.man 0)
                               (if (equal acc.sign prod.sign)
                                   acc.sign
                                 (bool->bit (equal (rc->rounding-mode rc) :rmi)))
                             (b-xor prod.sign norm-sum.sign))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      fp-add-core-naive)))
    :fn fp-add-core-naive)

  (defretd <fn>-mantissa-sign-normalize-exponent
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum))
         ((fp-arith-triple norm-sum)
          (fp-add-core-naive (change-fp-arith-triple prod :exp 0)
                             (change-fp-arith-triple acc :exp (- acc.exp prod.exp))
                             rc)))
      (implies (syntaxp (not (case-match prod
                               (('fp-arith-triple & ''0 &) t)
                               (('quote (& '(exp . 0) &)) t))))
               (and (equal sum.man norm-sum.man)
                    (equal sum.sign norm-sum.sign))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      fp-add-core-naive)))
    :fn fp-add-core-naive)

  (defretd <fn>-exponent-norm
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc))
         ((fp-arith-triple sum))
         ((fp-arith-triple norm-sum)
          (fp-add-core-naive (change-fp-arith-triple prod :exp 0 :sign 0)
                             (change-fp-arith-triple acc :exp (- acc.exp prod.exp)
                                                     :sign (b-xor prod.sign acc.sign))
                             rc)))
      (implies (syntaxp (not (case-match prod
                               (('fp-arith-triple & ''0 &) t)
                               (('quote (& '(exp . 0) &)) t))))
               (equal sum.exp
                      (if (eql 0 norm-sum.man)
                          0
                        (+ (if (and (eql 0 prod.man)
                                    (eql 0 acc.man))
                               0
                             prod.exp)
                           norm-sum.exp)))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      fp-add-core-naive)))
    :fn fp-add-core-naive)

  (defret <fn>-when-both-zero
    (b* (((fp-arith-triple prod))
         ((fp-arith-triple acc)))
      (implies (and (equal 0 prod.man)
                    (Equal 0 acc.man))
               (equal sum
                      (make-fp-arith-triple :man 0 :exp 0
                                            :sign (if (eql prod.sign acc.sign)
                                                      prod.sign
                                                    (bool->bit (eql (rc->rounding-mode rc) :rmi)))))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))
  )




;; For some operations (e.g. x87 additions with memory operands) we need to
;; allow for the case where we are adding a denorm to a normal with lesser
;; exponent.

;; 1. Left shift the bigger-exponent input's mantissa by a constant amount so that we'll end up with enough bits.
;; 2. Right- or left-shift the smaller-exponent input's mantissa to align.  Any bits rightshifted off are collected into a sticky bit.
;; 3. Add/subtract the shifted mantissas.

;; The bad case we need to avoid is a cancellation where we end up with both
;; not enough bits in the mantissa sum AND some sticky bits we have shifted
;; off. Working out the cases:

;; Suppose WLOG that a.exp >= b.exp.  We assume 1 <= length(a.man) <= a-width and similarly for b.
;; After step 1, leftshift + 1 <= length(ashift.man) <= leftshift + awidth.  For all i < leftshift, ashift.man[i] = 0.
;; The worst case, here, is where bshift aligns almost exactly with ashift and causes a mass cancellation, _but_ b also had some sticky bits shifted off.
;; We need to ensure that if b was rightshifted (and therefore might have sticky bits), the mantissa sum is at least reswidth+1 bits (for round).

;; The minimum lengths of the mantissa sum:
;;  1. 0 if the shifted lengths are equal
;;  2. 1 if the shifted lengths differ by 1
;;  3. max shifted length minus 1 if they differ by more than 1.

;; In cases 1 and 2 we definitely don't have enough bits in the sum, so we have to be sure there's no sticky.
;; We need to ensure that a) whenver b is rightshifted, the shifted lengths will differ by at least 2, and b)
;; the max shifted length minus 1 is enough mantissa bits.

;; For a), it suffices to ensure that leftshift >= bwidth.  In the worst case
;; length(ashift.man) is leftshift+1 and length(bshift.man) is bwidth-1 (i.e., when length(b.man) is bwidth and the rightshift was by only 1).
;; If leftshift >= bwidth, then these differ by at least 2.

;; For b), if we satisfy the requirements of a) then the ashift.man will be longer than bshift.man and so the max width is that of ashift.man, which is at least leftshift+1.
;; So we need leftshift >= reswidth+1.

;; This leads us to leftshift = max(reswidth+1, bwidth).

;; Revised algorithm:

;; Shift a by leftshift - max(b.exp-a.exp, 0)
;; Shift b by leftshift - max(a.exp-b.exp, 0)
;; Add/subtract the shifted mantissas.
;; Exponent of the result is max(a.exp,b.exp) - leftshift.

;; Note we may leftshift by much less when we have the usual arrangement where
;; denormal inputs always have the minimum exponent.  We could still use the
;; following function for that -- we'd just want a version of
;; <fn>-integer-length-when-sticky with different assumptions.


(thm
 (implies (and (integerp ashift.man)
               (integerp bshift.man)
               (not (Equal ashift.man bshift.man)))
          (equal (b* ((sum (fgl::binary-minus ashift.man bshift.man))
                      (sum-<-0 (< sum 0)))
                   (fgl::binary-minus
                    (if sum-<-0 (- sum) sum) (bool->bit sticky)))
                 (if (< bshift.man ashift.man)
                     (fgl::binary-minus ashift.man (+ bshift.man (bool->bit sticky)))
                   (fgl::binary-minus bshift.man (+ ashift.man (bool->bit sticky))))))
 :hints(("Goal" :in-theory (enable fgl::binary-minus))))


(define fp-add-core2 ((a fp-arith-triple-p)
                      (b fp-arith-triple-p)
                      (rc fp-rc-p)
                      (a-width posp)
                      (b-width posp)
                      (leftshift natp))
  ;; Correct usage in the general case (without the restriction that denormal inputs have minimum exponent) requires:
  ;; (unsigned-byte-p a-width a.man)
  ;; (unsigned-byte-p b-width b.man)
  ;; a.man != 0
  ;; b.man != 0
  ;; leftshift >= max(a-width, b-width, result_mantissa_width+1)
  ;; If a sticky bit is produced, result width is guaranteed to be at least leftshift-1.
  :returns (mv (sum fp-arith-triple-p)
               (stickyp booleanp))
  :prepwork ((local (in-theory (enable fgl::binary-minus fgl::+carry lognot))))
  :parents (fp-add-core-specs)
  :long "<p>This is a symbolic simulation-friendly and fairly
concrete-execution-efficient spec function for adds on @(see fp-arith-triple)s.</p>

<p>It has a few extra parameters which affect its efficiency and correctness:</p>

<ul>

<li>@('a-width') and @('b-width') must be upper bounds for the @(see
integer-length) for the mantissas (@(see fp-arith-triple->man)) of the @('a')
and @('b') inputs, respectively.  For symbolic simulation efficiency they
should be concrete/constant values -- typically the mantissa size of the FP
format in use.</li>

<li>@('leftshift') says how much the bigger-exponent input is left-shifted. It
is important for correctness that this be large enough (too large is OK, but
can affect symbolic simulation performance).</li>

</ul>

<p>The best setting for @('leftshift') depends on what we know about the input
triples; we have correctness theorems for a couple of main circumstances:</p>

<ul>

<li>Conventional FP adds where the inputs and output are all the same size and
the inputs are normalized unless they have the minimum possible exponent may
use a leftshift value of 2, by the theorem
@('fp-add-core2-correct-by-normalization-when-denorm-restriction') (shown
below).</li>

<li>For the more general case where denormal inputs may not have the minimum
exponent or where inputs may have different widths, it suffices to use as
leftshift the maximum of the two input mantissa widths as well as one plus the
output mantissa width (fraction width plus two), by the theorem
@('fp-add-core2-correct-by-normalization-when-big-leftshift').</li>

</ul>

<p>The two theorems mentioned above:</p>

@(def fp-add-core2-correct-by-normalization-when-denorm-restriction)
@(def fp-add-core2-correct-by-normalization-when-big-leftshift)

"
  (b* (((fp-arith-triple a))
       ((fp-arith-triple b))
       (leftshift (lnfix leftshift))
       ((when (eql a.man 0))
        (mv (if (eql 0 b.man)
                (make-fp-arith-triple
                 :sign (if (eql a.sign b.sign)
                           a.sign
                         (bool->bit (eql (rc->rounding-mode rc) :rmi)))
                 :man 0 :exp 0)
              (fp-arith-triple-fix b))
            nil))
       ((when (Eql b.man 0))
        (mv (fp-arith-triple-fix a) nil))
       ;; (zero-mant (or (eql a.man 0) (eql b.man 0)))
       (aexp-lt-bexp (< a.exp b.exp))
       (bexp-lt-aexp (< b.exp a.exp))
       (a-shiftamt (- leftshift (if aexp-lt-bexp (- b.exp a.exp) 0)))
       (b-shiftamt (- leftshift (if bexp-lt-aexp (- a.exp b.exp) 0)))
       (ashift.man (bitops::limshift-loghead-of-ash (+ (lposfix a-width) leftshift) a.man a-shiftamt))
       (bshift.man (bitops::limshift-loghead-of-ash (+ (lposfix b-width) leftshift) b.man b-shiftamt))
       (a-sticky (and ;; aexp-lt-bexp
                      (< a-shiftamt 0)
                      (not (eql 0 (loghead (- a-shiftamt) a.man)))))
       (b-sticky (and ;; bexp-lt-aexp
                      (< b-shiftamt 0)
                      (not (eql 0 (loghead (- b-shiftamt) b.man)))))
       (stickyp (or a-sticky b-sticky))
       ((mv sum sign cancel)
        (if (and (eql a.sign b.sign)
                 (not (and (eql 0 a.man)
                           (eql 0 b.man))))
            (mv (+ ashift.man bshift.man) a.sign nil)
          (if (eql ashift.man bshift.man)
              ;; Note: It should be impossible for either sticky bit to be set
              ;; here, if the widths are set properly.
              ;; However, if this is somehow violated, checking the sticky here
              ;; lets us set the sign properly at least.
              (cond (a-sticky (mv 0 a.sign nil))
                    (b-sticky (mv 0 b.sign nil))
                    (t (mv 0
                           (bool->bit (eql (rc->rounding-mode rc) :rmi))
                           t)))
            (if (< bshift.man ashift.man)
              ;;   (mv (fgl::binary-minus ashift.man (+ bshift.man (bool->bit b-sticky))) a.sign nil)
                ;; (mv (fgl::binary-minus bshift.man (+ ashift.man (bool->bit a-sticky))) b.sign nil)
                (mv (fgl::+carry (not b-sticky) ashift.man (lognot bshift.man)) a.sign nil)
              (mv (fgl::+carry (not a-sticky) bshift.man (lognot ashift.man)) b.sign nil)
              )
            )))
       (exp (if cancel 0 (- (if aexp-lt-bexp b.exp a.exp)
                            leftshift))))
    (mv (make-fp-arith-triple :man sum :sign sign :exp exp) stickyp))
  ///

  (local (in-theory (disable acl2::unsigned-byte-p-plus
                             acl2::logtail-identity)))
  
  (local (defthm fp-sign-value-redef
           (equal (fp-sign-value x)
                  (if (equal (bfix x) 1)
                      -1
                    1))
           :hints(("Goal" :in-theory (enable fp-sign-value)))))

  (local (defthm left-shift-of-plus
           (implies (and (integerp a) (integerp b)
                         (natp sh))
                    (equal (ash (+ a b) sh)
                           (+ (Ash a sh)
                              (ash b sh))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))

  
  (local (defthm left-shift-equal-0
           (implies (natp sh)
                    (equal (equal (ash x sh) 0)
                           (zip x)))
           :hints(("Goal" :in-theory (enable* bitops::ash-is-expt-*-x)))))

  (local (defthm integer-length-of-plus-ash
           (implies (and (natp b) (natp d))
                    (equal (integer-length (+ (ash a b) (ash c d)))
                           (if (equal 0 (+ (ash a b) (ash c d)))
                               0
                             (+ (min b d)
                                (integer-length (+ (ash a (- b (min b d)))
                                                   (ash c (- d (min b d)))))))))
           :hints (("goal" :use ((:instance bitops::integer-length-of-ash
                                  (n (+ (ash a (- b (min b d)))
                                        (ash c (- d (min b d)))))
                                  (m (min b d)))
                                 (:instance left-shift-equal-0
                                  ( x (+ (ash a (- b (min b d)))
                                         (ash c (- d (min b d)))))
                                  (sh (min b d))))
                    :in-theory (disable bitops::integer-length-of-ash
                                        left-shift-equal-0)))))
                                              

  (local (defthm logtail-of-plus-ash
           (implies (and (natp b) (natp d))
                    (equal (logtail n (+ (ash a b) (ash c d)))
                           (ash (+ (ash a (- b (min b d)))
                                   (ash c (- d (min b d))))
                                (- (min b d) (nfix n)))))
           :hints (("goal" :use ((:instance bitops::logtail-of-ash
                                  (x (+ (ash a (- b (min b d)))
                                        (ash c (- d (min b d)))))
                                  (sh1 (min b d))
                                  (sh2 n)))
                    :in-theory (disable bitops::logtail-of-ash)))))

  (local (defthm replace-integer-length-+
           (implies (Equal (+ a b c (integer-length (+ x (ash y n)))) d)
                    (equal (integer-length (+ x (ash y n)))
                           (- d (+ a b c))))))

  (local (defthm expt-same-equal
           (equal (EQual (expt 2 m) (expt 2 n))
                  (equal (ifix m) (ifix n)))
           :hints(("Goal" :use ((:instance acl2::expt-is-increasing-for-base>1
                                 (r 2) (i (ifix m)) (j (ifix n)))
                                (:instance acl2::expt-is-increasing-for-base>1
                                 (r 2) (j (ifix m)) (i (ifix n))))
                   :in-theory (disable acl2::expt-is-increasing-for-base>1))
                  (and stable-under-simplificationp
                       '(:in-theory (enable ifix))))))
  
  (local (defthm ash-of-same-equal
           (implies (and (not (equal 0 (ifix x)))
                         (natp m) (natp n))
                    (equal (equal (ash x m) (ash x n))
                           (equal m n)))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))
  
  (local (defund equalll (x y) (equal x y)))


  (local (defthm left-shift-same-amount-equal
           (implies (natp n)
                    (equal (equal (ash x n) (ash y n))
                           (equal (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))
  
  (local (defthm left-shift-same-amount-equalll
           (implies (natp n)
                    (equal (equalll (ash x n) (ash y n))
                           (equalll (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x
                                             equalll)))))

  (local (defthmd equal-of-left-shifts-lemma
           (implies (and (natp n) (natp m))
                    (equal (equalll (ash x n) (ash y m))
                           (equalll (ash x (- n (min m n)))
                                    (ash y (- m (min m n))))))
           :hints (("goal" :use ((:instance left-shift-same-amount-equalll
                                  (x (ash x (- n (min m n))))
                                  (y (ash y (- m (min m n))))
                                  (n (min m n))))
                    :in-theory (disable left-shift-same-amount-equalll)))))


  (local (defthm equal-of-left-shifts
           (implies (and (natp n) (natp m))
                    (equal (equal (ash x n) (ash y m))
                           (equal (ash x (- n (min m n)))
                                  (ash y (- m (min m n))))))
           :hints (("goal" :use equal-of-left-shifts-lemma
                    :in-theory (enable equalll)))))

  
  (local (defthm left-shift-same-amount-<
           (implies (natp n)
                    (equal (< (ash x n) (ash y n))
                           (< (ifix x) (ifix y))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))


  (local (defthm <-of-left-shifts
           (implies (and (natp n) (natp m))
                    (equal (< (ash x n) (ash y m))
                           (< (ash x (- n (min m n)))
                              (ash y (- m (min m n))))))
           :hints (("goal" :use ((:instance left-shift-same-amount-<
                                  (x (ash x (- n (min m n))))
                                  (y (ash y (- m (min m n))))
                                  (n (min m n))))
                    :in-theory (disable left-shift-same-amount-<)))))

  (local (defthm left-shift-of-minus
           (implies (natp n)
                    (equal (ash (- x) n)
                           (- (ash (ifix x) n))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x
                                             ifix)))))

  (local (defthm integer-length-of-minus-ash
           (implies (and (natp b) (natp d))
                    (equal (integer-length (+ (- (ash a b)) (ash c d)))
                           (if (equal 0 (+ (- (ash a b)) (ash c d)))
                               0
                             (+ (min b d)
                                (integer-length (+ (- (ash a (- b (min b d))))
                                                   (ash c (- d (min b d)))))))))
           :hints (("goal" :use ((:instance integer-length-of-plus-ash
                                  (a (- a))))
                    :in-theory (disable integer-length-of-plus-ash)))))

  (local (defthm integer-length-of-minus-ash2
           (implies (and (natp b) (natp d))
                    (equal (integer-length (+ (ash a b) (- (ash c d))))
                           (if (equal 0 (+ (ash a b) (- (ash c d))))
                               0
                             (+ (min b d)
                                (integer-length (+ (ash a (- b (min b d)))
                                                   (- (ash c (- d (min b d))))))))))
           :hints (("goal" :use ((:instance integer-length-of-plus-ash
                                  (c (- c))))
                    :in-theory (disable integer-length-of-plus-ash))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ifix))))))

  (local (defthm equal-0-of-minus-ash
           (equal (equal 0 (+ (- (ash x n)) (ash y m)))
                  (equal (ash x n) (ash y m)))))

  (local (defthm logtail-of-minus-ash
           (implies (and (natp b) (natp d))
                    (equal (logtail n (+ (- (ash a b)) (ash c d)))
                           (ash (+ (- (ash a (- b (min b d))))
                                   (ash c (- d (min b d))))
                                (- (min b d) (nfix n)))))
           :hints (("goal" :use ((:instance logtail-of-plus-ash
                                  (a (- a))))
                    :in-theory (disable logtail-of-plus-ash)))))

  (local (defthm logtail-of-minus-ash2
           (implies (and (natp b) (natp d))
                    (equal (logtail n (+ (ash a b) (- (ash c d))))
                           (ash (+ (ash a (- b (min b d)))
                                   (- (ash c (- d (min b d)))))
                                (- (min b d) (nfix n)))))
           :hints (("goal" :use ((:instance logtail-of-plus-ash
                                  (c (- c))))
                    :in-theory (disable logtail-of-plus-ash))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ifix))))))

  (local (defun logtail-left-plus-ind (n m y)
           (if (zp n)
               (list m y)
             (logtail-left-plus-ind (1- n) (1- m) (logcdr y)))))

  (local (defthm logtail-of-left-shift-plus
           (implies (and (integerp y) (natp m))
                    (equal (logtail n (+ (ash x m) y))
                           (if (< m (nfix n))
                               (logtail (- n m) (+ (ifix x) (logtail m y)))
                             (+ (ash x (- m (nfix n)))
                                (logtail n y)))))
           :hints (("goal" :induct (logtail-left-plus-ind n m y)
                    :expand ((:free (xx) (logtail n (+ y xx)))
                             (logtail m y)
                             (logtail n y)
                             (ash x m))))))
  
  (local (defthm logtail-of-left-shift-plus2
           (implies (and (integerp y) (natp m))
                    (equal (logtail n (+ y (ash x m)))
                           (if (< m (nfix n))
                               (logtail (- n m) (+ (ifix x) (logtail m y)))
                             (+ (ash x (- m (nfix n)))
                                (logtail n y)))))
           :hints (("goal" :use logtail-of-left-shift-plus
                    :in-theory (disable logtail-of-left-shift-plus)))))

  
  
  (local (defthm logtail-of-minus-left-shift
           (implies (and (integerp y) (natp m))
                    (equal (logtail n (+ y (- (ash x m))))
                           (if (< m (nfix n))
                               (logtail (- n m) (+ (- (ifix x)) (logtail m y)))
                             (+ (- (ash x (- m (nfix n))))
                                (logtail n y)))))
           :hints (("goal" :use ((:instance logtail-of-left-shift-plus
                                  (x (- x))))
                    :in-theory (disable logtail-of-left-shift-plus))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ifix))))))

  (local (defthm logcdr-of-neg
           (implies (integerp x)
                    (equal (logcdr (- x))
                           (+ (- (logcar x)) (- (logcdr x)))))
           :hints (("goal" :in-theory (e/d (bitops::minus-to-lognot)
                                           (lognot))))))


  (local (defthm logtail-of-neg-ash
           (implies (natp m)
                    (equal (logtail n (- (ash x m)))
                           (logtail (- (nfix n) (min m (nfix n)))
                                    (- (ash x (- m (min m (nfix n))))))))
           :hints (("goal" :use ((:instance bitops::logtail-of-ash
                                  (sh2 n) (sh1 m) (x (- x)))
                                 (:instance bitops::logtail-of-ash
                                  (sh2 (- (nfix n) (min m (nfix n))))
                                  (sh1 (- m (min m (nfix n)))) (x (- x))))
                    :in-theory (disable bitops::logtail-of-ash)))))
  
  (local (defthm integer-length-equal-0-when-natp
           (implies (natp x)
                    (equal (equal 0 (integer-length x))
                           (Equal 0 x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm integer-length-of-ash-plus-logtail
           (implies (and (natp n)
                         (< 0 (+ (ifix x) (logtail (+ n (nfix m)) y))))
                    (equal (integer-length (+ (ash x n) (logtail m y)))
                           (+ n (integer-length (+ (ifix x) (logtail (+ n (nfix m)) y))))))
           :hints (("goal" :use ((:instance bitops::integer-length-of-logtail
                                  (n n)
                                  (x (+ (ash x n) (logtail m y)))))
                    :in-theory (disable bitops::integer-length-of-logtail)
                    :cases ((<= 0 (+ (- N)
                              (INTEGER-LENGTH (+ (ASH X N) (LOGTAIL M Y))))))))))
  
  (local (defthm logtail-0
           (equal (logtail 0 x)
                  (ifix x))))

  (local (defthm logtail-<=-ash
           (implies (and (integerp y)
                         (<= (ifix x) (ash y (nfix n))))
                    (<= (logtail n x) y))
           :hints (("Goal" :induct (logtail n x)
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        bitops::logcons-<-n-strong)))))


  (local (Defthmd logtail-of-equal-to-ash
           (implies (equal x (ash y n))
                    (equal (logtail m x)
                           (ash y (+ (ifix n) (- (nfix m))))))))
  
  (local (defthm logtail->=-ash
           (implies (and (integerp y)
                         (>= (ifix x) (ash y (nfix n))))
                    (>= (logtail n x) y))
           :hints (("Goal" :induct (logtail n x)
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        bitops::logcons-<-n-strong
                                        bitops::logcons->-n-strong
                                        logtail-of-equal-to-ash)))))

  (local (defthm rewrite-<=-hyp-to-<-when-not-equal
           (implies (and (acl2::rewriting-positive-literal `(< ,a ,b))
                         (not (equal (fix a) (fix b))))
                    (equal (< a b)
                           (<= a b)))))

  (local (defthm logtail-of-minus
           (implies (integerp x)
                    (equal (logtail n (- x))
                           (if (equal (loghead n x) 0)
                               (- (logtail n x))
                             (+ -1 (- (logtail n x))))))
           :hints(("Goal" :in-theory (e/d* (bitops::minus-to-lognot
                                            bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (lognot))))))
  

  (local (defthm loghead-of-left-shift-plus
           (implies (and (integerp y)
                         (natp m)
                         (<= (nfix n) (ifix m)))
                    (equal (loghead n (+ y (ash x m)))
                           (loghead n y)))
           :hints (("goal" :induct (logtail-left-plus-ind n m y)
                    :expand ((:free (y) (loghead n y))
                             (ash x m))))))

  (local (defthm loghead-of-left-shift-minus
           (implies (and (integerp y)
                         (natp m)
                         (<= (nfix n) (ifix m)))
                    (equal (loghead n (+ y (- (ash x m))))
                           (loghead n y)))
           :hints (("goal" :use ((:instance loghead-of-left-shift-plus
                                  (x (- x))))
                    :in-theory (disable loghead-of-left-shift-plus))
                   (and stable-under-simplificationp
                        '(:in-theory (enable ifix))))))

  (local (defthm loghead-equal-0-of-neg
           (implies (integerp x)
                    (equal (equal 0 (loghead n (- x)))
                           (equal 0 (loghead n x))))
           :hints(("Goal" :in-theory (e/d* (bitops::minus-to-lognot
                                            bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (lognot))))))

  (local (defthm ash-of-logtail-same-shift-<=
           (implies (natp n)
                    (<= (ash (logtail n x) n) (ifix x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs
                                            bitops::logcons->-n-strong))))
           :rule-classes :linear))
  
  (local (defthmd logtail-equal-when-ash->=
           (implies (and (<= (ifix x) (ash y (nfix m)))
                         (not (equal 0 (loghead m x))))
                    (not (equal (logtail m x) y)))
           :hints (("goal" 
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        bitops::logcons-<-n-strong
                                        )
                    :expand ((:free (y) (logtail m y))
                             (:free (y) (loghead m y)))))))

  (local (defthm logtail-equal-when-loghead-0
           (implies (equal 0 (loghead m x))
                    (equal (equal (logtail m x) y)
                           (and (integerp y)
                                (equal (ifix x) (ash y (nfix m))))))
           :hints (("goal" 
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs
                                        bitops::equal-logcons-strong
                                        )
                    :expand ((:free (y) (logtail m y))
                             (:free (y) (loghead m y)))))))

  (local (defthm logtail-equal-ash-when-ash->=
           (implies (and (<= (ifix x) (ash y (+ n (nfix m))))
                         (not (equal 0 (loghead m x)))
                         (natp n))
                    (not (equal (logtail m x) (ash y n))))
           :hints (("goal" :use ((:instance logtail-equal-when-ash->=
                                  (y (ash y n))))))))


  (defret <fn>-is-shift-of-add-core-naive
    (implies (and (unsigned-byte-p (pos-fix a-width) (fp-arith-triple->man a))
                  (unsigned-byte-p (pos-fix b-width) (fp-arith-triple->man b))
                  ;; (not (equal 0 (fp-arith-triple->man a)))
                  ;; (not (equal 0 (fp-arith-triple->man b)))
                  ;; (>= (nfix leftshift) (pos-fix a-width))
                  ;; (>= (nfix leftshift) (pos-fix b-width))
                  ;; (<= (fp-size->frac-size size) (+ 1 leftshift))
                  )
             (b* (((fp-arith-triple spec) (fp-add-core-naive a b rc :verbosep nil))
                  ((fp-arith-triple a))
                  ((fp-arith-triple b))
                  ;;(zero-man (or (eql a.man 0) (eql b.man 0)))
                  (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                  (zero (or (equal spec.man 0)
                            (equal a.man 0)
                            (equal b.man 0))))
               (and (implies (and (<= 0 rel-shift)
                                  (not zero))
                             (and (equal sum (fp-arith-leftshift spec rel-shift))
                                  (not stickyp)
                                  ))
                    (implies (and (< rel-shift 0)
                                  (not zero))
                             (and (equal sum (fp-arith-rightshift spec (- rel-shift)))
                                  (equal stickyp
                                         (not (equal 0 (loghead (- rel-shift) spec.man))))))
                    (implies zero
                             (and (equal sum spec)
                                  (not stickyp)
                                  )))))
    :hints(("Goal" :in-theory (enable fp-add-core-naive
                                      fp-arith-leftshift
                                      fp-arith-rightshift)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:cases ((< (- (nfix leftshift) (abs (- (fp-arith-triple->exp a) (fp-arith-triple->exp b)))) 0)))))))

 


(defsection fp-add-core2-integer-length-when-sticky

  (local (std::set-define-current-function fp-add-core2))

  (defret <fn>-integer-length-when-sticky-and-big-leftshift
    (implies (and stickyp
                  (unsigned-byte-p (pos-fix a-width) (fp-arith-triple->man a))
                  (unsigned-byte-p (pos-fix b-width) (fp-arith-triple->man b))
                  ;; (not (equal 0 (fp-arith-triple->man a)))
                  ;; (not (equal 0 (fp-arith-triple->man b)))
                  (>= (nfix leftshift) (pos-fix a-width))
                  (>= (nfix leftshift) (pos-fix b-width)))
             (<= (+ -1 (nfix leftshift)) (integer-length (fp-arith-triple->man sum))))
    :hints (("goal" :do-not-induct t
             :cases ((b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       zero)
                     (b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       (and (not zero) (<= 0 rel-shift)))))
            (and stable-under-simplificationp
                 (cond ((member-equal '(< (FP-ARITH-TRIPLE->EXP$INLINE A)
                                          (FP-ARITH-TRIPLE->EXP$INLINE B))
                                      clause)
                        ;; b.exp <= a.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-1
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-1)))
                       (t
                        ;; a.exp < b.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-3
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-3))))))
    :rule-classes :linear)

  (defret <fn>-integer-length-when-sticky-and-denorm-restriction
    (implies (and stickyp
                  (unsigned-byte-p (pos-fix a-width) (fp-arith-triple->man a))
                  (unsigned-byte-p (pos-fix b-width) (fp-arith-triple->man b))
                  ;; (not (equal 0 (fp-arith-triple->man a)))
                  ;; (not (equal 0 (fp-arith-triple->man b)))
                  (implies (< (integer-length (fp-arith-triple->man a))
                              (integer-length (fp-arith-triple->man b)))
                           (<= (fp-arith-triple->exp a)
                               (fp-arith-triple->exp b)))
                  (implies (< (integer-length (fp-arith-triple->man b))
                              (integer-length (fp-arith-triple->man a)))
                           (<= (fp-arith-triple->exp b)
                               (fp-arith-triple->exp a)))
                  (posp leftshift))
             (and (<= (+ -1 leftshift (integer-length (fp-arith-triple->man a)))
                      (integer-length (fp-arith-triple->man sum)))
                  (<= (+ -1 leftshift (integer-length (fp-arith-triple->man b)))
                      (integer-length (fp-arith-triple->man sum)))))
    :hints (("goal" :do-not-induct t
             :cases ((b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       zero)
                     (b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       (and (not zero) (<= 0 rel-shift)))))
            (and stable-under-simplificationp
                 (cond ((member-equal '(< (FP-ARITH-TRIPLE->EXP$INLINE A)
                                          (FP-ARITH-TRIPLE->EXP$INLINE B))
                                      clause)
                        ;; b.exp <= a.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-1
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-1)))
                       (t
                        ;; a.exp < b.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-3
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-3))))))
    :rule-classes :linear))


(defsection normalize-arith-triple-of-shift

  (local (defthm left-shift-equal-0
           (implies (natp sh)
                    (equal (equal (ash x sh) 0)
                           (zip x)))
           :hints(("Goal" :in-theory (enable* bitops::ash-is-expt-*-x)))))
  
  (local (defthm loghead-of-ash-equal-0
           (implies (natp m)
                    (equal (equal 0 (loghead n (ash x m)))
                           (equal 0 (loghead (- (nfix n) m) x))))
           :hints(("Goal" :in-theory (enable bitops::loghead-of-ash)))))

  (local (defthm loghead-when-zp
           (implies (zp n)
                    (equal (loghead n x) 0))))
  
  (defthm normalize-arith-triple-of-leftshift
    (implies (not (equal 0 (fp-arith-triple->man x)))
             (equal (normalize-arith-triple (fp-arith-leftshift x n))
                    (normalize-arith-triple x)))
    :hints(("Goal" :in-theory (enable normalize-arith-triple
                                      fp-arith-leftshift
                                      fp-arith-rightshift))))

  (local (defthm loghead-equal-0-when-less
           (implies (and (not (equal 0 (loghead n x)))
                         (<= (nfix n) (nfix m)))
                    (not (equal 0 (loghead m x))))
           :hints (("goal" :use ((:instance bitops::loghead-of-loghead-1
                                  (m n) (n m) (x x)))
                    :in-theory (disable bitops::loghead-of-loghead-1)))))

  (local (defthm loghead-of-logtail-equal-0
           (implies (and (equal 0 (loghead n x))
                         (<= (+ (nfix m) (nfix sh)) (nfix n)))
                    (equal (equal 0 (loghead m (logtail sh x)))
                           t))
           :hints (("goal" :use ((:instance bitops::logtail-of-loghead
                                  (n sh) (m (+ (nfix m) (nfix sh))) (x x))
                                 (:instance loghead-equal-0-when-less
                                  (m n) (n (+ (nfix m) (nfix sh)))))
                    :in-theory (disable bitops::logtail-of-loghead)))))


  (local (defthm loghead-of-logtail-not-equal-0
           (implies (and (not (equal 0 (loghead (+ (nfix m) (nfix sh)) x)))
                         (equal 0 (loghead sh x)))
                    (not (equal 0 (loghead m (logtail sh x)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthm logtail-nonzero-by-integer-length
           (implies (< (nfix shift) (integer-length x))
                    (not (equal 0 (logtail shift x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defthm normalize-arith-triple-of-rightshift-when-long
    (implies (and ;; (not (equal 0 (fp-arith-triple->man x)))
              (<= (nfix n) (- (integer-length (fp-arith-triple->man x))
                              (+ 2 (fp-size->frac-size size))))
              (iff sticky-in (not (equal 0 (loghead n (fp-arith-triple->man x))))))
             (equal (normalize-arith-triple (fp-arith-rightshift x n)
                                            :sticky-in sticky-in)
                    (normalize-arith-triple x)))
    :hints(("Goal" :in-theory (enable normalize-arith-triple
                                      fp-arith-leftshift
                                      fp-arith-rightshift))))


  (local (defthm nfix-when-zp
           (implies (zp x)
                    (equal (nfix x) 0))))

  (local (defthm loghead-equal-0-when-integer-length-less
           (implies (and (<= (integer-length x) (nfix n))
                         (natp x))
                    (equal (equal 0 (loghead n x))
                           (equal 0 (ifix x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm ash-logtail-when-loghead-0
           (implies (and (equal 0 (loghead n x)))
                    (equal (ash (logtail n x) m)
                           (ash x (- (ifix m) (nfix n)))))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logbitp-when-loghead-0
           (implies (And (equal 0 (loghead n x))
                         (< (nfix m) (nfix n)))
                    (not (logbitp m x)))
           :hints ((bitops::logbitp-reasoning))))
  
  (defthm normalize-arith-triple-of-rightshift-when-no-sticky
    (implies (and ;; (not (equal 0 (fp-arith-triple->man x)))
              (equal 0 (loghead n (fp-arith-triple->man x)))
              ;; (not (equal 0 (fp-arith-triple->man x)))
              )
             (equal (normalize-arith-triple (fp-arith-rightshift x n))
                    (normalize-arith-triple x)))
    :hints(("Goal" :in-theory (enable normalize-arith-triple
                                      fp-arith-leftshift
                                      fp-arith-rightshift)
            :cases ((< (nfix n) (integer-length (fp-arith-triple->man x))))))))


(defsection normalize-of-fp-add-core2
  (local (std::set-define-current-function fp-add-core2))

  (defret fp-add-core2-correct-by-normalization-when-big-leftshift
    (implies (and (unsigned-byte-p (pos-fix a-width) (fp-arith-triple->man a))
                  (unsigned-byte-p (pos-fix b-width) (fp-arith-triple->man b))
                  ;; (not (equal 0 (fp-arith-triple->man a)))
                  ;; (not (equal 0 (fp-arith-triple->man b)))
                  (>= (nfix leftshift) (pos-fix a-width))
                  (>= (nfix leftshift) (pos-fix b-width))
                  (>= (nfix leftshift) (+ 2 (fp-size->frac-size size))))
             (equal (normalize-arith-triple sum :sticky-in stickyp)
                    (normalize-arith-triple
                     (fp-add-core-naive a b rc))))
    :hints (("goal" :do-not-induct t
             :cases ((b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       zero)
                     (b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       (and (not zero) (<= 0 rel-shift)))))
            (and stable-under-simplificationp
                 (cond ((member-equal '(< (FP-ARITH-TRIPLE->EXP$INLINE A)
                                          (FP-ARITH-TRIPLE->EXP$INLINE B))
                                      clause)
                        ;; b.exp <= a.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-1
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-1)))
                       (t
                        ;; a.exp < b.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-3
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-3)))))))

  (defret fp-add-core2-correct-by-normalization-when-denorm-restriction
    :pre-bind (((fp-size size))
               (a-width (+ 1 size.frac-size))
               (b-width (+ 1 size.frac-size)))
    (implies (and (unsigned-byte-p (+ 1 size.frac-size) (fp-arith-triple->man a))
                  (unsigned-byte-p (+ 1 size.frac-size) (fp-arith-triple->man b))
                  ;; (not (equal 0 (fp-arith-triple->man a)))
                  ;; (not (equal 0 (fp-arith-triple->man b)))
                  (implies (< (integer-length (fp-arith-triple->man a)) (+ 1 size.frac-size))
                           (<= (fp-arith-triple->exp a)
                               (fp-arith-triple->exp b)))
                  (implies (< (integer-length (fp-arith-triple->man b)) (+ 1 size.frac-size))
                           (<= (fp-arith-triple->exp b)
                               (fp-arith-triple->exp a)))
                  (<= 2 (nfix leftshift)))
             (equal (normalize-arith-triple sum :sticky-in stickyp)
                    (normalize-arith-triple
                     (fp-add-core-naive a b rc))))
    :hints (("goal" :do-not-induct t
             :cases ((b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       zero)
                     (b* (((fp-arith-triple spec) (fp-add-core-naive a b rc))
                          ((fp-arith-triple a))
                          ((fp-arith-triple b))
                          (?rel-shift (- (nfix leftshift) (abs (- a.exp b.exp))))
                          (zero (or (equal spec.man 0)
                                    (equal a.man 0)
                                    (equal b.man 0))))
                       (and (not zero) (<= 0 rel-shift)))))
            (and stable-under-simplificationp
                 (cond ((member-equal '(< (FP-ARITH-TRIPLE->EXP$INLINE A)
                                          (FP-ARITH-TRIPLE->EXP$INLINE B))
                                      clause)
                        ;; b.exp <= a.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-1
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-1)))
                       (t
                        ;; a.exp < b.exp
                        '(:use ((:instance integer-length-lower-bound-of-fp-add-core-naive-sub-far-3
                                 (acc b) (prod a)))
                          :in-theory (disable integer-length-lower-bound-of-fp-add-core-naive-sub-far-3)))))))

  )





(define fp-add-core ((prod fp-arith-triple-p)
                     (acc  fp-arith-triple-p)
                     (rc fp-rc-p)
                     &key
                     ((size fp-size-p) 'size)
                     ((verbosep) 'verbosep))
  :short "An alternative version of @(tsee fp-add-core-naive) that is
  optimized for symbolic simulation"

  :guard (and (posp (fp-arith-triple->man prod))
              (<= (integer-length (fp-arith-triple->man prod))
                  (+ 2 (fp-size->frac-size size) (fp-size->frac-size size)))
              (posp (fp-arith-triple->man acc))
              (<= (integer-length (fp-arith-triple->man acc))
                  (+ 1 (fp-size->frac-size size))))

  :returns (mv (sum fp-arith-triple-p)
               (stickyp booleanp :rule-classes :type-prescription))

  :prepwork
  ((local
    (defthm leftshift-posp-is-posp
      (implies (and (< 0 (fp-arith-triple->man x)) (natp n))
               (not (equal (fp-arith-triple->man (fp-arith-leftshift x n)) 0)))
      :hints (("goal" :in-theory (e/d (fp-arith-leftshift
                                       (:executable-counterpart tau-system))
                                      ())))))

   (local
    (in-theory (e/d (fp-arith-leftshift-opt-is-fp-arith-leftshift)
                    ()))))

  (b* (((fp-size size))
       (- (cw-verbose "~% Size: ~x0 ~%" size))
       ;; Left shift prod so that it has 2f+4 bits (low 2 bits are zeroes).
       ((fp-arith-triple p)
        (fp-arith-leftshift-opt (+ 4 (* 2 size.frac-size)) prod 2))
       ;; Left shift acc so that it has 2f+3 bits (low f+2 bits are zeroes).
       ((fp-arith-triple a)
        (fp-arith-leftshift-opt (+ 3 (* 2 size.frac-size)) acc (+ 2 size.frac-size)))

       (ediff (- p.exp a.exp))
       (eff-add (b-not (b-xor p.sign a.sign)))
       (- (cw-verbose "~% Left-shifted Prod.:~% ~x0 ~%" p))
       (- (cw-verbose "~% Left-shifted Acc.:~%  ~x0 ~%" a))
       (- (cw-verbose "~% Ediff: ~x0 Eff-add: ~x1 ~%" ediff eff-add))

       ((mv sign exp sum-mantissa stickyp)
        (cond ((< (+ size.frac-size size.frac-size 3) ediff)
               ;; P is far bigger than A, and A is reduced to sticky
               ;; (A is non-zero here).

               (if (eql eff-add 1)
                   (mv p.sign p.exp p.man t)
                 ;; We subtract the sticky from P and pass on the sticky
                 ;; for rounding.
                 (mv p.sign p.exp (- p.man 1) t)))

              ((and (<= 0 ediff) (<= ediff (+ size.frac-size size.frac-size 3)))
               ;; Pexp is bigger than Aexp, but there is overlap
               ;; between them.  We shift A to the right.
               (b* ((a-man-aligned
                     (bitops::limshift-loghead-of-ash (+ 3 size.frac-size size.frac-size) a.man (- ediff)))
                    (a-stickyp (not (eql (loghead ediff a.man) 0))))
                 (cond ((eql eff-add 1)
                        (mv p.sign p.exp (+ p.man a-man-aligned) a-stickyp))
                       (t
                        (if (< a-man-aligned p.man)
                            ;; P is indeed bigger.
                            (mv p.sign p.exp (+ p.man (- a-man-aligned) (- (bool->bit a-stickyp))) a-stickyp)
                          ;; A is bigger.
                          (mv a.sign p.exp (+ a-man-aligned (- p.man)) a-stickyp))))))

              ((and (<= (- (+ 4 size.frac-size size.frac-size)) ediff) (< ediff 0))
               ;; Aexp is bigger than Pexp, but there is overlap
               ;; between them. We shift A to the left.
               (b* ((a-man-aligned
                     (bitops::limshift-loghead-of-ash
                      (+ 7 size.frac-size size.frac-size size.frac-size size.frac-size)
                      a.man (- ediff)))
                    (a-stickyp nil)
                    (- (cw-verbose "~% a-man-aligned: ~s0 a-stickyp: ~x1 ~%" (str::hexify a-man-aligned) a-stickyp)))
                 (cond ((eql eff-add 1)
                        (mv a.sign (+ a.exp ediff) (+ a-man-aligned p.man) a-stickyp))
                       (t
                        (if (< p.man a-man-aligned)
                            ;; A is indeed bigger.
                            (mv a.sign (+ a.exp ediff) (+ a-man-aligned (- p.man) (- (bool->bit a-stickyp))) a-stickyp)
                          ;; P is bigger.
                          (mv p.sign (+ a.exp ediff) (+ p.man (- a-man-aligned)) a-stickyp))))))

              (t ;; (< ediff (- (+ 4 size.frac-size size.frac-size)))
               ;; A is far bigger than P, and P is reduced to sticky
               ;; (P is non-zero here).
               (if (eql eff-add 1)
                   (mv a.sign a.exp a.man t)
                 ;; We subtract sticky from A and also pass it on for
                 ;; rounding.
                 (mv a.sign a.exp (- a.man 1) t)))))

       (- (cw-verbose "~% Sign: ~x0 Sum-mantissa: ~s1 ~% Alignment-stickyp: ~x2 ~%"
                      sign (str::hexify sum-mantissa) stickyp))

       (sum (if (eql sum-mantissa 0)
                (make-fp-arith-triple :sign (if stickyp
                                                ;; Retain the sign of the bigger operand.
                                                sign
                                              ;; This can only happen
                                              ;; when P and A are
                                              ;; exact opposites of
                                              ;; each other. The
                                              ;; result should be -0
                                              ;; when rounding down
                                              ;; and +0 otherwise.
                                              (bool->bit (eql (rc->rounding-mode rc) :rmi)))
                                      :exp 0
                                      :man 0)
              (make-fp-arith-triple :sign sign
                                    :exp exp
                                    :man sum-mantissa))))
    (mv sum stickyp))

  ///

  (defret posp-<fn>.man-when-non-zero-exp-no-stickyp
    (b* (((fp-arith-triple sum)))
      (implies (and (not (eql sum.exp 0))
                    (not stickyp))
               (posp sum.man))))

  (defret posp-<fn>.man-when-non-zero-exp-stickyp
    (b* (((fp-arith-triple sum)))
      (implies (and (not (eql sum.exp 0))
                    stickyp
                    (posp (fp-arith-triple->man prod))
                    (<= (integer-length (fp-arith-triple->man prod))
                        (+ 2 (fp-size->frac-size size) (fp-size->frac-size size)))
                    (posp (fp-arith-triple->man acc))
                    (<= (integer-length (fp-arith-triple->man acc))
                        (+ 1 (fp-size->frac-size size))))
               (posp sum.man)))))

