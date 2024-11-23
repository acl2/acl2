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

;; ======================================================================

(in-package "IFP")

(include-book "fp-common")
(include-book "centaur/bitops/rational-exponent" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p)))

(defthmd fp-sign-value-redef
  (equal (fp-sign-value x)
         (if (equal x 1) -1 1))
  :hints (("Goal" :in-theory (enable fp-sign-value))))

(local (defthm equal-0-of-leftshift
         (implies (natp sh)
                  (equal (equal 0 (ash x sh))
                         (zip x)))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

(local (defthm fp-arith-triple->rational-is-0-when-man
         (implies (equal 0 (fp-arith-triple->man x))
                  (equal (fp-arith-triple->rational x) 0))
         :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

(defsection rational-sign-significand-exponent-of-fp-arith-triple->rational

  (local (defthm bounds-of-normalize-significand-1
           (implies (posp x)
                    (b* ((norm (* x (/ (expt 2 (+ -1 (integer-length x)))))))
                      (and (<= 1 norm)
                           (< norm 2))))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               logcons
                                               expt)
                    :expand ((integer-length x))))
           :rule-classes :linear))

  (defthm bounds-of-normalize-significand
    (implies (posp x)
             (b* ((norm (* x (expt 2 (+ 1 (- (integer-length x)))))))
               (and (<= 1 norm)
                    (< norm 2))))
    :hints (("Goal" :use ((:instance acl2::expt-minus
                                     (r 2) (i (+ -1 (integer-length x))))
                          bounds-of-normalize-significand-1)
             :in-theory (disable ;; acl2::expt-minus
                         bounds-of-normalize-significand-1
                         acl2::<-*-/-left
                         acl2::equal-/)))
    :rule-classes :linear)

  (defthmd rational-sign-significand-exponent-of-fp-arith-triple->rational
    (b* (((fp-arith-triple x))
         (val (fp-arith-triple->rational x)))
      (and (implies (not (equal (fp-arith-triple->man x) 0))
                    (equal (rational-sign val) (fp-sign-value x.sign)))
           (equal (rational-significand val)
                  (* x.man (expt 2 (- 1 (integer-length x.man)))))
           (implies (not (equal (fp-arith-triple->man x) 0))
                    (equal (rational-exponent val)
                           (+ -1
                              (integer-length x.man)
                              x.exp)))))
    :hints (("Goal" :use ((:instance acl2::rational-sign-significand-exponent-unique
                                     (sign (fp-sign-value (fp-arith-triple->sign x)))
                                     (significand
                                      (* (fp-arith-triple->man x)
                                         (expt 2 (- 1 (integer-length (fp-arith-triple->man x))))))
                                     (exponent
                                      (+ -1
                                         (integer-length (fp-arith-triple->man x))
                                         (fp-arith-triple->exp x)))))
             :cases ((equal 0 (fp-arith-triple->man x)))
             :in-theory (enable fp-arith-triple->rational
                                rational-sign))
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               fp-sign-value
                               acl2::exponents-add-unrestricted))))))



(local (defthm logtail-nonzero-by-integer-length
         (implies (< (nfix n) (integer-length x))
                  (not (equal 0 (logtail n x))))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

(local
 (encapsulate
   nil

   (local (in-theory (disable bitops::logbitp-when-bitmaskp)))

   (local (defthm 1+logcons-0
            (equal (+ 1 (logcons 0 x))
                   (logcons 1 x))
            :hints (("Goal" :in-theory (enable logcons)))))

   (defthm ash-of-logtail-no-round-no-sticky
     (implies (and (natp n)
                   (equal 0 (loghead (+ -1 n) x))
                   (not (logbitp (+ -1 n) x)))
              (equal (ash (logtail n x) n)
                     (ifix x)))
     :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                         bitops::equal-logcons-strong)
              :induct (logtail n x)
              :expand ((logtail n x)
                       (:free (x) (ash x n))
                       (ash 1 (+ -1 n))
                       (loghead (+ -1 n) x)
                       (logbitp (+ -1 n) x)))))

   (local (defthmd ash-of-logtail-round-no-sticky-lemma
            (implies (and (natp n)
                          (equal 0 (loghead (+ -1 n) x))
                          (logbitp (+ -1 n) x))
                     (equal (+ (ash (logtail n x) n)
                               (ash 1 (+ -1 n)))
                            (ifix x)))
            :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                bitops::equal-logcons-strong)
                     :induct (logtail n x)
                     :expand ((logtail n x)
                              (:free (x) (ash x n))
                              (ash 1 (+ -1 n))
                              (loghead (+ -1 n) x)
                              (logbitp (+ -1 n) x))))))
   (defthm ash-of-logtail-round-no-sticky
     (implies (and (natp n)
                   (equal 0 (loghead (+ -1 n) x))
                   (logbitp (+ -1 n) x))
              (equal (ash (logtail n x) n)
                     (+ (- (ash 1 (+ -1 n)))
                        (ifix x))))
     :hints (("Goal" :use ash-of-logtail-round-no-sticky-lemma)))

   (local (defthmd ash-of-logtail-no-round-sticky-lemma
            (implies (and (natp n)
                          (not (equal 0 (loghead (+ -1 n) x)))
                          (not (logbitp (+ -1 n) x)))
                     (and (< (ifix x)
                             (+ (ash (logtail n x) n)
                                (ash 1 (+ -1 n))))
                          (< (ash (logtail n x) n)
                             (ifix x))))
            :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                bitops::logcons->-n-strong
                                                bitops::logcons-<-n-strong)
                     :induct (logtail n x)
                     :expand ((logtail n x)
                              (:free (x) (ash x n))
                              (ash 1 (+ -1 n))
                              (loghead (+ -1 n) x)
                              (logbitp (+ -1 n) x))))))

   (defthm ash-of-logtail-no-round-sticky
     (implies (and (natp n)
                   (not (equal 0 (loghead (+ -1 n) x)))
                   (not (logbitp (+ -1 n) x)))
              (and (< (ash (logtail n x) n)
                      (ifix x))
                   (< (+ (- (ash 1 (+ -1 n)))
                         (ifix x))
                      (ash (logtail n x) n))))
     :hints (("Goal" :use ash-of-logtail-no-round-sticky-lemma)))

   (local (defthm minus-plus-logcons-0
            (implies (integerp x)
                     (equal (+ (- x) (logcons 0 x))
                            x))
            :hints (("Goal" :in-theory (enable logcons)))))

   (local (defthmd ash-of-logtail-round-sticky-lemma
            (implies (and (natp n)
                          (not (equal 0 (loghead (+ -1 n) x)))
                          (logbitp (+ -1 n) x))
                     (and (< (+ (ash (logtail n x) n)
                                (ash 1 (+ -1 n)))
                             (ifix x))
                          (< (ifix x)
                             (+ (ash 1 n)
                                (ash (logtail n x) n)))))
            :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                bitops::logcons->-n-strong
                                                bitops::logcons-<-n-strong)
                     :induct (logtail n x)
                     :expand ((logtail n x)
                              (:free (x) (ash x n))
                              (ash 1 (+ -1 n))
                              (loghead (+ -1 n) x)
                              (logbitp (+ -1 n) x))))))

   (defthm ash-of-logtail-round-sticky
     (implies (and (natp n)
                   (not (equal 0 (loghead (+ -1 n) x)))
                   (logbitp (+ -1 n) x))
              (and (< (ash (logtail n x) n)
                      (+ (- (ash 1 (+ -1 n)))
                         (ifix x)))
                   (< (+ (- (ash 1 n))
                         (ifix x))
                      (ash (logtail n x) n))))
     :hints (("Goal" :use ash-of-logtail-round-sticky-lemma)))))



;; (local (defthm expt-*-logtail-bounds
;;          (implies (and (natp x))
;;                   (<= (* (expt 2 (nfix n))
;;                          (logtail n x))
;;                       x))
;;          :hints (("Goal" :use ((:instance ash-of-logtail-bounds (n (nfix n))))
;;                   :in-theory (e/d (bitops::ash-is-expt-*-x)
;;                                   (ash-of-logtail-bounds))))
;;          :rule-classes :linear))


(local
 (defthm fp-arith-triple->rational-of-fp-arith-rightshift
   (equal (fp-arith-triple->rational (fp-arith-rightshift x n))
          (fp-arith-triple->rational
           (change-fp-arith-triple x
                                   :man (ash (logtail n (fp-arith-triple->man x)) (nfix n)))))
   :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                      fp-arith-rightshift
                                      bitops::ash-is-expt-*-x)))))


(local (defthm ash-1-lte-when-logbitp
         (implies (and (logbitp n x)
                       (natp n)
                       (natp x))
                  (<= (ash 1 n) x))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions)
                  :induct (logbitp n x)
                  :expand ((logbitp n x)
                           (ash 1 n))))))

;; (defret fp-arith-rightshift-rational-nonneg-upper-bound
;;   (implies (<= 0 (fp-arith-triple->rational x))
;;            (<= (fp-arith-triple->rational new-x)
;;                (fp-arith-triple->rational x)))
;;   :hints (("Goal" :in-theory (e/d (<fn>
;;                                   fp-arith-triple->rational)
;;                                  (expt-*-logtail-bounds))
;;           :use ((:instance expt-*-logtail-bounds
;;                  (x (fp-arith-triple->man x)))))
;;          (and stable-under-simplificationp
;;               '(:nonlinearp t)))
;;   :fn fp-arith-rightshift)

;; (defret fp-arith-rightshift-rational-nonneg-upper-bound-when-roundp
;;   (implies (and (<= 0 (fp-arith-triple->rational x))
;;                 (<= 1 (nfix n))
;;                 (logbitp (+ -1 (nfix n)) (fp-arith-triple->man x)))
;;            (<= (fp-arith-triple->rational new-x)
;;                (- (fp-arith-triple->rational x)
;;                   (expt 2 (+ -1 (fp-arith-triple->exp x) n)))))
;;   :hints (("Goal" :in-theory (e/d (<fn>
;;                                   fp-arith-triple->rational)))
;;          (and stable-under-simplificationp
;;               '(:nonlinearp t)))
;;   :fn fp-arith-rightshift)

(local (defthm fp-arith-triple->exp-of-fp-arith-rightshift
         (equal (fp-arith-triple->exp (fp-arith-rightshift x n))
                (+ (fp-arith-triple->exp x) (nfix n)))
         :hints (("Goal" :in-theory (enable fp-arith-rightshift)))))



(local (defthmd ash-1-to-expt
         (implies (natp n)
                  (equal (ash 1 n)
                         (expt 2 n)))
         :hints (("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))


(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))


(defthmd compare-rationals-by-rational-sign-signif-exp
  (implies (and (rationalp x)
                (rationalp y))
           (iff (< x y)
                (b* ((xexp (rational-exponent x))
                     (xsig (rational-significand x))
                     (yexp (rational-exponent y))
                     (ysig (rational-significand y)))
                  (cond ((< 0 x)
                         (and (< 0 y)
                              (or (< xexp yexp)
                                  (and (equal xexp yexp)
                                       (< xsig ysig)))))
                        ((< y 0)
                         (and (< x 0)
                              (or (< yexp xexp)
                                  (and (equal xexp yexp)
                                       (< ysig xsig)))))
                        (t (not (and (equal x 0) (equal y 0))))))))
  :hints (("Goal" :use ((:instance acl2::rational-exponent-monotonic (x x) (y y))
                        (:instance acl2::rational-exponent-monotonic (x y) (y x))
                        (:instance acl2::rational-significand-compare-nonneg (x x) (y y))
                        (:instance acl2::rational-significand-compare-nonneg (x y) (y x))
                        (:instance acl2::rational-significand-compare-neg (x x) (y y))
                        (:instance acl2::rational-significand-compare-neg (x y) (y x)))
           :in-theory (disable acl2::rational-significand-compare-neg
                               acl2::rational-significand-compare-nonneg
                               acl2::rational-exponent-monotonic))))






(defsection normalize-arith-triple-cases

  (defret fp-arith-triple->rational-of-normalize-arith-triple-when-not-sticky
    (b* ((val (fp-arith-triple->rational new-x))
         (spec-val (fp-arith-triple->rational x)))
      (implies (case-split (not stickyp))
               (equal val
                      (- spec-val
                         (if roundp
                             (* (fp-sign-value (fp-arith-triple->sign x))
                                (expt 2 (1- (fp-arith-triple->exp new-x))))
                           0)))))
    :hints (("Goal"
             :in-theory (enable normalize-arith-triple)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-arith-triple->rational)))
            (and stable-under-simplificationp
                 '(:in-theory (enable bitops::ash-is-expt-*-x)))
            )
    :otf-flg t
    :fn normalize-arith-triple)

  (encapsulate
    nil

    (local (defthm divide-out-expt2exp
             (implies (and (rationalp x) (rationalp y))
                      (iff (< x (* (expt 2 exp) y))
                           (< (* (/ (expt 2 exp)) x) y)))))

    (local (defthm divide-out-expt2exp-2
             (implies (and (rationalp x) (rationalp y))
                      (iff (< x (* y (expt 2 exp)))
                           (< (* (/ (expt 2 exp)) x) y)))))

    (defret fp-arith-triple->rational-of-normalize-arith-triple-nonneg-when-no-round-sticky
      (b* ((val (fp-arith-triple->rational new-x))
           (spec-val (fp-arith-triple->rational x)))
        (implies (and stickyp
                      (not sticky-in)
                      (not roundp)
                      (eql (fp-arith-triple->sign x) 0))
                 (and (< val spec-val)
                      (< (+ (- (expt 2 (1- (fp-arith-triple->exp new-x))))
                            spec-val)
                         val))))
      :hints (("Goal"
               :in-theory (enable normalize-arith-triple)
               :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable fp-arith-triple->rational)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-logtail-no-round-sticky
                                      (x (fp-arith-triple->man x))
                                      (n (+ -1 (- (FP-SIZE->FRAC-SIZE SIZE))
                                            (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))))
                          :in-theory (e/d (ash-1-to-expt)
                                          (ash-of-logtail-no-round-sticky)))))
      :otf-flg t
      :rule-classes :linear
      :fn normalize-arith-triple)

    (local (defthm divide-out-expt2exp-3
             (implies (and (rationalp x) (rationalp y))
                      (iff (< (* (expt 2 exp) y) x)
                           (< y (* (/ (expt 2 exp)) x))))))

    (local (defthm divide-out-expt2exp-4
             (implies (and (rationalp x) (rationalp y))
                      (iff (< (* y (expt 2 exp)) x)
                           (< y (* (/ (expt 2 exp)) x))))))

    (defret fp-arith-triple->rational-of-normalize-arith-triple-nonneg-when-round-sticky
      (b* ((val (fp-arith-triple->rational new-x))
           (spec-val (fp-arith-triple->rational x)))
        (implies (and stickyp
                      (not sticky-in)
                      roundp
                      (eql (fp-arith-triple->sign x) 0))
                 (and (< val
                         (+ (- (expt 2 (1- (fp-arith-triple->exp new-x))))
                            spec-val))
                      (< (+ (- (expt 2 (fp-arith-triple->exp new-x)))
                            spec-val)
                         val))))
      :hints (("Goal"
               :in-theory (enable normalize-arith-triple)
               :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable fp-arith-triple->rational)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-logtail-round-sticky
                                      (x (fp-arith-triple->man x))
                                      (n (+ -1 (- (FP-SIZE->FRAC-SIZE SIZE))
                                            (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))))
                          :in-theory (e/d (ash-1-to-expt
                                           acl2::exponents-add-unrestricted)
                                          (ash-of-logtail-round-sticky)))))
      :otf-flg t
      :rule-classes :linear
      :fn normalize-arith-triple))


  (encapsulate
    nil

    (local (defthm divide-out-expt2exp
             (implies (and (rationalp x) (rationalp y))
                      (iff (< (- (* (expt 2 exp) y)) x)
                           (< (- y) (* (/ (expt 2 exp)) x))))))

    (local (defthm divide-out-expt2exp-2
             (implies (and (rationalp x) (rationalp y))
                      (iff (< (- (* y (expt 2 exp))) x)
                           (< (- y) (* (/ (expt 2 exp)) x))))))

    (defret fp-arith-triple->rational-of-normalize-arith-triple-neg-when-no-round-sticky
      (b* ((val (fp-arith-triple->rational new-x))
           (spec-val (fp-arith-triple->rational x)))
        (implies (and stickyp
                      (not sticky-in)
                      (not roundp)
                      (eql (fp-arith-triple->sign x) 1))
                 (and (< spec-val val)
                      (< val
                         (+ (expt 2 (1- (fp-arith-triple->exp new-x)))
                            spec-val)))))
      :hints (("Goal" :in-theory (enable normalize-arith-triple)
               :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable fp-arith-triple->rational)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-logtail-no-round-sticky
                                      (x (fp-arith-triple->man x))
                                      (n (+ -1 (- (FP-SIZE->FRAC-SIZE SIZE))
                                            (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))))
                          :in-theory (e/d (ash-1-to-expt)
                                          (ash-of-logtail-no-round-sticky)))))
      :otf-flg t
      :rule-classes :linear
      :fn normalize-arith-triple)


    (local (defthm divide-out-expt2exp-3
             (implies (and (rationalp x) (rationalp y))
                      (iff (< x (- (* (expt 2 exp) y)))
                           (< (* (/ (expt 2 exp)) x) (- y))))))

    (local (defthm divide-out-expt2exp-4
             (implies (and (rationalp x) (rationalp y))
                      (iff (< x (- (* y (expt 2 exp))))
                           (< (* (/ (expt 2 exp)) x) (- y))))))



    (defret fp-arith-triple->rational-of-normalize-arith-triple-neg-when-round-sticky
      (b* ((val (fp-arith-triple->rational new-x))
           (spec-val (fp-arith-triple->rational x)))
        (implies (and stickyp
                      (not sticky-in)
                      roundp
                      (eql (fp-arith-triple->sign x) 1))
                 (and (< (+ (expt 2 (1- (fp-arith-triple->exp new-x)))
                            spec-val)
                         val)
                      (< val
                         (+ (expt 2 (fp-arith-triple->exp new-x))
                            spec-val)))))
      :hints (("Goal" :in-theory (enable normalize-arith-triple)
               :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable fp-arith-triple->rational)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-logtail-round-sticky
                                      (x (fp-arith-triple->man x))
                                      (n (+ -1 (- (FP-SIZE->FRAC-SIZE SIZE))
                                            (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))))
                          :in-theory (e/d (ash-1-to-expt
                                           acl2::exponents-add-unrestricted)
                                          (ash-of-logtail-round-sticky)))))
      :otf-flg t
      :rule-classes ((:linear :trigger-terms ((fp-arith-triple->rational new-x))))
      :fn normalize-arith-triple))

  (defret rational-exponent-of-normalize-arith-triple
    (equal (rational-exponent
            (fp-arith-triple->rational new-x))
           (rational-exponent
            (fp-arith-triple->rational x)))
    :hints (("Goal" :in-theory (enable rational-sign-significand-exponent-of-fp-arith-triple->rational
                                       normalize-arith-triple)
             :cases ((equal (fp-arith-triple->man x) 0))))
    :fn normalize-arith-triple)

  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (local (include-book "centaur/misc/multiply-out" :dir :system))

  (local (defthm denominator-/-integer
           (implies (and (integerp x)
                         (not (equal 0 x)))
                    (equal (denominator (/ x))
                           (abs x)))
           :hints (("Goal" :use ((:instance rational-implies2
                                            (x (/ x)))
                                 (:instance lowest-terms
                                            (x (/ x)) (n (denominator x))
                                            (r (if (< x 0) -1 1)) (q x)))
                    :in-theory (disable rational-implies2
                                        acl2::equal-*-/-1
                                        acl2::*-r-denominator-r)))
           :otf-flg t))

  (local (in-theory (disable acl2::multiply-out-<
                             acl2::<-unary-/-positive-right)))

  (defret normalize-arith-triple-exact-in-terms-of-rational
    (implies (and (integerp (* (expt 2 (fp-size->frac-size size))
                               (rational-significand (fp-arith-triple->rational x))))
                  (not sticky-in))
             (and (not roundp)
                  (not stickyp)
                  (equal (fp-arith-triple->rational new-x)
                         (fp-arith-triple->rational x))))
    :hints (("Goal" :in-theory (e/d (normalize-arith-triple
                                     loghead
                                     logbitp
                                     oddp evenp)
                                    (acl2::exponents-add
                                     acl2::expt-minus))
             :cases ((equal 0 (fp-arith-triple->man x))))
            (and stable-under-simplificationp
                 '(:in-theory (enable
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               acl2::exponents-add-unrestricted)))
            )
    :fn normalize-arith-triple)


  ;; (defthm normalize-arith-triple-monotonic
  ;;   (implies (<= (fp-arith-triple->rational a1)
  ;;                (fp-arith-triple->rational a2))
  ;;            (b* (((mv x1 round1 sticky1) (normalize-arith-triple a1))
  ;;                 ((mv x2 round2 sticky2) (normalize-arith-triple a2 :verbosep verbp2)))
  ;;              (and (<= (fp-arith-triple->rational x2) (fp-arith-triple->rational x1))
  ;;                   (implies (equal (fp-arith-triple->rational x2) (fp-arith-triple->rational x1))
  ;;                            (and (implies (and (<= 0 (fp-arith-triple->rational a1))
  ;;                                               round1)
  ;;                                          round2)
  ;;                                 (implies (and (<= (fp-arith-triple->rational a2) 0)
  ;;                                               round2)
  ;;                                          round1)))
  ;;                   (implies (and (equal (fp-arith-triple->rational x2) (fp-arith-triple->rational x1))
  ;;                                 (equal round1 round2))
  ;;                            (and (implies (and (<= 0 (fp-arith-triple->rational a1))
  ;;                                               sticky1)
  ;;                                          sticky2)
  ;;                                 (implies (and (<= (fp-arith-triple->rational a2) 0)
  ;;                                               sticky2)
  ;;                                          sticky1))))))
  ;;   :hints (("Goal" :in-theory (enable normalize-arith-triple
  ;;                                     fp-arith-triple->rational
  ;;                                     fp-arith-rightshift
  ;;                                     fp-arith-leftshift
  ;;                                     fp-sign-value-redef)
  ;;           :do-not-induct t))
  ;;   :otf-flg t)





  ;; (defret normalize-arith-triple-gte-exact
  ;;   (implies (and (integerp (* (expt 2 (fp-size->frac-size size))
  ;;                              (rational-significand r)))
  ;;                 (<= r (fp-arith-triple->rational x)))
  ;;            (<= r (fp-arith-triple->rational new-x)))
  ;;   :hints (("Goal" :in-theory (e/d (normalize-arith-triple
  ;;                                   fp-arith-triple->rational
  ;;                                   ;; fp-arith-rightshift
  ;;                                   fp-arith-leftshift))
  ;;           :cases ((equal 0 (fp-arith-triple->man x))
  ;;                   (< 0 (fp-arith-triple->rational x))
  ;;                   (> 0 (fp-arith-triple->rational x))))
  ;;          )
  ;;   :rule-classes :linear
  ;;   :fn normalize-arith-triple
  ;;   :otf-flg t)
  )



(defsection round-arith-triple-bounds
  (local (in-theory (disable logmask)))

  (local (defthmd +-1-logcons-1
           (equal (+ 1 (logcons 1 x))
                  (logcons 0 (+ 1 (ifix x))))
           :hints (("Goal" :in-theory (enable logcons)))))

  (local (defthm logmask+1
           (equal (+ 1 (logmask n))
                  (ash 1 (nfix n)))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               +-1-logcons-1)
                    :induct (logmask n)
                    :expand ((logmask n)
                             (ash 1 n))))))

  (local (defthm integer-length-of-plus-1
           (implies (natp x)
                    (equal (integer-length (+ 1 x))
                           (+ (if (equal x (logmask (integer-length x))) 1 0)
                              (integer-length x))))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions)
                    :induct (integer-length x)
                    :expand ((integer-length x)
                             (integer-length (+ 1 x))
                             (:free (x) (logmask (+ 1 x))))))))

  (define my-round-arith-triple ((x fp-arith-triple-p)
                                 (roundp booleanp)
                                 (stickyp booleanp)
                                 (rc fp-rc-p)
                                 &key ((size fp-size-p) 'size))
    :returns (new-x fp-arith-triple-p)
    (b* (((fp-size size))
         ((fp-arith-triple x))
         (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc))
         ((unless round-up?)
          (fp-arith-triple-fix x))
         ((when (eql x.man (logmask (+ 1 size.frac-size))))
          (change-fp-arith-triple x :exp (+ 1 x.exp) :man (ash 1 size.frac-size))))
      (change-fp-arith-triple x :man (+ 1 x.man)))
    ///
    (local (defthm distrib2
             (equal (* (+ x y) z)
                    (+ (* x z) (* y z)))))

    (defret fp-arith-triple->rational-of-my-round-arith-triple
      (equal (fp-arith-triple->rational new-x)
             (b* (((fp-arith-triple x))
                  (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc)))
               (+ (fp-arith-triple->rational x)
                  (if round-up?
                      (* (fp-sign-value x.sign)
                         (expt 2 x.exp))
                    0))))
      :hints (("Goal" :in-theory (enable fp-arith-triple->rational))
              (and stable-under-simplificationp
                   '(:in-theory (enable logmask
                                        ash-1-to-expt
                                        acl2::exponents-add-unrestricted))))))

  (local (defthm round-up-of-no-round-sticky
           (equal (round-up sign l nil nil rc) nil)
           :hints (("Goal" :in-theory (enable round-up)))))

  (defretd round-arith-triple-of-normalize
    :pre-bind (((mv x roundp stickyp1) (normalize-arith-triple in :verbosep verbp)))
    (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
              (equal stickyp stickyp1))
             (equal new-x
                    (my-round-arith-triple x roundp stickyp rc)))
    :hints (("Goal"
             :in-theory (enable round-arith-triple
                                my-round-arith-triple)
             :cases ((equal (fp-arith-triple->man in) 0)))
            (and stable-under-simplificationp
                 '(:expand ((:free (sign exp man verbosep)
                                   (normalize-arith-triple
                                    (fp-arith-triple sign exp man))))
                           :in-theory (enable fp-arith-rightshift))))
    :fn round-arith-triple)

  (defretd fp-arith-triple->rational-of-round
    :pre-bind (((mv x roundp1 stickyp1) (normalize-arith-triple in :verbosep verbp)))
    (implies (and (equal roundp roundp1)
                  (equal stickyp stickyp1))
             (equal (fp-arith-triple->rational new-x)
                    (b* (((fp-arith-triple x))
                         (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc)))
                      (+ (fp-arith-triple->rational x)
                         (if round-up?
                             (* (fp-sign-value x.sign)
                                (expt 2 x.exp))
                           0)))))
    :hints (("Goal" :in-theory (e/d (round-arith-triple-of-normalize)
                                    (my-round-arith-triple))))
    :fn round-arith-triple)


  (local (in-theory (enable round-arith-triple-of-normalize)))
  (local (in-theory (disable normalize-arith-triple.exp-value)))

  (local (defthm plus-minus-times
           (implies (syntaxp (and (Quotep c1) (quotep c2)))
                    (equal (+ (- (* c1 x)) (* c2 x))
                           (* (- c2 c1) x)))))

  ;; Focus on RNE since we need this for most
  (local (defretd exp-of-round-arith-triple
           :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
           (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
                     (not (equal (fp-arith-triple->exp new-x)
                                 (fp-arith-triple->exp x))))
                    (equal (fp-arith-triple->exp new-x)
                           (+ 1 (fp-arith-triple->exp x))))
           :hints (("Goal" :in-theory (enable my-round-arith-triple)))
           :fn round-arith-triple))

  (defret round-arith-triple-of-normalize-exact
    :pre-bind (((mv x & &) (normalize-arith-triple in :verbosep verbp))
               (roundp nil)
               (stickyp nil))
    (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
              (integerp (* (expt 2 (fp-size->frac-size size))
                           (rational-significand (fp-arith-triple->rational in)))))
             (equal (fp-arith-triple->rational new-x)
                    (fp-arith-triple->rational in)))
    :hints (("Goal" :in-theory (e/d (my-round-arith-triple)
                                    (round-arith-triple-of-normalize))
             :use ((:instance round-arith-triple-of-normalize (stickyp nil)))))
    :fn round-arith-triple)

  ;; (defret round-arith-triple-of-normalize-gte-exact
  ;;   :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
  ;;   (implies (and (integerp (* (expt 2 frac-size)
  ;;                              (rational-significand r)))
  ;;                 (rationalp r)
  ;;                 (<= r (+ (fp-arith-triple->rational in))))
  ;;            (<= r (fp-arith-triple->rational new-x)))
  ;;   :hints (("Goal" :in-theory (e/d (my-round-arith-triple
  ;;                                   round-arith-triple-of-normalize
  ;;                                   round-up)
  ;;                                  ())))
  ;;   :fn round-arith-triple
  ;;   :rule-classes nil)

  (defret round-arith-triple-bounds-in-terms-of-norm-exp-when-rne
    :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
    (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
              (eq (rc->rounding-mode rc) :rne))
             (b* (((fp-arith-triple x))
                  ((fp-size size))
                  (val (fp-arith-triple->rational new-x)))
               (and (<= (+ (- (expt 2 (+ -1 x.exp)))
                           (fp-arith-triple->rational in))
                        val)
                    (<= val
                        (+ (expt 2 (+ -1 x.exp))
                           (fp-arith-triple->rational in))))))
    :hints (("Goal" :in-theory (enable round-up))
            (and stable-under-simplificationp
                 '(:cases ((equal (fp-arith-triple->sign in) 0))
                          :in-theory (enable acl2::exponents-add-unrestricted)))
            (and stable-under-simplificationp
                 (b* ((neg (member-equal '(not (equal (fp-arith-triple->sign$inline in) '1)) clause))
                      (roundp (member-equal '(not (MV-NTH '1 (NORMALIZE-ARITH-TRIPLE-FN IN SIZE 'NIL 'NIL))) clause))
                      (stickyp (member-equal '(not (MV-NTH '2 (NORMALIZE-ARITH-TRIPLE-FN IN SIZE 'NIL 'NIL))) clause))
                      (rule
                       (if neg
                           (if roundp
                               'fp-arith-triple->rational-of-normalize-arith-triple-neg-when-round-sticky
                             'fp-arith-triple->rational-of-normalize-arith-triple-neg-when-no-round-sticky)
                         (if roundp
                             'fp-arith-triple->rational-of-normalize-arith-triple-nonneg-when-round-sticky
                           'fp-arith-triple->rational-of-normalize-arith-triple-nonneg-when-no-round-sticky)))
                      (hint
                       (if stickyp
                           `(:use ((:instance ,rule (x in) (sticky-in nil) (verbosep nil)))
                                  :in-theory (e/d (acl2::exponents-add-unrestricted)
                                                  (,rule)))
                         '(:in-theory (enable normalize-arith-triple.exp-value
                                              acl2::exponents-add-unrestricted)))))
                   ;; (cw "hint: ~x0~%" hint)
                   hint)))

    :fn round-arith-triple)

  (local (defret normalize-arith-triple-nonzero
           (implies (not (equal (fp-arith-triple->man x) 0))
                    (not (equal (fp-arith-triple->man new-x) 0)))
           :hints (("Goal" :in-theory (enable normalize-arith-triple
                                              fp-arith-rightshift
                                              fp-arith-leftshift)))
           :fn normalize-arith-triple))


  (defret round-arith-triple-bounds-in-terms-of-input-rational-exponent-when-rne
    :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
    (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
              (eq (rc->rounding-mode rc) :rne))
             (b* (((fp-arith-triple x))
                  ((fp-size size))
                  (val (fp-arith-triple->rational new-x))
                  (exp (- (rational-exponent (fp-arith-triple->rational in))
                          (+ 1 size.frac-size))))
               (and (<= (+ (- (expt 2 exp))
                           (fp-arith-triple->rational in))
                        val)
                    (<= val
                        (+ (expt 2 exp)
                           (fp-arith-triple->rational in))))))
    :hints (("Goal" :use (round-arith-triple-bounds-in-terms-of-norm-exp-when-rne)
             :in-theory (e/d (rational-sign-significand-exponent-of-fp-arith-triple->rational
                              NORMALIZE-ARITH-TRIPLE.EXP-VALUE)
                             (rational-exponent-of-normalize-arith-triple
                              round-arith-triple-bounds-in-terms-of-norm-exp-when-rne))))
    :rule-classes ((:linear :trigger-terms
                            ((fp-arith-triple->rational
                              (mv-nth 0 (round-arith-triple
                                         (mv-nth 0 (normalize-arith-triple in))
                                         (mv-nth 1 (normalize-arith-triple in))
                                         (mv-nth 2 (normalize-arith-triple in))
                                         rc))))))
    :fn round-arith-triple)

  (defret round-arith-triple-bounds-in-terms-of-final-exponent-when-rne
    :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
    (implies (and ;; (not (equal (fp-arith-triple->man in) 0))
              (eq (rc->rounding-mode rc) :rne))
             (b* (((fp-arith-triple new-x))
                  ((fp-size size))
                  (val (fp-arith-triple->rational new-x)))
               (and (<= (+ (- (expt 2 (+ -1 new-x.exp)))
                           (fp-arith-triple->rational in))
                        val)
                    (<= val
                        (+ (expt 2 (+ -1 new-x.exp))
                           (fp-arith-triple->rational in))))))
    :hints (("Goal" :use ((:instance exp-of-round-arith-triple)
                          (:instance round-arith-triple-bounds-in-terms-of-norm-exp-when-rne))
             :in-theory (e/d (acl2::exponents-add-unrestricted)
                             (exp-of-round-arith-triple
                              round-arith-triple-bounds-in-terms-of-norm-exp-when-rne
                              round-arith-triple-of-normalize))))
    :rule-classes ((:linear :trigger-terms
                            ((fp-arith-triple->rational
                              (mv-nth 0 (round-arith-triple
                                         (mv-nth 0 (normalize-arith-triple in))
                                         (mv-nth 1 (normalize-arith-triple in))
                                         (mv-nth 2 (normalize-arith-triple in))
                                         rc))))))
    :fn round-arith-triple)

  (defret integer-length-of-normalize-round-arith-triple
    :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in)))
    (implies (not (equal (fp-arith-triple->man in) 0))
             (equal (integer-length (fp-arith-triple->man new-x))
                    (+ 1 (fp-size->frac-size size))))
    :hints (("Goal" :in-theory (enable my-round-arith-triple)))
    :fn round-arith-triple))


(define round-arith-triple-ulp-error ((in fp-arith-triple-p)
                                      (rc fp-rc-p)
                                      &key ((size fp-size-p) 'size))
  :returns (error rationalp :rule-classes :type-prescription)
  :prepwork ((local (include-book "centaur/misc/multiply-out" :dir :system)))
  (b* (((mv norm roundp stickyp) (normalize-arith-triple in :verbosep nil))
       ((mv round & &) (round-arith-triple norm roundp stickyp rc :verbosep nil))
       ((fp-size size))
       (in-val (fp-arith-triple->rational in))
       (round-val (fp-arith-triple->rational round))
       (ulp (expt 2 (- (rational-exponent in-val) size.frac-size))))
    (/ (- round-val in-val) ulp))
  ///
  (local (in-theory (disable ACL2::/R-WHEN-ABS-NUMERATOR=1)))
  (local (include-book "centaur/misc/multiply-out" :dir :system))

  (defret <fn>-bounds-when-rne
    (implies (eq (rc->rounding-mode rc) :rne)
             (and (<= -1/2 error)
                  (<= error 1/2)))
    :hints (("Goal"
             :use ((:instance round-arith-triple-bounds-in-terms-of-input-rational-exponent-when-rne
                              (verbosep nil)))
             :in-theory (e/d (acl2::exponents-add-unrestricted)
                             (round-arith-triple-bounds-in-terms-of-input-rational-exponent-when-rne)))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
    :rule-classes :linear)

  (defretd round-arith-triple-in-terms-of-ulp-error
    (b* (((mv norm roundp stickyp) (normalize-arith-triple in))
         ((mv round & &) (round-arith-triple norm roundp1 stickyp1 rc :verbosep verbp))
         ((fp-size size))
         (in-val (fp-arith-triple->rational in))
         (round-val (fp-arith-triple->rational round))
         (ulp (expt 2 (- (rational-exponent in-val) size.frac-size))))
      (implies (and (equal roundp1 roundp)
                    (equal stickyp1 stickyp))
               (equal round-val (+ in-val (* error ulp)))))
    :hints (("Goal" :in-theory (enable round-arith-triple-normalize-verbosep)))))


(encapsulate
  nil

  (local (defthmd equal-integer-length-of-positive-by-ash
           (implies (and (syntaxp (quotep n))
                         (posp n)
                         (natp x))
                    (iff (equal (integer-length x) n)
                         (and (<= (ash 1 (1- n)) x)
                              (< x (ash 1 n)))))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs
                                               bitops::logcons->-n-strong
                                               bitops::logcons-<-n-strong)
                    :induct (loghead n x)))))

  (defthmd equal-integer-length-of-positive
    (implies (and ;; (syntaxp (quotep n))
              (posp n)
              (natp x))
             (iff (equal (integer-length x) n)
                  (and (<= (expt 2 (1- n)) x)
                       (<= x (+ -1 (expt 2 n))))))
    :hints (("Goal" :use equal-integer-length-of-positive-by-ash
             :in-theory (enable bitops::ash-is-expt-*-x)))))


(defsection left-normalize-arith-triple
  (local (std::set-define-current-function left-normalize-arith-triple))

  (local (defthmd unsigned-byte-p-of-integer-length
           (implies (natp x)
                    (unsigned-byte-p (integer-length x) x))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (defret bounds-of-<fn>
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (implies (and (not (equal x.man 0))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man))
               (and (<= (expt 2 (pos-fix frac-size)) new-x.man)
                    (<= new-x.man (+ -1 (expt 2 (+ 1 (pos-fix frac-size))))))))
    :hints (("Goal" :use man-length-of-<fn>
             :in-theory (e/d (equal-integer-length-of-positive)
                             (man-length-of-<fn> <fn>))))
    :rule-classes :linear))


(define normalize-arith-triple-round+sticky ((x fp-arith-triple-p)
                                             (frac-size posp))
  :returns (round+sticky rationalp :rule-classes :type-prescription)
  :prepwork
  ((local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
   (local (include-book "centaur/misc/multiply-out" :dir :system)))
  (b* (((fp-arith-triple x))
       ((when (eql x.man 0)) 0)
       (man-len (integer-length x.man))
       (shiftcnt (- man-len (+ 1 (lposfix frac-size))))
       ((unless (< 0 shiftcnt)) 0))
    (/ (loghead shiftcnt x.man) (expt 2 (1- shiftcnt))))
  ///
  (local (in-theory (disable ACL2::/R-WHEN-ABS-NUMERATOR=1)))
  (local (defthmd decompose-as-logapp
           (equal (logapp w x (logtail w x))
                  (ifix x))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthmd decompose2
           (equal (logapp w x (logapp 1 (logbit w x) (logtail (+ 1 (nfix w)) x)))
                  (ifix x))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logapp-when-loghead-equal-0
           (implies (equal 0 (loghead w x))
                    (equal (logapp w x y)
                           (ash y (nfix w))))
           :hints ((bitops::logbitp-reasoning))))

  ;; (local (defretd stickypart-size-lemma
  ;;          (b* (((fp-arith-triple x)))
  ;;            (implies (<= 0 (- (integer-length x.man) (+ 2 (pos-fix frac-size))))
  ;;                     (unsigned-byte-p (- (integer-length x.man) (+ 2 (pos-fix frac-size)))
  ;;                                      sticky)))))

  ;; (defret <fn>-width
  ;;   (b* (((fp-arith-triple x)))
  ;;     (implies (and (<= (- (integer-length x.man) (+ 2 (pos-fix frac-size))) n)
  ;;                   (natp n))
  ;;              (unsigned-byte-p n sticky)))
  ;;   :hints (("Goal" :use ((:instance stickypart-size-lemma))
  ;;            :in-theory (disable <fn>))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable <fn>)))))

  (defret <fn>-lower-bound
    (<= 0 round+sticky)
    :rule-classes (:linear :type-prescription))

  (defret <fn>-upper-bound
    (< round+sticky 2)
    :hints (("Goal" :use ((:instance unsigned-byte-p-of-loghead
                                     (size (+ -1 (- (POS-FIX FRAC-SIZE))
                                              (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                                     (size1 (+ -1 (- (POS-FIX FRAC-SIZE))
                                               (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                                     (i (fp-arith-triple->man x))))
             :in-theory (e/d (unsigned-byte-p
                              acl2::exponents-add-unrestricted)
                             (unsigned-byte-p-of-loghead
                              acl2::loghead-upper-bound))))
    :rule-classes :linear)

  (defretd integer-bits-of-<fn>
    (b* (((fp-arith-triple x)))
      (and (integerp (* (expt 2 (- (integer-length x.man) (+ 2 (pos-fix frac-size)))) round+sticky))
           (implies (<= 0 (- (integer-length x.man) (+ 1 (pos-fix frac-size))))
                    (unsigned-byte-p (- (integer-length x.man) (+ 1 (pos-fix frac-size)))
                                     (* (expt 2 (- (integer-length x.man) (+ 2 (pos-fix frac-size)))) round+sticky))))))

  (defthmd normalize-round+sticky-logapp-decomp
    (b* (((mv (fp-arith-triple norm) & &)
          (normalize-arith-triple x))
         ((fp-arith-triple x))
         ((fp-size size))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (implies (<= (+ 2 size.frac-size) (integer-length x.man))
               (equal (logapp (- (integer-length x.man) (+ 1 size.frac-size))
                              (* (expt 2 (- (integer-length x.man) (+ 2 size.frac-size))) round+sticky)
                              norm.man)
                      x.man)))
    :hints (("Goal" :use ((:instance decompose-as-logapp
                                     (x (fp-arith-triple->man x))
                                     (w (- (integer-length (fp-arith-triple->man x))
                                           (+ 1 (fp-size->frac-size size))))))
             :in-theory (enable normalize-arith-triple
                                fp-arith-rightshift
                                fp-arith-leftshift))))

  (defthmd normalize-round+sticky-decomp
    (b* (((mv (fp-arith-triple norm) & &)
          (normalize-arith-triple x))
         ((fp-arith-triple x))
         ((fp-size size))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (equal norm.man
             (* (expt 2 (- (- (integer-length x.man) (+ 1 size.frac-size))))
                (+ x.man
                   (- (* (expt 2 (- (integer-length x.man) (+ 2 size.frac-size))) round+sticky))))))
    :hints (("Goal"
             :use ((:instance normalize-round+sticky-logapp-decomp)
                   (:instance integer-bits-of-normalize-arith-triple-round+sticky
                              (frac-size (fp-size->frac-size size))))
             :cases ((<= (+ 2 (fp-size->frac-size size))
                         (integer-length (fp-arith-triple->man x))))
             :in-theory (enable logapp))
            (and stable-under-simplificationp
                 '(:in-theory (enable normalize-arith-triple
                                      fp-arith-leftshift
                                      normalize-arith-triple-round+sticky)))
            (and stable-under-simplificationp
                 '(:in-theory (enable bitops::ash-is-expt-*-x
                                      acl2::exponents-add-unrestricted)))))


  (defthmd normalize-round+sticky-value-decomp
    (b* (((mv (fp-arith-triple norm) & &)
          (normalize-arith-triple x))
         ((fp-arith-triple x))
         ((fp-size size))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (equal (fp-arith-triple->rational x)
             (* (fp-sign-value x.sign)
                (* (expt 2 (+ x.exp (- (integer-length x.man) (+ 2 size.frac-size))))
                   (+ round+sticky (* 2 norm.man))))))
    :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                       normalize-round+sticky-decomp
                                       acl2::exponents-add-unrestricted))))



  (local (defthmd loghead-in-terms-of-loghead-of-one-less
           (implies (posp n)
                    (equal (loghead n x)
                           (+ (ash (logbit (1- n) x) (1- n))
                              (loghead (1- n) x))))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions)
                    :induct t
                    :expand ((loghead n x)
                             (loghead (+ -1 n) x)
                             (logbitp 0 x)
                             (:free (x) (ash x (+ -1 n)))
                             (logbitp (+ -1 n) x))))))

  (local (defthmd expand-this-loghead
           (b* ((n (+ -1 (- (fp-size->frac-size size))
                      (integer-length (fp-arith-triple->man x))))
                (x (fp-arith-triple->man x)))
             (implies (posp n)
                      (equal (loghead n x)
                             (+ (ash (logbit (1- n) x) (1- n))
                                (loghead (1- n) x)))))
           :hints (("Goal" :use ((:instance loghead-in-terms-of-loghead-of-one-less
                                            (n (+ -1 (- (fp-size->frac-size size))
                                                  (integer-length (fp-arith-triple->man x))))
                                            (x (fp-arith-triple->man x))))))))


  (local (defthm integerp-of-plus-integer
           (implies (and (rationalp x)
                         (integerp y))
                    (equal (integerp (+ y x))
                           (integerp x)))
           :hints (("Goal" :cases ((integerp x))))))

  (local (defthmd integerp-of-loghead-divided
           (implies (not (equal (loghead n x) 0))
                    (not (integerp (* (expt 2 (- n)) (loghead n x)))))
           :hints (("Goal"
                    :use ((:instance acl2::loghead-upper-bound
                                     (size n) (i x)))
                    :in-theory (disable acl2::loghead-upper-bound))
                   '(:cases ((and (< 0 (* (expt 2 (- n)) (loghead n x)))
                                  (< (* (expt 2 (- n)) (loghead n x)) 1)))))))

  (defthmd normalize-in-terms-of-round+sticky
    (b* (((mv & roundp stickyp) (normalize-arith-triple x :sticky-in sticky-in))
         ((fp-size size))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (and (equal roundp
                  (<= 1 round+sticky))
           (equal stickyp
                  (or (and sticky-in t)
                      (not (integerp round+sticky))))))
    :hints (("Goal" :in-theory (enable normalize-arith-triple))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (expand-this-loghead
                                    bitops::ash-is-expt-*-x)
                                   (acl2::loghead-upper-bound))
                              :use ((:instance integerp-of-loghead-divided
                                               (n (+ -2 (- (FP-SIZE->FRAC-SIZE SIZE))
                                                     (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                                               (x (fp-arith-triple->man x)))
                                    (:instance acl2::loghead-upper-bound
                                               (size (+ -2 (- (FP-SIZE->FRAC-SIZE SIZE))
                                                        (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                                               (i (fp-arith-triple->man x)))))))
    :otf-flg t)

  (local
   (defthm normalize-round+sticky-value-decomp-here
     (b* (((mv (fp-arith-triple norm) & &)
           (normalize-arith-triple x))
          ((fp-arith-triple x))
          ((fp-size size))
          (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
       (implies (syntaxp (equal x 'x))
                (equal (fp-arith-triple->rational x)
                       (* (fp-sign-value x.sign)
                          (* (expt 2 (+ x.exp (- (integer-length x.man) (+ 2 size.frac-size))))
                             (+ round+sticky (* 2 norm.man)))))))
     :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                        normalize-round+sticky-decomp
                                        acl2::exponents-add-unrestricted)))))

  (defthmd normalize-arith-triple-round+sticky-when-0
    (implies (equal (fp-arith-triple->man x) 0)
             (equal (normalize-arith-triple-round+sticky x frac-size) 0))
    :hints (("Goal" :in-theory (enable normalize-arith-triple-round+sticky))))

  ;; (local (defthm integer-length-of-plus-one
  ;;          (implies (natp x)
  ;;                   (<= (integer-length x) (integer-length (+ 1 x))))
  ;;          :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
  ;;                                             bitops::ihsext-recursive-redefs)))
  ;;          :rule-classes ((:linear :trigger-terms ((integer-length (+ 1 x)))))))

  (defthmd round-nearest-in-terms-of-round+sticky
    (b* (((mv (fp-arith-triple norm) roundp1 stickyp1) (normalize-arith-triple x :verbosep verbosep1))
         ((mv new-x & &) (round-arith-triple norm roundp stickyp rc))
         ((fp-size size))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (implies (and (equal roundp roundp1)
                    (equal stickyp stickyp1)
                    (equal (rc->rounding-mode rc) :rne))
               (and (implies (case-split (< 1 round+sticky))
                             (equal (fp-arith-triple->rational new-x)
                                    (fp-arith-triple->rational
                                     (change-fp-arith-triple norm :man (+ 1 norm.man)))))
                    (implies (case-split (< round+sticky 1))
                             (equal (fp-arith-triple->rational new-x)
                                    (fp-arith-triple->rational norm))))))
    :hints (("Goal" :in-theory (e/d (normalize-in-terms-of-round+sticky
                                     normalize-arith-triple-round+sticky-when-0
                                     round-up
                                     fp-arith-triple->rational-of-round
                                     acl2::exponents-add-unrestricted)
                                    (normalize-arith-triple-round+sticky
                                     logmask
                                     fp-arith-triple->rational-of-normalize-arith-triple-when-not-sticky)))
            (and stable-under-simplificationp
                 '(:expand ((:free (sign exp man) (fp-arith-triple->rational (fp-arith-triple sign exp man)))
                            (fp-arith-triple->rational (mv-nth 0 (normalize-arith-triple x :verbosep nil)))))))
    :otf-flg t)

  (defthmd round-in-terms-of-round+sticky
    (b* (((mv (fp-arith-triple norm) roundp1 stickyp1) (normalize-arith-triple x :verbosep verbosep1))
         ((mv new-x & &) (round-arith-triple norm roundp stickyp rc))
         ((fp-size size))
         (xval (fp-arith-triple->rational x))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (implies (and (equal roundp roundp1)
                    (equal stickyp stickyp1))
               (equal (fp-arith-triple->rational new-x)
                      (fp-arith-triple->rational
                       (if (case (rc->rounding-mode rc)
                             (:rne (b* ((l (logbitp 0 norm.man)))
                                     (or (< 1 round+sticky)
                                         (and l (<= 1 round+sticky)))))
                             (:rmi (and (< xval 0) (< 0 round+sticky)))
                             (:ri (and (< 0 xval) (< 0 round+sticky)))
                             (t nil))
                           (change-fp-arith-triple norm :man (+ 1 norm.man))
                         norm)))))
    :hints (("Goal" :in-theory (e/d (normalize-in-terms-of-round+sticky
                                     normalize-arith-triple-round+sticky-when-0
                                     round-up
                                     fp-arith-triple->rational-of-round
                                     acl2::exponents-add-unrestricted)
                                    (normalize-arith-triple-round+sticky
                                     logmask
                                     fp-arith-triple->rational-of-normalize-arith-triple-when-not-sticky)))
            (and stable-under-simplificationp
                 '(:expand ((:free (sign exp man) (fp-arith-triple->rational (fp-arith-triple sign exp man)))
                            (fp-arith-triple->rational (mv-nth 0 (normalize-arith-triple x :verbosep nil)))))))
    :otf-flg t)

  (defthmd round-in-terms-of-round+sticky2
    (b* (((mv (fp-arith-triple norm) roundp1 stickyp1) (normalize-arith-triple x :verbosep verbosep1))
         ((mv new-x & &) (round-arith-triple norm roundp stickyp rc))
         ((fp-size size))
         (xval (fp-arith-triple->rational x))
         (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
      (implies (and (equal roundp roundp1)
                    (equal stickyp stickyp1))
               (equal (fp-arith-triple->rational new-x)
                      (+ (fp-arith-triple->rational x)
                         (* (fp-sign-value (fp-arith-triple->sign x))
                            (expt 2 (+ -2
                                       (fp-arith-triple->exp x)
                                       (integer-length (fp-arith-triple->man x))
                                       (- size.frac-size)))
                            (if (case (rc->rounding-mode rc)
                                  (:rne (b* ((l (logbitp 0 norm.man)))
                                          (or (< 1 round+sticky)
                                              (and l (<= 1 round+sticky)))))
                                  (:rmi (and (< xval 0) (< 0 round+sticky)))
                                  (:ri (and (< 0 xval) (< 0 round+sticky)))
                                  (t nil))
                                (- 2 round+sticky)
                              (- round+sticky)))))))
    :hints (("Goal" :in-theory (e/d (normalize-in-terms-of-round+sticky
                                     normalize-arith-triple-round+sticky-when-0
                                     round-up
                                     fp-arith-triple->rational-of-round
                                     acl2::exponents-add-unrestricted)
                                    (normalize-arith-triple-round+sticky
                                     logmask
                                     fp-arith-triple->rational-of-normalize-arith-triple-when-not-sticky)))
            (and stable-under-simplificationp
                 '(:expand ((:free (sign exp man) (fp-arith-triple->rational (fp-arith-triple sign exp man)))
                            (fp-arith-triple->rational (mv-nth 0 (normalize-arith-triple x :verbosep nil))))))
            (and stable-under-simplificationp
                 ;; just to deal with the case where mant = 0
                 '(:in-theory (enable normalize-arith-triple))))
    :otf-flg t))









(defret integer-length-of-normalize-arith-triple
  (implies (not (equal 0 (fp-arith-triple->man x)))
           (equal (integer-length (fp-arith-triple->man new-x))
                  (+ 1 (fp-size->frac-size size))))
  :hints (("Goal" :in-theory (enable normalize-arith-triple
                                     fp-arith-rightshift
                                     fp-arith-leftshift)))
  :fn normalize-arith-triple)

(defret normalize-arith-triple-bounds
  (implies (not (equal 0 (fp-arith-triple->man x)))
           (and (<= (expt 2 (fp-size->frac-size size))
                    (fp-arith-triple->man new-x))
                (<= (fp-arith-triple->man new-x)
                    (1- (* 2 (expt 2 (fp-size->frac-size size)))))))
  :hints (("Goal"
           :use integer-length-of-normalize-arith-triple
           :in-theory (enable equal-integer-length-of-positive)))
  :fn normalize-arith-triple
  :rule-classes :linear)


(define fp-arith-triple->rational-and-sign-equiv ((x fp-arith-triple-p)
                                                  (y fp-arith-triple-p))
  (and (equal (fp-arith-triple->sign x)
              (fp-arith-triple->sign y))
       (equal (fp-arith-triple->rational x)
              (fp-arith-triple->rational y)))
  ///
  (defequiv fp-arith-triple->rational-and-sign-equiv)

  (defcong fp-arith-triple->rational-and-sign-equiv equal (fp-arith-triple->rational x) 1)
  (defcong fp-arith-triple->rational-and-sign-equiv equal (fp-arith-triple->sign x) 1)

  (defthm left-normalize-under-fp-arith-triple->rational-and-sign-equiv
    (fp-arith-triple->rational-and-sign-equiv
     (left-normalize-arith-triple x frac-size)
     x)
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable left-normalize-arith-triple))))))



(defsection normalize-arith-triple-canonical
  ;; (local (defthmd integer-length-is-rational-exponent
  ;;          (implies (posp x)
  ;;                   (equal (integer-length x)
  ;;                          (rational-exponent (ifix x))))

  (local (defthm fp-arith-triple->rational-equals-0
           (equal (equal 0 (fp-arith-triple->rational x))
                  (equal 0 (fp-arith-triple->man x)))
           :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

  (local (defthm floor-divide-out
           (implies (and (not (equal (rfix y) 0))
                         (syntaxp (not (equal y ''1)))
                         (rationalp x))
                    (equal (floor x y)
                           (floor (/ x y) 1)))
           :hints (("Goal" :in-theory (enable rfix)))))

  (local (in-theory (disable ACL2::/R-WHEN-ABS-NUMERATOR=1)))

  (defthmd normalize-arith-triple-in-terms-of-rational
    (b* (((mv norm ?roundp ?stickyp) (normalize-arith-triple x :sticky-in sticky-in))
         ((fp-arith-triple x))
         ((fp-size size))
         (xval (fp-arith-triple->rational x)))
      (equal norm
             (make-fp-arith-triple
              :sign x.sign
              :exp (if (eql 0 xval)
                       0
                     (- (rational-exponent xval) size.frac-size))
              :man (if (eql xval 0)
                       0
                     (floor (* (expt 2 size.frac-size)
                               (rational-significand xval))
                            1)))))
    :hints (("Goal" :in-theory (enable normalize-arith-triple
                                       fp-arith-rightshift
                                       fp-arith-leftshift
                                       rational-sign-significand-exponent-of-fp-arith-triple->rational
                                       acl2::exponents-add-unrestricted))
            (and stable-under-simplificationp
                 '(:in-theory (enable logtail ash)))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::exponents-add-unrestricted)))))

  (local (defthm mod-divide-out
           (implies (and (not (equal (rfix y) 0))
                         (syntaxp (not (equal y ''1)))
                         (rationalp x))
                    (equal (mod x y)
                           (* y (mod (/ x y) 1))))
           :hints (("Goal" :in-theory (enable mod rfix)))))



  (defthmd normalize-arith-triple-round+sticky-in-terms-of-rational
    (b* ((r+s (normalize-arith-triple-round+sticky x frac-size))
         ((fp-arith-triple x))
         (xval (fp-arith-triple->rational x)))
      (equal r+s
             (if (eql 0 xval)
                 0
               (* (expt 2 (+ 1 (pos-fix frac-size)))
                  (mod (rational-significand xval)
                       (expt 2 (- (pos-fix frac-size))))))))
    :hints (("Goal" :in-theory (enable normalize-arith-triple-round+sticky
                                       rational-sign-significand-exponent-of-fp-arith-triple->rational))
            (and stable-under-simplificationp
                 '(:in-theory (enable loghead)))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::exponents-add-unrestricted)
                              :use ((:instance acl2::expt-type-prescription-integerp
                                               (r 2) (i (- (pos-fix frac-size)
                                                           (integer-length (fp-arith-triple->man x))))))))))


  (local (defthm normalize-arith-triple-multivalues
           (equal (list (mv-nth 0 (normalize-arith-triple x :sticky-in sticky-in))
                        (mv-nth 1 (normalize-arith-triple x :sticky-in sticky-in))
                        (mv-nth 2 (normalize-arith-triple x :sticky-in sticky-in)))
                  (normalize-arith-triple x :sticky-in sticky-in))
           :hints (("Goal" :in-theory (enable normalize-arith-triple)))))

  (defcong fp-arith-triple->rational-and-sign-equiv equal (normalize-arith-triple x :sticky-in sticky-in) 1
    :hints (("Goal" :use ((:instance normalize-arith-triple-multivalues)
                          (:instance normalize-arith-triple-multivalues (x x-equiv)))
             :in-theory (e/d (normalize-arith-triple-in-terms-of-rational
                              normalize-in-terms-of-round+sticky
                              normalize-arith-triple-round+sticky-in-terms-of-rational)
                             (normalize-arith-triple-multivalues))))))



(define normalize-rational-to-arith-triple ((x rationalp)
                                            (frac-size posp)
                                            &key
                                            ((sticky-in booleanp) 'nil))
  :returns (mv (norm fp-arith-triple-p)
               (roundp booleanp :rule-classes :type-prescription)
               (stickyp booleanp :rule-classes :type-prescription))
  (b* (((when (equal (rfix x) 0))
        (mv (fp-arith-triple 0 0 0) nil
            (mbe :logic (acl2::bool-fix sticky-in) :exec sticky-in)))
       (frac-size (mbe :logic (acl2::pos-fix frac-size) :exec frac-size))
       (signif (rational-significand x))
       (exp (rational-exponent x))
       (sign (if (< x 0) 1 0))
       (norm-exact (* signif (expt 2 frac-size)))
       (norm (make-fp-arith-triple :sign sign
                                   :exp (- exp frac-size)
                                   :man (floor norm-exact 1)))
       (round+sticky (* 2 (mod norm-exact 1)))
       (roundp (>= round+sticky 1))
       (stickyp (or (and sticky-in t)
                    (not (integerp round+sticky)))))
    (mv norm roundp stickyp))
  ///
  (local
   (defthm rational-exponent-of-times-power
     (implies (and (rationalp x)
                   (not (equal x 0)))
              (equal (rational-exponent (* x (expt 2 y)))
                     (+ (ifix y) (rational-exponent x))))
     :hints (("Goal" :in-theory (enable acl2::rational-exponent/significand-of-multiply)))))

  (local
   (defthm rational-significand-of-times-power
     (implies (and (rationalp x)
                   (not (equal x 0)))
              (equal (rational-significand (* x (expt 2 y)))
                     (rational-significand x)))
     :hints (("Goal" :in-theory (enable acl2::rational-exponent/significand-of-multiply)))))

  (local
   (defthm ash-1-integer-length-minus-1-lte-x
     (implies (posp x)
              (<= (ash 1 (+ -1 (integer-length x))) x))
     :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                         bitops::ihsext-recursive-redefs)))))

  (local
   (defthm rational-exponent-of-pos
     (implies (posp x)
              (equal (rational-exponent x)
                     (1- (integer-length x))))
     :hints (("Goal"
              :in-theory (enable rational-exponent)
              :expand ((rational-exponent x))))))

  (local
   (defthm floor-divide-out
     (implies (and (not (equal (rfix y) 0))
                   (syntaxp (not (equal y ''1)))
                   (rationalp x))
              (equal (floor x y)
                     (floor (/ x y) 1)))
     :hints (("Goal" :in-theory (enable rfix)))))

  (local
   (defthm mod-divide-out
     (implies (and (not (equal (rfix y) 0))
                   (syntaxp (not (equal y ''1)))
                   (rationalp x))
              (equal (mod x y)
                     (* y (mod (/ x y) 1))))
     :hints (("Goal" :in-theory (enable mod rfix)))))

  (local (in-theory (disable acl2::/r-when-abs-numerator=1
                             ;; acl2::floor-bounded-by-/
                             acl2::x*y>1-positive
                             acl2::0-<-*
                             acl2::floor-=-x/y)))

  (defret <fn>.man-zero
    (implies (equal (rfix x) 0)
             (equal (fp-arith-triple->man norm) 0)))

  (encapsulate
    ()

    (local (include-book "centaur/bitops/integer-length" :dir :system))

    (local
     (defthmd integer-length-of-normalized-nat
       (implies (and (integerp m)
                     (natp f)
                     (<= (expt 2 f) m)
                     (< m (expt 2 (1+ f))))
                (equal (integer-length m) (1+ f)))))

    (local (include-book "arithmetic-3/top" :dir :system))

    (defret integer-length-of-<fn>.man
      (implies (not (equal (rfix x) 0))
               (equal (integer-length (fp-arith-triple->man norm))
                      (1+ (pos-fix frac-size))))
      :hints (("Goal"
               :nonlinearp t
               :use ((:instance integer-length-of-normalized-nat
                                (m (floor (* (rational-significand x)
                                             (expt 2 (pos-fix frac-size)))
                                          1))
                                (f (pos-fix frac-size))))
               :in-theory (disable acl2::normalize-factors-gather-exponents)))))

  (defretd <fn>-correct-for-arith-triples
    :pre-bind ((x (fp-arith-triple->rational in))
               (frac-size (fp-size->frac-size size)))
    (implies (not (equal x 0))
             (b* (((mv norm-spec & &)
                   (normalize-arith-triple in :sticky-in sticky-in)))
               (equal norm-spec norm)))
    :hints (("Goal" :in-theory (enable normalize-arith-triple
                                       fp-arith-rightshift
                                       fp-arith-leftshift
                                       fp-arith-triple->rational
                                       fp-sign-value-redef))
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-sign
                                      acl2::rational-significand-in-terms-of-rational-exponent
                                      logtail
                                      loghead)))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::exponents-add-unrestricted
                                      ash))))
    :otf-flg t))

(define normalize-rational-to-arith-triple-round+sticky ((x rationalp)
                                                         (frac-size posp))
  :returns (round+sticky rationalp :rule-classes :type-prescription)
  (b* (((when (equal (rfix x) 0)) 0)
       (frac-size (mbe :logic (acl2::pos-fix frac-size) :exec frac-size))
       (signif (rational-significand x))
       (norm-exact (* signif (expt 2 frac-size))))
    (* 2 (mod norm-exact 1)))
  ///
  (local
   (defthm rational-exponent-of-times-power
     (implies (and (rationalp x)
                   (not (equal x 0)))
              (equal (rational-exponent (* x (expt 2 y)))
                     (+ (ifix y) (rational-exponent x))))
     :hints (("Goal" :in-theory (enable acl2::rational-exponent/significand-of-multiply)))))

  (local
   (defthm rational-significand-of-times-power
     (implies (and (rationalp x)
                   (not (equal x 0)))
              (equal (rational-significand (* x (expt 2 y)))
                     (rational-significand x)))
     :hints (("Goal" :in-theory (enable acl2::rational-exponent/significand-of-multiply)))))

  (local
   (defthm ash-1-integer-length-minus-1-lte-x
     (implies (posp x)
              (<= (ash 1 (+ -1 (integer-length x))) x))
     :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                         bitops::ihsext-recursive-redefs)))))

  (local
   (defthm rational-exponent-of-pos
     (implies (posp x)
              (equal (rational-exponent x)
                     (1- (integer-length x))))
     :hints (("Goal"
              :in-theory (enable rational-exponent)
              :expand ((rational-exponent x))))))

  (local
   (defthm floor-divide-out
     (implies (and (not (equal (rfix y) 0))
                   (syntaxp (not (equal y ''1)))
                   (rationalp x))
              (equal (floor x y)
                     (floor (/ x y) 1)))
     :hints (("Goal" :in-theory (enable rfix)))))

  (local
   (defthm mod-divide-out
     (implies (and (not (equal (rfix y) 0))
                   (syntaxp (not (equal y ''1)))
                   (rationalp x))
              (equal (mod x y)
                     (* y (mod (/ x y) 1))))
     :hints (("Goal" :in-theory (enable mod rfix)))))

  (local (in-theory (disable acl2::/r-when-abs-numerator=1)))

  (local
   (defthm integerp-of-divide-exponents
     (implies (and (<= y (+ 1 x))
                   (integerp y)
                   (integerp x)
                   (integerp z))
              (integerp (* 2 z (expt 2 x) (/ (expt 2 y)))))
     :hints (("Goal"
              :use ((:instance (:theorem (implies (natp x) (integerp (expt 2 x))))
                               (x (+ 1 x (- y))))
                    (:instance (:theorem (implies (and (integerp x) (integerp y)) (integerp (* x y))))
                               (x z) (y (* 2 (expt 2 x) (/ (expt 2 y))))))
              :in-theory (e/d (acl2::exponents-add-unrestricted))))))

  (defretd <fn>-correct-for-arith-triples
    :pre-bind ((x (fp-arith-triple->rational in)))
    (implies (not (equal x 0))
             (equal (normalize-arith-triple-round+sticky in frac-size)
                    round+sticky))
    :hints (("Goal" :in-theory (enable normalize-arith-triple-round+sticky
                                       fp-arith-triple->rational
                                       fp-sign-value-redef))
            (and stable-under-simplificationp
                 '(:in-theory (enable rational-sign
                                      acl2::rational-significand-in-terms-of-rational-exponent
                                      logtail
                                      loghead)))
            (and stable-under-simplificationp
                 '(:in-theory (enable ;; acl2::exponents-add-unrestricted
                               ash nfix)))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::exponents-add-unrestricted))))
    :otf-flg t)

  (defret <fn>-lower-bound
    (<= 0 round+sticky)
    :rule-classes (:linear :type-prescription))

  (defret <fn>-upper-bound
    (< round+sticky 2)
    :hints (("Goal"
             :use ((:instance unsigned-byte-p-of-loghead
                              (size (+ -1 (- (POS-FIX FRAC-SIZE))
                                       (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                              (size1 (+ -1 (- (POS-FIX FRAC-SIZE))
                                        (INTEGER-LENGTH (FP-ARITH-TRIPLE->MAN X))))
                              (i (fp-arith-triple->man x))))
             :in-theory (e/d (unsigned-byte-p
                              acl2::exponents-add-unrestricted)
                             (unsigned-byte-p-of-loghead
                              acl2::loghead-upper-bound))))
    :rule-classes :linear)

  (defret <fn>-decomp
    (b* (((mv (fp-arith-triple norm) & &)
          (normalize-rational-to-arith-triple x frac-size)))
      (implies (rationalp x)
               (equal x
                      (* (fp-sign-value norm.sign)
                         (* (expt 2 norm.exp)
                            (+ (* 1/2 round+sticky) norm.man))))))
    :hints (("Goal" :in-theory (enable normalize-rational-to-arith-triple
                                       mod
                                       acl2::rational-exponent-in-terms-of-rational-significand
                                       rational-sign)))
    :rule-classes nil)

  (defretd normalize-rational-in-terms-of-round+sticky
    (b* (((mv & roundp stickyp)
          (normalize-rational-to-arith-triple x frac-size :sticky-in sticky-in)))
      (and (equal roundp
                  (<= 1 round+sticky))
           (equal stickyp
                  (or (and sticky-in t)
                      (not (integerp round+sticky))))))
    :hints (("Goal" :in-theory (enable normalize-rational-to-arith-triple)))))

(local
 (defthmd normalize-rational-to-arith-triple-correct-for-arith-triples-full-decomp
   (b* ((x (fp-arith-triple->rational in))
        (frac-size (fp-size->frac-size size))
        ((mv norm roundp stickyp)
         (normalize-rational-to-arith-triple x frac-size :sticky-in sticky-in))
        ((mv norm-spec roundp-spec stickyp-spec)
         (normalize-arith-triple in :sticky-in sticky-in :verbosep nil)))
     (implies (not (equal x 0))
              (and (equal norm-spec norm)
                   (equal roundp-spec roundp)
                   (equal stickyp-spec stickyp))))
   :hints (("Goal"
            :in-theory (enable
                        normalize-rational-to-arith-triple-correct-for-arith-triples
                        normalize-rational-in-terms-of-round+sticky
                        normalize-rational-to-arith-triple-round+sticky-correct-for-arith-triples
                        normalize-in-terms-of-round+sticky)))))

(defthmd normalize-rational-to-arith-triple-correct-for-arith-triples-full
  (b* ((x (fp-arith-triple->rational in))
       (frac-size (fp-size->frac-size size)))
    (implies (not (equal x 0))
             (equal (normalize-rational-to-arith-triple x frac-size
                                                        :sticky-in sticky-in)
                    (normalize-arith-triple in
                                            :sticky-in sticky-in
                                            :verbosep nil))))
  :hints (("Goal"
           :use normalize-rational-to-arith-triple-correct-for-arith-triples-full-decomp
           :in-theory '(normalize-rational-to-arith-triple
                        normalize-arith-triple))))

(define normalize-rational+round-arith-triple ((x rationalp)
                                               (rc fp-rc-p)
                                               &key
                                               ((size fp-size-p) 'size)
                                               ((sticky-in booleanp) 'nil))
  :returns (res fp-arith-triple-p) ;; normalized, rounded
  :guard-hints (("Goal"
                 :use ((:instance integer-length-of-normalize-rational-to-arith-triple.man
                                  (frac-size (fp-size->frac-size size))))
                 :in-theory (disable integer-length-of-normalize-rational-to-arith-triple.man)))
  (b* (((mv norm roundp stickyp)
        (normalize-rational-to-arith-triple x
                                            (fp-size->frac-size size)
                                            :sticky-in sticky-in))
       ((mv round & &)
        (round-arith-triple norm roundp stickyp rc :verbosep nil)))
    round)
  ///
  (local (include-book "centaur/bitops/integer-length" :dir :system))
  (local (include-book "centaur/misc/multiply-out" :dir :system))

  (local
   (defthmd expt-2-of-minus-one
     (implies (integerp x)
              (equal (expt 2 (1- x))
                     (* 1/2 (expt 2 x))))))

  (local
   (defthmd expt-2-of-plus-one
     (implies (integerp x)
              (equal (expt 2 (1+ x))
                     (* 2 (expt 2 x))))
     :hints (("Goal" :in-theory (enable expt)))))

  (local
   (encapsulate
     ()

     (local (include-book "arithmetic-3/top" :dir :system))

     (local (in-theory (disable acl2::normalize-factors-gather-exponents)))

     (defthm integerp-rewrite-mod-1
       (implies (and (rationalp x)
                     (not (equal (mod (* x (expt 2 f))
                                      1)
                                 0)))
                (equal (integerp (* 2 (mod (* x (expt 2 f))
                                           1)))
                       (equal (mod (* x (expt 2 f))
                                   1)
                              1/2))))

     (defthm integer-length-of-floor-1
       (implies (and (rationalp x)
                     (natp f)
                     (<= 1 x)
                     (< x 2))
                (equal (integer-length (floor (* x (expt 2 f))
                                              1))
                       (1+ f)))
       :hints (("Goal"
                :nonlinearp t
                :use ((:instance bitops::integer-length-unique
                                 (x (floor (* x (expt 2 f))
                                           1))
                                 (y (1+ f)))))))))

  (local
   (defthmd integer-length-plus-one-unchanged
     (implies (and (natp x)
                   (equal (integer-length x) n)
                   (<= (integer-length (1+ x)) n))
              (equal (integer-length (1+ x)) n))
     :hints (("Goal"
              :use ((:instance bitops::integer-length-monotonic
                               (i x)
                               (j (1+ x))))
              :in-theory (disable bitops::integer-length-monotonic)))))

  (local
   (defthm integer-length-plus-one-ovf
     (implies (and (natp x)
                   (equal (integer-length x) n)
                   (< n (integer-length (1+ x))))
              (and (equal (integer-length (1+ x))
                          (1+ n))
                   (equal x (1- (expt 2 n)))))
     :hints (("Goal"
              :use ((:instance bitops::integer-length-when-less-than-exp
                               (x (1+ x))
                               (y n))
                    (:instance bitops::integer-length-when-greater-than-exp
                               (y n)))
              :in-theory (disable bitops::integer-length-when-less-than-exp
                                  bitops::integer-length-when-greater-than-exp)))
     :rule-classes nil))

  (local
   (defthm floor-mod-rel-1
     (implies (<= 1/2 (mod x 1))
              (<= (floor x 1) (- x 1/2)))
     :hints (("Goal" :in-theory (enable mod)))
     :rule-classes :linear))

  (local
   (defthm floor-mod-rel-2
     (implies (<= (mod x 1) 1/2)
              (<= (- x 1/2) (floor x 1)))
     :rule-classes :linear))

  (local
   (defthm logtail1-2*2^f
     (implies (integerp n)
              (equal (logtail 1 (* 2 n))
                     n))
     :hints (("Goal" :in-theory (enable logtail)))))

  (defret <fn>-bounds-when-rne
    (b* ((frac-size (fp-size->frac-size size))
         ((fp-arith-triple res))
         (val (fp-arith-triple->rational res))
         (exp (- (rational-exponent x)
                 (+ 1 frac-size))))
      (implies (and (rationalp x)
                    (equal (rc->rounding-mode rc) :rne))
               (and (<= (+ (- (expt 2 exp))
                           x)
                        val)
                    (<= val
                        (+ (expt 2 exp)
                           x)))))
    :hints (("Goal"
             :use ((:instance integer-length-plus-one-unchanged
                              (x (floor (* (rational-significand x)
                                           (expt 2 (fp-size->frac-size size)))
                                        1))
                              (n (1+ (fp-size->frac-size size))))
                   (:instance integer-length-plus-one-ovf
                              (x (floor (* (rational-significand x)
                                           (expt 2 (fp-size->frac-size size)))
                                        1))
                              (n (1+ (fp-size->frac-size size)))))
             :in-theory (e/d (fp-arith-triple->rational
                              normalize-rational-to-arith-triple
                              round-arith-triple
                              round-up
                              normalize-arith-triple
                              fp-arith-rightshift
                              acl2::rational-exponent-in-terms-of-rational-significand
                              acl2::divide-out-common-factors-<
                              expt-2-of-minus-one
                              expt-2-of-plus-one
                              rational-sign)
                             (acl2::rational-significand-base-case
                              (:linear acl2::x*y>1-positive)
                              acl2::x*y>1-positive
                              acl2::mod-x-y-=-x+y-for-rationals
                              acl2::mod-x-y-=-x+y-for-rationals
                              acl2::mod-x-y-=-x-for-rationals
                              abs
                              acl2::/r-when-abs-numerator=1
                              bitops::|(* 1/2 (expt 2 n))|))))
    :rule-classes :linear)
  )

;; Rounding of two rational numbers within a 1/2 ulp interval would return the
;; same value.

(defsection normalize-rational+round-arith-triple-within-1/2*ulp
  (local (include-book "centaur/bitops/integer-length" :dir :system))
  (local (include-book "centaur/misc/multiply-out" :dir :system))

  (define ulp ((x rationalp)
               (frac-size posp))
    :returns (res rationalp :rule-classes :type-prescription)
    (expt 2 (- (rational-exponent x) frac-size))
    ///
    (defret <fn>-is-positive
      (< 0 res)
      :rule-classes :linear)

    (defret <fn>-of-abs-canceled
      (equal (ulp (abs x) frac-size)
             res))

    (defretd <fn>-is-smaller
      (implies (and (rationalp x)
                    (not (equal x 0))
                    (posp frac-size))
               (< res (abs x)))
      :hints (("Goal"
               :use ((:instance acl2::rational-exponent-correct-positive
                                (x (abs x))))
               :in-theory (e/d ()
                               (acl2::rational-exponent-correct-positive)))
              (and stable-under-simplificationp
                   '(:nonlinearp t)))
      :rule-classes :linear))

  (define within-1/2*ulp ((x rationalp)
                          (y1 rationalp)
                          (y2 rationalp)
                          (frac-size posp))
    :returns (res booleanp :rule-classes :type-prescription)
    (b* ((ulp (ulp y2 frac-size)))
      (or (equal y1 y2)
          (and (< (- x ulp) y1)
               (< y1 (- x (* 1/2 ulp)))
               (< (- x ulp) y2)
               (< y2 (- x (* 1/2 ulp))))
          (and (< (- x (* 1/2 ulp)) y1)
               (< y1 x)
               (< (- x (* 1/2 ulp)) y2)
               (< y2 x))
          (and (< x y1)
               (< y1 (+ x (* 1/2 ulp)))
               (< x y2)
               (< y2 (+ x (* 1/2 ulp))))
          (and (< (+ x (* 1/2 ulp)) y1)
               (< y1 (+ x ulp))
               (< (+ x (* 1/2 ulp)) y2)
               (< y2 (+ x ulp))))))

  (local
   (defthm integer-length-of-normalized-man
     (implies (and (unsigned-byte-p (1+ f) m)
                   (<= (expt 2 f) m))
              (equal (integer-length m) (1+ f)))
     :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-1a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< xval 0)
                     (< (- xval ulp-x) yval)
                     (< yval (- xval (* 1/2 ulp-x))))
                (and (< (+ x.man 1/2)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (+ x.man 1)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-1b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< 0 yval)
                     (< (- xval ulp-x) yval)
                     (< yval (- xval (* 1/2 ulp-x))))
                (and (< (- x.man 1)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (- x.man 1/2)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-2a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< xval 0)
                     (< (- xval (* 1/2 ulp-x)) yval)
                     (< yval xval))
                (and (< x.man
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (+ x.man 1/2)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-2b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< 0 yval)
                     (< (- xval (* 1/2 ulp-x)) yval)
                     (< yval xval))
                (and (< (- x.man 1/2)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        x.man))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-3a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< yval 0)
                     (< xval yval)
                     (< yval (+ xval (* 1/2 ulp-x))))
                (and (< (- x.man 1/2)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        x.man))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-3b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (<= 0 xval)
                     (< xval yval)
                     (< yval (+ xval (* 1/2 ulp-x))))
                (and (< x.man
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (+ x.man 1/2)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-4a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< yval 0)
                     (< (+ xval (* 1/2 ulp-x)) yval)
                     (< yval (+ xval ulp-x)))
                (and (< (- x.man 1)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (- x.man 1/2)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (defthmd rational-significand-bounds-within-1/2*ulp-4b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size)))
       (implies (and (integerp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (<= 0 xval)
                     (< (+ xval (* 1/2 ulp-x)) yval)
                     (< yval (+ xval ulp-x)))
                (and (< (+ x.man 1/2)
                        (* (rational-significand yval)
                           (expt 2 frac-size)))
                     (< (* (rational-significand yval)
                           (expt 2 frac-size))
                        (+ x.man 1)))))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (e/d (ulp
                               acl2::rational-significand-in-terms-of-rational-exponent-abs
                               rational-sign-significand-exponent-of-fp-arith-triple->rational
                               fp-sign-value-redef
                               acl2::divide-out-common-factors-<)
                              (bitops::|(* 1/2 (expt 2 n))|))))
     :rule-classes :linear))

  (local
   (encapsulate
     ()

     (local (include-book "arithmetic-3/top" :dir :system))

     (defthmd floor-1-unique-lemma-1
       (implies (and (rationalp x)
                     (integerp n)
                     (<= (- n 1) x)
                     (<= x (- n 1/2)))
                (equal (floor x 1) (1- n))))

     (defthmd floor-1-unique-lemma-2
       (implies (and (rationalp x)
                     (integerp n)
                     (<= (- n 1/2) x)
                     (< x n))
                (equal (floor x 1) (1- n))))

     (defthmd floor-1-unique-lemma-3
       (implies (and (rationalp x)
                     (integerp n)
                     (<= n x)
                     (< x (+ n 1/2)))
                (equal (floor x 1) n)))

     (defthmd floor-1-unique-lemma-4
       (implies (and (rationalp x)
                     (integerp n)
                     (<= (+ n 1/2) x)
                     (< x (+ n 1)))
                (equal (floor x 1) n)))

     (defthmd mod-1-bounds-lemma-1
       (implies (and (rationalp x)
                     (integerp n)
                     (< (- n 1) x)
                     (< x (- n 1/2)))
                (and (< 0 (mod x 1))
                     (< (mod x 1) 1/2)))
       :hints (("Goal" :in-theory (enable mod floor-1-unique-lemma-1)))
       :rule-classes :linear)

     (defthmd mod-1-bounds-lemma-2
       (implies (and (rationalp x)
                     (integerp n)
                     (< (- n 1/2) x)
                     (< x n))
                (and (< 1/2 (mod x 1))
                     (< (mod x 1) 1)))
       :hints (("Goal" :in-theory (enable mod floor-1-unique-lemma-2)))
       :rule-classes :linear)

     (defthmd mod-1-bounds-lemma-3
       (implies (and (rationalp x)
                     (integerp n)
                     (< n x)
                     (< x (+ n 1/2)))
                (and (< 0 (mod x 1))
                     (< (mod x 1) 1/2)))
       :hints (("Goal" :in-theory (enable mod floor-1-unique-lemma-3)))
       :rule-classes :linear)

     (defthmd mod-1-bounds-lemma-4
       (implies (and (rationalp x)
                     (integerp n)
                     (< (+ n 1/2) x)
                     (< x (+ n 1)))
                (and (< 1/2 (mod x 1))
                     (< (mod x 1) 1)))
       :hints (("Goal" :in-theory (enable mod floor-1-unique-lemma-4)))
       :rule-classes :linear)
     ))

  (local
   (defthmd not-integerp-lemma
     (implies (and (rationalp x)
                   (< 1/2 x)
                   (< x 1))
              (not (integerp (* 2 x))))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-1a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< xval 0)
                     (< (- xval ulp-x) yval)
                     (< yval (- xval (* 1/2 ulp-x))))
                (and (equal norm x)
                     roundp
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x))
                    (:instance not-integerp-lemma
                               (x (mod (* (rational-significand yval)
                                          (expt 2 frac-size))
                                       1))))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-1a
                                 floor-1-unique-lemma-4
                                 mod-1-bounds-lemma-4)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-1b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< 0 yval)
                     (< (- xval ulp-x) yval)
                     (< yval (- xval (* 1/2 ulp-x))))
                (and (equal norm
                            (change-fp-arith-triple x :man (1- x.man)))
                     (not roundp)
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-1b
                                 floor-1-unique-lemma-1
                                 mod-1-bounds-lemma-1)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-2a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< xval 0)
                     (< (- xval (* 1/2 ulp-x)) yval)
                     (< yval xval))
                (and (equal norm x)
                     (not roundp)
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-2a
                                 floor-1-unique-lemma-3
                                 mod-1-bounds-lemma-3)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-2b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< 0 yval)
                     (< (- xval (* 1/2 ulp-x)) yval)
                     (< yval xval))
                (and (equal norm
                            (change-fp-arith-triple x :man (1- x.man)))
                     roundp
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x))
                    (:instance not-integerp-lemma
                               (x (mod (* (rational-significand yval)
                                          (expt 2 frac-size))
                                       1))))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-2b
                                 floor-1-unique-lemma-2
                                 mod-1-bounds-lemma-2)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-3a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< yval 0)
                     (< xval yval)
                     (< yval (+ xval (* 1/2 ulp-x))))
                (and (equal norm
                            (change-fp-arith-triple x :man (1- x.man)))
                     roundp
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x))
                    (:instance not-integerp-lemma
                               (x (mod (* (rational-significand yval)
                                          (expt 2 frac-size))
                                       1))))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-3a
                                 floor-1-unique-lemma-2
                                 mod-1-bounds-lemma-2)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-3b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (<= 0 xval)
                     (< xval yval)
                     (< yval (+ xval (* 1/2 ulp-x))))
                (and (equal norm x)
                     (not roundp)
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-3b
                                 floor-1-unique-lemma-3
                                 mod-1-bounds-lemma-3)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-4a
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (< yval 0)
                     (< (+ xval (* 1/2 ulp-x)) yval)
                     (< yval (+ xval ulp-x)))
                (and (equal norm
                            (change-fp-arith-triple x :man (1- x.man)))
                     (not roundp)
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x)))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-4a
                                 floor-1-unique-lemma-1
                                 mod-1-bounds-lemma-1)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-4b
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          (ulp-x (ulp xval frac-size))
          ((mv norm roundp stickyp)
           (normalize-rational-to-arith-triple yval
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval)
                     (equal (rational-exponent yval)
                            (rational-exponent xval))
                     (<= 0 xval)
                     (< (+ xval (* 1/2 ulp-x)) yval)
                     (< yval (+ xval ulp-x)))
                (and (equal norm x)
                     roundp
                     stickyp)))
     :hints (("Goal"
              :use ((:instance fp-arith-triple->rational (x x))
                    (:instance not-integerp-lemma
                               (x (mod (* (rational-significand yval)
                                          (expt 2 frac-size))
                                       1))))
              :in-theory (enable normalize-rational-to-arith-triple
                                 rational-sign-significand-exponent-of-fp-arith-triple->rational
                                 rational-significand-bounds-within-1/2*ulp-4b
                                 floor-1-unique-lemma-4
                                 mod-1-bounds-lemma-4)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-normalized
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          ((mv norm1 roundp1 stickyp1)
           (normalize-rational-to-arith-triple yval1
                                               frac-size
                                               :sticky-in sticky-in))
          ((mv norm2 roundp2 stickyp2)
           (normalize-rational-to-arith-triple yval2
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (<= (expt 2 frac-size) x.man)
                     (rationalp yval1)
                     (rationalp yval2)
                     (not (equal yval1 0))
                     (not (equal yval2 0))
                     (equal (rational-exponent yval1)
                            (rational-exponent xval))
                     (equal (rational-exponent yval2)
                            (rational-exponent xval))
                     (equal (<= 0 yval1)
                            (<= 0 xval))
                     (equal (<= 0 yval2)
                            (<= 0 xval))
                     (within-1/2*ulp xval yval1 yval2 frac-size))
                (and (equal norm1 norm2)
                     (equal roundp1 roundp2)
                     (equal stickyp1 stickyp2))))
     :hints (("Goal"
              :cases ((<= 0 (fp-arith-triple->rational x)))
              :in-theory (enable within-1/2*ulp
                                 ulp
                                 normalize-rational-within-1/2*ulp-1a
                                 normalize-rational-within-1/2*ulp-1b
                                 normalize-rational-within-1/2*ulp-2a
                                 normalize-rational-within-1/2*ulp-2b
                                 normalize-rational-within-1/2*ulp-3a
                                 normalize-rational-within-1/2*ulp-3b
                                 normalize-rational-within-1/2*ulp-4a
                                 normalize-rational-within-1/2*ulp-4b)))))

  (local
   (defthmd normalize-rational-within-1/2*ulp-decomp
     (b* (((fp-arith-triple x))
          (xval (fp-arith-triple->rational x))
          ((mv norm1 roundp1 stickyp1)
           (normalize-rational-to-arith-triple yval1
                                               frac-size
                                               :sticky-in sticky-in))
          ((mv norm2 roundp2 stickyp2)
           (normalize-rational-to-arith-triple yval2
                                               frac-size
                                               :sticky-in sticky-in)))
       (implies (and (fp-arith-triple-p x)
                     (posp frac-size)
                     (unsigned-byte-p (1+ frac-size) x.man)
                     (not (equal x.man 0))
                     (rationalp yval1)
                     (rationalp yval2)
                     (not (equal yval1 0))
                     (not (equal yval2 0))
                     (equal (rational-exponent yval1)
                            (rational-exponent xval))
                     (equal (rational-exponent yval2)
                            (rational-exponent xval))
                     (equal (<= 0 yval1)
                            (<= 0 xval))
                     (equal (<= 0 yval2)
                            (<= 0 xval))
                     (within-1/2*ulp xval yval1 yval2 frac-size))
                (and (equal norm1 norm2)
                     (equal roundp1 roundp2)
                     (equal stickyp1 stickyp2))))
     :hints (("Goal"
              :use ((:instance normalize-rational-within-1/2*ulp-normalized
                               (x (left-normalize-arith-triple x
                                                               frac-size))))))))

  (defthmd normalize-rational-within-1/2*ulp
    (b* (((fp-arith-triple x))
         (xval (fp-arith-triple->rational x)))
      (implies (and (fp-arith-triple-p x)
                    (posp frac-size)
                    (unsigned-byte-p (1+ frac-size) x.man)
                    (not (equal x.man 0))
                    (rationalp yval1)
                    (rationalp yval2)
                    (not (equal yval1 0))
                    (not (equal yval2 0))
                    (equal (rational-exponent yval1)
                           (rational-exponent xval))
                    (equal (rational-exponent yval2)
                           (rational-exponent xval))
                    (equal (<= 0 yval1)
                           (<= 0 xval))
                    (equal (<= 0 yval2)
                           (<= 0 xval))
                    (within-1/2*ulp xval yval1 yval2 frac-size))
               (equal (normalize-rational-to-arith-triple yval1
                                                          frac-size
                                                          :sticky-in sticky-in)
                      (normalize-rational-to-arith-triple yval2
                                                          frac-size
                                                          :sticky-in sticky-in))))
    :hints (("Goal"
             :use normalize-rational-within-1/2*ulp-decomp
             :in-theory '(normalize-rational-to-arith-triple))))

  (defthmd normalize-rational+round-arith-triple-within-1/2*ulp
    (b* (((fp-arith-triple x))
         (frac-size (fp-size->frac-size size))
         (xval (fp-arith-triple->rational x)))
      (implies (and (fp-arith-triple-p x)
                    (unsigned-byte-p (1+ frac-size) x.man)
                    (not (equal x.man 0))
                    (rationalp yval1)
                    (rationalp yval2)
                    (not (equal yval1 0))
                    (not (equal yval2 0))
                    (equal (rational-exponent yval1)
                           (rational-exponent xval))
                    (equal (rational-exponent yval2)
                           (rational-exponent xval))
                    (equal (<= 0 yval1)
                           (<= 0 xval))
                    (equal (<= 0 yval2)
                           (<= 0 xval))
                    (within-1/2*ulp xval yval1 yval2 frac-size))
               (equal (normalize-rational+round-arith-triple
                       yval1 rc :sticky-in sticky-in)
                      (normalize-rational+round-arith-triple
                       yval2 rc :sticky-in sticky-in))))
    :hints (("Goal"
             :in-theory (enable normalize-rational+round-arith-triple
                                normalize-rational-within-1/2*ulp))))
  )

(local
 (defthm abs-maintain-inequality-lemma
   (implies (and (< (- y u) x)
                 (< x (+ y u)))
            (and (< (- (abs y) u)
                    (abs x))
                 (< (abs x)
                    (+ (abs y) u))))
   :rule-classes :linear))

(define approx-within-ulp ((x rationalp)
                           (y rationalp)
                           (frac-size posp))
  :returns (res booleanp :rule-classes :type-prescription)
  (and (< (- y (ulp y frac-size)) x)
       (< x (+ y (ulp y frac-size))))
  ///
  (defretd <fn>-in-terms-of-abs
    (implies res
             (< (abs (- x y))
                (ulp y frac-size)))
    :rule-classes :linear)

  (defret <fn>-of-abs
    (implies res
             (<fn> (abs x) (abs y) frac-size))
    :hints (("Goal" :in-theory (disable abs))))

  (defret not-<fn>-zero
    (implies (and (not (equal (rfix y) 0))
                  (posp frac-size))
             (not (<fn> 0 y frac-size)))
    :hints (("Goal" :in-theory (enable ulp
                                       acl2::exponents-add-unrestricted
                                       acl2::rational-exponent-in-terms-of-rational-significand
                                       rational-sign))
            (and stable-under-simplificationp
                 '(:nonlinearp t))))

  (defret <fn>-implies-nonzero-arith-triple-man
    :pre-bind ((x (fp-arith-triple->rational in)))
    (implies (and res
                  (not (equal (rfix y) 0))
                  (posp frac-size))
             (not (equal (fp-arith-triple->man in) 0)))
    :hints (("Goal"
             :use not-<fn>-zero
             :in-theory (e/d (fp-arith-triple->rational)
                             (not-<fn>-zero)))))
  )

(define approx-within-eps*ulp ((x rationalp)
                               (y rationalp)
                               (eps (and (rationalp eps) (<= 0 eps)))
                               (frac-size posp))
  :returns (res booleanp :rule-classes :type-prescription)
  (and (< (- y (* eps (ulp y frac-size)))
          x)
       (< x
          (+ y (* eps (ulp y frac-size)))))
  ///
  (defretd <fn>-in-terms-of-abs
    (implies res
             (< (abs (- x y))
                (* eps (ulp y frac-size))))
    :rule-classes :linear)

  (defret <fn>-of-abs
    (implies res
             (<fn> (abs x) (abs y) eps frac-size))
    :hints (("Goal" :in-theory (disable abs))))

  (defretd <fn>-=>-within-ulp
    (implies (and res
                  (<= eps 1))
             (approx-within-ulp x y frac-size))
    :hints (("Goal"
             :nonlinearp t
             :in-theory (enable approx-within-ulp))))

  (defret not-<fn>-zero
    (implies (and (<= eps 1)
                  (not (equal (rfix y) 0))
                  (posp frac-size))
             (not (<fn> 0 y eps frac-size)))
    :hints (("Goal" :in-theory (enable ulp
                                       acl2::exponents-add-unrestricted
                                       acl2::rational-exponent-in-terms-of-rational-significand
                                       rational-sign))
            (and stable-under-simplificationp
                 '(:nonlinearp t))))
  )
