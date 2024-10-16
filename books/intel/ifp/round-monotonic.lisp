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

(include-book "round-math")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p)))


(local (include-book "centaur/misc/multiply-out" :dir :system))



(local (defund norm-exp (x size)
         (b* (((fp-arith-triple x))
              ((fp-size size)))
           (+ x.exp (- (integer-length x.man) (+ 2 size.frac-size))))))

(local
 (defthm normalize-round+sticky-value-decomp-x/y
   (b* (((mv (fp-arith-triple norm) & &)
         (normalize-arith-triple x))
        ((fp-arith-triple x))
        ((fp-size size))
        (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
     (implies (and (syntaxp (or (equal x 'x)
                                (equal x 'y))))
              (equal (fp-arith-triple->rational x)
                     (* (fp-sign-value x.sign)
                        (* (expt 2 (norm-exp x size))
                           (+ round+sticky (* 2 norm.man)))))))
   :hints(("Goal" :use normalize-round+sticky-value-decomp
           :in-theory (enable norm-exp)))))

(local (defund norm-exp-diff (x y size)
         (- (norm-exp x size)
            (norm-exp y size))))

(local (defthm norm-exp-y-in-terms-of-diff
         (implies (bind-free (and (eq y 'y)
                                  '((x . x)))
                             (x))
                  (equal (norm-exp y size)
                         (- (norm-exp x size) (norm-exp-diff x y size))))
         :hints(("Goal" :in-theory (enable norm-exp-diff)))))





(local (defthmd normalize-integer-length-x/y
         (implies (And (syntaxp (or (equal in 'x) (equal in 'y)))
                       (bind-free '((size . size)) (size)))
                  (equal (integer-length (fp-arith-triple->man in))
                         (+ 2
                            (norm-exp in size)
                            (- (fp-arith-triple->exp in))
                            (fp-size->frac-size size))))
         :hints(("Goal" :in-theory (enable norm-exp)))))

(local (in-theory (disable FP-ARITH-TRIPLE->RATIONAL-OF-NORMALIZE-ARITH-TRIPLE-WHEN-NOT-STICKY
                           NORMALIZE-ARITH-TRIPLE-EXACT-IN-TERMS-OF-RATIONAL)))


(local (defthm less-than-0-of-fp-arith-triple->Rational
         (equal (< (fp-arith-triple->rational x) 0)
                (and (not (equal 0 (fp-arith-triple->man x)))
                     (equal (fp-arith-triple->sign x) 1)))
         :hints(("Goal" :in-theory (enable fp-arith-triple->rational)))))


(local (defthm man-of-normalize-equal-0
         (implies (equal (fp-arith-triple->man x) 0)
                  (equal (fp-arith-triple->man (mv-nth 0 (normalize-arith-triple x))) 0))
         :hints(("Goal" :in-theory (enable normalize-arith-triple)))))

(local (in-theory (disable (tau-system))))

(local (defthmd expt-2-when-greater-than-0
         (implies (and (integerp x)
                       (< 0 x))
                  (<= 2 (expt 2 x)))
         :rule-classes :linear))

(local (defthmd expt-2-when-less-than-0
         (implies (and (integerp x)
                       (< x 0))
                  (>=  1/2 (expt 2 x)))
         :hints(("Goal" :in-theory (enable expt)))
         :rule-classes :linear))


(local (defthm crock4
         (implies (and (bind-free '((e2f . (expt '2 (fp-size->frac-size$inline size))))
                                  (e2f))
                       (<= 0 xrs)
                       (< xrs 2)
                       (<= 0 yrs)
                       (< yrs 2)
                       (<= e2f x)
                       (<= x (+ -1 (* 2 e2f)))
                       (<= e2f y)
                       (<= y (+ -1 (* 2 e2f)))
                       (rationalp xrs)
                       (rationalp yrs)
                       (posp e2f)
                       (integerp x)
                       (integerp y)
                       (rationalp exp)
                       (<= 2 exp))
                  (> (+ (* xrs exp)
                        (* 2 x exp))
                     (+ yrs (* 2 y))))
         :hints (("goal" :nonlinearp t))))

(local (defthm crock5
         (implies (and (bind-free '((e2f . (expt '2 (fp-size->frac-size$inline size))))
                                  (e2f))
                       (<= 0 xrs)
                       (< xrs 2)
                       (<= 0 yrs)
                       (< yrs 2)
                       (<= e2f x)
                       (<= x (+ -1 (* 2 e2f)))
                       (<= e2f y)
                       (<= y (+ -1 (* 2 e2f)))
                       (rationalp xrs)
                       (rationalp yrs)
                       (posp e2f)
                       (integerp x)
                       (integerp y)
                       (rationalp exp)
                       (<= exp 1/2))
                  (> (+ (- (* xrs exp))
                        (- (* 2 x exp)))
                     (+ (- yrs) (- (* 2 y)))))
         :hints (("goal" :nonlinearp t))))


(defthm round-arith-triple-of-normalize-monotonic
  (b* (((mv xnorm xroundp xstickyp) (normalize-arith-triple x))
       ((mv xround & &) (round-arith-triple xnorm xroundp xstickyp rc))
       ((mv ynorm yroundp ystickyp) (normalize-arith-triple y))
       ((mv yround & &) (round-arith-triple ynorm yroundp ystickyp rc))
       (xval (fp-arith-triple->rational x))
       (xroundval (fp-arith-triple->rational xround))
       (yval (fp-arith-triple->rational y))
       (yroundval (fp-arith-triple->rational yround)))
    (implies (<= xval yval)
             (<= xroundval yroundval)))
  :hints (("goal" :in-theory (enable fp-sign-value-redef
                                     normalize-arith-triple-round+sticky-when-0)
           :cases ((equal (fp-arith-triple->man x) 0)))
          '(:cases ((equal (fp-arith-triple->man y) 0)))
          (and stable-under-simplificationp
               (acl2::use-termhint
                (b* ((rules (cond ((< 0 (norm-exp-diff x y size))
                                   '(expt-2-when-greater-than-0))
                                  ((< (norm-exp-diff x y size) 0)
                                   '(expt-2-when-less-than-0)))))
                  `(:computed-hint-replacement
                    ((and stable-under-simplificationp
                          '(:nonlinearp t)))
                    :cases ((equal (fp-arith-triple->man (mv-nth 0 (normalize-arith-triple x)))
                                   (fp-arith-triple->man (mv-nth 0 (normalize-arith-triple y)))))
                    :in-theory (enable ,@rules
                                       acl2::divide-out-common-factors-<
                                       acl2::exponents-add-unrestricted
                                       round-in-terms-of-round+sticky
                                       fp-sign-value-redef
                                       normalize-arith-triple-round+sticky-when-0
                                       normalize-integer-length-x/y)
                    :expand ((:Free (sign exp man) (fp-arith-triple->rational
                                                    (fp-arith-triple sign exp man)))
                             (:Free (x) (fp-arith-triple->rational
                                         (mv-nth 0 (normalize-arith-triple x :verbosep nil)))))))))))

