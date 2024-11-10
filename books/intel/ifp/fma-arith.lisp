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
(include-book "add-core")
(local (include-book "centaur/misc/multiply-out" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p)))

(define fp-mul-arith ((x fp-arith-triple-p)
                      (y fp-arith-triple-p)
                      &key
                      ((product-man-override
                        (or (not product-man-override)
                            (natp product-man-override)))
                       'nil))
  :returns (prod fp-arith-triple-p)
  (b* (((fp-arith-triple x))
       ((fp-arith-triple y)))
    (make-fp-arith-triple
     :sign (b-xor x.sign y.sign)
     :man (or product-man-override
              (* x.man y.man))
     :exp (+ x.exp y.exp)))
  ///
  (defret <fn>-correct
    (implies (not product-man-override)
             (equal (fp-arith-triple->rational prod)
                    (* (fp-arith-triple->rational x)
                       (fp-arith-triple->rational y))))
    :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                      b-xor))))

  (local (defthm posp-expt
           (implies (natp x)
                    (posp (expt 2 x)))
           :rule-classes :type-prescription))

  (local
   (defret <fn>-unsigned-byte-p-lemma
     (implies (and (not product-man-override)
                   (unsigned-byte-p x-width (fp-arith-triple->man x))
                   (unsigned-byte-p y-width (fp-arith-triple->man y)))
              (unsigned-byte-p (+ x-width y-width) (fp-arith-triple->man prod)))
     :hints (("Goal" :in-theory (enable unsigned-byte-p))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))))

  (defret <fn>-unsigned-byte-p
    (implies (and (not product-man-override)
                  (unsigned-byte-p x-width (fp-arith-triple->man x))
                  (unsigned-byte-p y-width (fp-arith-triple->man y))
                  (<= (+ x-width y-width) width)
                  (natp width))
             (unsigned-byte-p width (fp-arith-triple->man prod)))
    :hints (("Goal" :use <fn>-unsigned-byte-p-lemma
            :in-theory (disable <fn>-unsigned-byte-p-lemma <fn>)))))

(local (defthm equal-0-of-leftshift
         (implies (natp sh)
                  (equal (equal 0 (ash x sh))
                         (zip x)))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logtail-nonzero-by-integer-length
         (implies (< (nfix n) (integer-length x))
                  (not (equal 0 (logtail n x))))
         :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local
 (defret <fn>-nonzero-when-add-core-naive-nonzero
   (implies (and (unsigned-byte-p (pos-fix a-width) (fp-arith-triple->man a))
                 (unsigned-byte-p (pos-fix b-width) (fp-arith-triple->man b))
                 (not (equal 0 (fp-arith-triple->man a)))
                 (not (equal 0 (fp-arith-triple->man b)))
                 (>= (nfix leftshift) (pos-fix a-width))
                 (>= (nfix leftshift) (pos-fix b-width))
                 (>= (nfix leftshift) 3))
            (b* (((fp-arith-triple sum-spec) (fp-add-core-naive a b rc))
                 ((fp-arith-triple sum)))
              (implies (not (equal sum-spec.man 0))
                       (not (equal sum.man 0)))))
   :hints (("Goal" :use ((:instance fp-add-core2-correct-by-normalization-when-big-leftshift
                                   (size (fp-size 2 nil 1))))
           :in-theory (e/d (normalize-arith-triple
                            fp-arith-leftshift
                            fp-arith-rightshift)
                           (fp-add-core2-correct-by-normalization-when-big-leftshift))))
   :fn fp-add-core2))

(local
 (defret integer-length-of-<fn>.man-split
   (b* (((fp-arith-triple new-x))
        ((fp-arith-triple x))
        ((fp-size size)))
     (implies (case-split (posp x.man))
              (equal (integer-length new-x.man) (+ 1 size.frac-size))))
   :fn normalize-arith-triple))

(local (defthm fp-mul-arith-man-equal-0
         (implies (equal (fp-arith-triple->man (fp-mul-arith y z)) 0)
                  (equal (* (fp-arith-triple->rational y)
                            (fp-arith-triple->rational z))
                         0))
         :hints (("Goal" :use ((:instance fp-mul-arith-correct
                                         (x y) (y z)
                                         (product-man-override nil)))
                 :expand ((fp-arith-triple->rational (fp-mul-arith y z)))
                 :in-theory (disable fp-mul-arith-correct)))))

(local (defthm fp-arith-triple->rational-when-man-0
         (implies (equal (fp-arith-triple->man x) 0)
                  (equal (fp-arith-triple->rational x) 0))
         :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

(define fp-muladd-arith-naive ((x fp-arith-triple-p)
                               (y fp-arith-triple-p)
                               (z fp-arith-triple-p)
                               (rc fp-rc-p) ;; we should change everything to use a more abstract rounding mode
                               &key
                               ((product-man-override
                                 (or (not product-man-override)
                                     (natp product-man-override)))
                                'nil))
  :returns (res fp-arith-triple-p)
  (b* (((fp-arith-triple prod) (fp-mul-arith y z :product-man-override product-man-override))
       ((fp-arith-triple x)))
    (fp-add-core-naive x prod rc :verbosep nil))
  ///
  (defret <fn>-correct
    (implies (not product-man-override)
             (equal (fp-arith-triple->rational res)
                    (+ (fp-arith-triple->rational x)
                       (* (fp-arith-triple->rational y)
                          (fp-arith-triple->rational z))))))

  (defret <fn>-equals-zero
    (implies (not product-man-override)
             (iff (equal 0 (fp-arith-triple->man res))
                  (equal (+ (fp-arith-triple->rational x)
                            (* (fp-arith-triple->rational y)
                               (fp-arith-triple->rational z)))
                         0)))
    :hints (("Goal" :use <fn>-correct
             :expand ((fp-arith-triple->rational (fp-muladd-arith-naive x y z rc)))
             :in-theory (e/d ()
                             (<fn> <fn>-correct))))))

(define fp-muladd-arith ((x fp-arith-triple-p)
                         (y fp-arith-triple-p)
                         (z fp-arith-triple-p)
                         (rc fp-rc-p) ;; we should change everything to use a more abstract rounding mode
                         (frac-size posp)
                         &key
                         ((product-man-override
                           (or (not product-man-override)
                               (natp product-man-override)))
                          'nil))
  :guard (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z)))
  :returns (mv (res fp-arith-triple-p)
               (stickyp booleanp))
  (b* (((fp-arith-triple prod) (fp-mul-arith y z :product-man-override product-man-override))
       ((fp-arith-triple x))
       (mant-width (1+ (lposfix frac-size))))
    (fp-add-core2 x prod rc mant-width (* 2 mant-width) (* 2 mant-width)))
  ///

  (local (defthm unsigned-byte-p-integer-length
           (implies (natp x)
                    (unsigned-byte-p (integer-length x) x))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (defret <fn>-in-terms-of-add-naive
    (implies (and (not product-man-override)
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (equal (fp-size->frac-size size) frac-size))
             (equal (normalize-arith-triple res :sticky-in stickyp)
                    (normalize-arith-triple
                     (fp-muladd-arith-naive x y z rc
                                            :product-man-override product-man-override)
                     :sticky-in nil :verbosep nil)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive))))

  (defret <fn>-is-zero
    (implies (and (not product-man-override)
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (posp frac-size))
             (iff (equal 0 (fp-arith-triple->man res))
                  (equal 0 (fp-arith-triple->man (fp-muladd-arith-naive x y z rc)))))
    :hints (("Goal" :use ((:instance <fn>-in-terms-of-add-naive
                                     (size (make-fp-size :exp-size 2 :frac-size (pos-fix frac-size)))
                                     (frac-size (pos-fix frac-size))))
             :in-theory (e/d (normalize-arith-triple
                              fp-arith-rightshift
                              fp-arith-leftshift)
                             (<fn> <fn>-in-terms-of-add-naive
                                   fp-muladd-arith-naive-equals-zero))))))

(define fp-muladd-arith-round ((x fp-arith-triple-p)
                               (y fp-arith-triple-p)
                               (z fp-arith-triple-p)
                               (rc fp-rc-p) ;; we should change everything to use a more abstract rounding mode
                               (frac-size posp))
  :guard (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z)))
  :returns (res fp-arith-triple-p) ;; normalized, rounded
  (b* (((mv (fp-arith-triple sum) stickyp) (fp-muladd-arith x y z rc frac-size))
       (size (make-fp-size :exp-size 2 :frac-size frac-size))
       ((mv norm roundp stickyp)
        (normalize-arith-triple sum :sticky-in stickyp :verbosep nil))
       ((mv round & &)
        (round-arith-triple norm roundp stickyp rc :verbosep nil)))
    round)
  ///

  (local (in-theory (disable fp-muladd-arith)))

  (local (defret fp-add-core-naive-when-prod-0
           (b* (((fp-arith-triple prod))
                ((fp-arith-triple acc)))
             (implies (equal prod.man 0)
                      (equal sum
                             (make-fp-arith-triple :man acc.man
                                                   :exp (if (eql acc.man 0) 0 acc.exp)
                                                   :sign (if (and (eql acc.man 0) (not (eql acc.sign prod.sign)))
                                                             (BOOL->BIT (EQL (RC->ROUNDING-MODE RC) :RMI))
                                                           acc.sign)))))
           :hints (("Goal" :in-theory (enable fp-add-core-naive
                                              fp-arith-leftshift)))
           :fn fp-add-core-naive))

  (local (defthmd man-zero-iff-rational-zero
           (iff (equal (fp-arith-triple->man x) 0)
                (equal (fp-arith-triple->rational x) 0))
           :hints (("Goal" :in-theory (enable fp-arith-triple->rational-equal-0)))))

  (local (defretd mant-when-rational-equal-0
           (implies (equal (fp-arith-triple->rational x) 0)
                    (equal (fp-arith-triple->man x) 0))
           :hints (("Goal" :in-theory (enable fp-arith-triple->rational-equal-0)))))

  (defret <fn>-mantissa-zero-of-add-zero
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z)))
      (implies (and (equal x.man 0)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (iff (equal res.man 0)
                    (or (equal y.man 0)
                        (equal z.man 0)))))
    :hints (("Goal" :in-theory (e/d (man-zero-iff-rational-zero
                                     mant-when-rational-equal-0
                                     fp-sign-value)
                                    (fp-arith-triple->rational-equal-0)))))

  (defretd mantissa-of-<fn>-norm-add-zero
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round (fp-arith-triple 0 0 0)
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp 0 :sign 0)
                                 rc frac-size)))
      (implies (and (syntaxp (not (and (case-match y
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t))
                                       (case-match z
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t)))))
                    (equal rc (rounding-mode->rc :rne))
                    (equal x.man 0)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.man res-norm.man)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-mul-arith
                                       ))
            (and stable-under-simplificationp
                 '(:in-theory (enable mantissa-of-normalize-arith-triple-norm
                                      fp-add-core-naive-mantissa-sign-normalize-exponent
                                      mantissa-of-round-arith-triple-norm-round-nearest)))))

  (defretd exponent-of-<fn>-norm-add-zero
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round (fp-arith-triple 0 0 0)
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp 0 :sign 0)
                                 rc frac-size)))
      (implies (and (syntaxp (not (and (case-match y
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t))
                                       (case-match z
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t)))))
                    (equal rc (rounding-mode->rc :rne))
                    (equal x.man 0)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.exp
                      (if (eql res-norm.man 0)
                          0
                        (+ y.exp z.exp res-norm.exp)))))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-add-core-naive
                                       fp-mul-arith))
            (and stable-under-simplificationp
                 '(:in-theory (enable exponent-of-normalize-arith-triple-norm
                                      exponent-of-round-arith-triple-norm-round-nearest
                                      fp-add-core-naive-exponent-norm
                                      mantissa-of-normalize-arith-triple-norm
                                      fp-mul-arith)))))

  (defretd sign-of-<fn>-add-zero
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z)))
      (implies (and (equal x.man 0)
                    (not (equal y.man 0))
                    (not (equal z.man 0))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.sign
                      (b-xor y.sign z.sign))))
    :hints (("Goal" :in-theory (e/d (fp-muladd-arith-naive
                                     fp-add-core-naive
                                     fp-mul-arith)
                                    (normalize-arith-triple.sign-unchanged)))
            (and stable-under-simplificationp
                 '(:in-theory (enable normalize-arith-triple.sign-unchanged)))))

  (defretd mantissa-of-<fn>-norm
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round (make-fp-arith-triple :man x.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp (- (+ y.exp z.exp)
                                                                          (if (eql x.man 0) 0 x.exp))
                                                       :sign (b-xor (if (eql x.man 0) 0 x.sign)
                                                                    (b-xor y.sign z.sign)))
                                 rc frac-size)))
      (implies (and (syntaxp (not (and (case-match x
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t))
                                       (case-match y
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t)))))
                    (equal rc (rounding-mode->rc :rne))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.man res-norm.man)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-mul-arith
                                       ))
            (and stable-under-simplificationp
                 '(:in-theory (enable mantissa-of-normalize-arith-triple-norm
                                      mantissa-of-round-arith-triple-norm-round-nearest
                                      fp-add-core-naive-mantissa-normalize-sign-exponent))))
    :fn fp-muladd-arith-round)

  (defretd <fn>-normalize-z-when-y-0
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round x y
                                 (fp-arith-triple 0 0 0)
                                 rc frac-size)))
      (implies (and (syntaxp (not (or (equal z '(fp-arith-triple '0 '0 '0))
                                      (equal z ''((sign . 0) (exp . 0) (man . 0))))))
                    ;; (equal rc (rounding-mode->rc :rne))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man)
                    (equal 0 y.man)
                    (not (equal 0 x.man))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res res-norm)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-mul-arith
                                       fp-add-core-naive))))

  (defretd sign-of-<fn>-norm
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round (make-fp-arith-triple :man x.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp (- (+ y.exp z.exp)
                                                                          (if (eql x.man 0) 0 x.exp))
                                                       :sign (b-xor (if (eql x.man 0) 0 x.sign)
                                                                    (b-xor y.sign z.sign)))
                                 rc frac-size)))
      (implies (and (syntaxp (not (and (case-match x
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t))
                                       (case-match y
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t)))))
                    ;; (equal rc (rounding-mode->rc :rne))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.sign
                      (if (equal 0 res.man)
                          (if (eql x.sign (b-xor y.sign z.sign))
                              x.sign
                            (bool->bit (equal (rc->rounding-mode rc) :rmi)))
                        (b-xor (if (eql x.man 0) 0 x.sign)
                               res-norm.sign)))))
    :hints (("Goal" :in-theory (e/d (fp-muladd-arith-naive
                                     fp-mul-arith
                                     )
                                    (normalize-arith-triple.sign-unchanged)))
            (and stable-under-simplificationp
                 '(:in-theory (enable mantissa-of-normalize-arith-triple-norm
                                      mantissa-of-round-arith-triple-norm-round-nearest
                                      fp-add-core-naive-mantissa-normalize-sign-exponent))))
    :fn fp-muladd-arith-round)

  (defretd exponent-of-<fn>-norm
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         ((fp-arith-triple res-norm)
          (fp-muladd-arith-round (make-fp-arith-triple :man x.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp (- (+ y.exp z.exp)
                                                                          (if (eql x.man 0) 0 x.exp))
                                                       :sign (b-xor (if (eql x.man 0) 0 x.sign)
                                                                    (b-xor y.sign z.sign)))
                                 rc frac-size)))
      (implies (and (syntaxp (not (and (case-match x
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t))
                                       (case-match y
                                         (('fp-arith-triple ''0 ''0 &) t)
                                         (('quote ('(sign . 0) '(exp . 0) &)) t)))))
                    (equal rc (rounding-mode->rc :rne))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res.exp (+ (if (or (eql x.man 0)
                                         (eql res-norm.man 0))
                                     0
                                   x.exp)
                                 res-norm.exp))))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-add-core-naive-exponent-norm
                                       ))
            (and stable-under-simplificationp
                 '(:in-theory (enable exponent-of-normalize-arith-triple-norm
                                      exponent-of-round-arith-triple-norm-round-nearest
                                      fp-add-core-naive-exponent-norm
                                      fp-mul-arith)))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-add-core-naive-mantissa-normalize-sign-exponent
                                      fp-add-core-naive-exponent-norm
                                      mantissa-of-normalize-arith-triple-norm))))
    :fn fp-muladd-arith-round)

  (defretd <fn>-norm-multiplied-exp-sign
    (b* (((fp-arith-triple res))
         ((fp-arith-triple x))
         ((fp-arith-triple y))
         ((fp-arith-triple z))
         (res-norm
          (fp-muladd-arith-round x
                                 (make-fp-arith-triple :man y.man :exp 0 :sign 0)
                                 (make-fp-arith-triple :man z.man :exp (+ y.exp z.exp) :sign (b-xor y.sign z.sign))
                                 rc frac-size)))
      (implies (and (syntaxp (not (case-match y
                                    (('fp-arith-triple ''0 ''0 &) t)
                                    (('quote ('(sign . 0) '(exp . 0) &)) t))))
                    (equal rc (rounding-mode->rc :rne))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) y.man)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) z.man)
                    (posp frac-size))
               (equal res res-norm)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-naive
                                       fp-mul-arith
                                       fp-add-core-naive-mantissa-sign-normalize-exponent
                                       ))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable mantissa-of-normalize-arith-triple-norm
            ;;                           mantissa-of-round-arith-triple-norm-round-nearest
            ;;                           fp-add-core-naive-mantissa-sign-normalize-exponent)))
            ))

  (local (defthm unsigned-byte-p-integer-length
           (implies (natp x)
                    (unsigned-byte-p (integer-length x) x))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (local (defret width-of-normalize-arith-triple
           (implies (equal w (+ 1 (fp-size->frac-size size)))
                    (unsigned-byte-p w (fp-arith-triple->man new-x)))
           :hints (("Goal" :in-theory (enable normalize-arith-triple
                                              fp-arith-rightshift
                                              fp-arith-leftshift)))
           :fn normalize-arith-triple))

  (local (defret width-of-round-arith-triple
           (implies (and (equal w (+ 1 (fp-size->frac-size size)))
                         (unsigned-byte-p w (fp-arith-triple->man x)))
                    (unsigned-byte-p w (fp-arith-triple->man new-x)))
           :hints (("Goal" :in-theory (enable round-arith-triple)))
           :fn round-arith-triple))

  (local
   (defret width-of-<fn>-lemma
     (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                   (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                   (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z)))
              (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man res)))))

  (defret width-of-<fn>
    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (integerp w)
                  (<= (+ 1 (acl2::pos-fix frac-size)) w))
             (unsigned-byte-p w (fp-arith-triple->man res)))
    :hints (("Goal" :use width-of-<fn>-lemma
             :in-theory (disable <fn>
                                 width-of-<fn>-lemma))))

  (local (defret normalize-arith-triple-nonzero
           (implies (not (equal (fp-arith-triple->man x) 0))
                    (not (equal (fp-arith-triple->man new-x) 0)))
           :hints (("Goal" :in-theory (enable normalize-arith-triple
                                              fp-arith-rightshift
                                              fp-arith-leftshift)))
           :rule-classes :type-prescription
           :fn normalize-arith-triple))

  (defret <fn>-bounds-when-rne
    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne)
                  (posp frac-size))
             (b* (((fp-arith-triple res))
                  (val (fp-arith-triple->rational res))
                  (exact (+ (fp-arith-triple->rational x)
                            (* (fp-arith-triple->rational y)
                               (fp-arith-triple->rational z))))
                  (exp (- (rational-exponent exact)
                          (+ 1 frac-size))))
               (and (<= (+ (- (expt 2 exp))
                           exact)
                        val)
                    (<= val
                        (+ (expt 2 exp)
                           exact)))))
    :hints (("Goal" :in-theory (e/d (fp-muladd-arith-in-terms-of-add-naive)
                                    (FP-ARITH-TRIPLE->RATIONAL-OF-NORMALIZE-ARITH-TRIPLE-WHEN-NOT-STICKY)))))

  (defret <fn>-when-exact
    (implies (and (integerp (* (expt 2 frac-size)
                               (rational-significand (+ (fp-arith-triple->rational x)
                                                        (* (fp-arith-triple->rational y)
                                                           (fp-arith-triple->rational z))))))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (posp frac-size))
             (equal (fp-arith-triple->rational res)
                    (+ (fp-arith-triple->rational x)
                       (* (fp-arith-triple->rational y)
                          (fp-arith-triple->rational z))))))

  (defret <fn>-mantissa-length
    (b* (((fp-arith-triple res)))
      (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                    (posp frac-size)
                    (not (equal 0 (+ (fp-arith-triple->rational x)
                                     (* (fp-arith-triple->rational y)
                                        (fp-arith-triple->rational z))))))
               (equal (integer-length res.man)
                      (+ 1 frac-size))))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-round)))
    :fn fp-muladd-arith-round)

  (defret <fn>-mantissa-lower-bound
    (b* (((fp-arith-triple res)))
      (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                    (posp frac-size)
                    (not (equal 0 (+ (fp-arith-triple->rational x)
                                     (* (fp-arith-triple->rational y)
                                        (fp-arith-triple->rational z))))))
               (<= (expt 2 frac-size)
                   res.man)))
    :hints (("Goal"
             :use ((:instance equal-integer-length-of-positive
                              (x (fp-arith-triple->man
                                  (fp-muladd-arith-round x y z rc frac-size)))
                              (n (+ 1 frac-size))))
             :in-theory (disable fp-muladd-arith-round)))
    :fn fp-muladd-arith-round
    :rule-classes :linear)

  (defret <fn>-mantissa-equal-zero
    (b* (((fp-arith-triple res)))
      (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                    (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                    (posp frac-size))
               (iff (equal res.man 0)
                    (equal 0 (+ (fp-arith-triple->rational x)
                                (* (fp-arith-triple->rational y)
                                   (fp-arith-triple->rational z))))))))

  (defret <fn>-value-equal-zero
    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (posp frac-size))
             (iff (equal (fp-arith-triple->rational res) 0)
                  (equal 0 (+ (fp-arith-triple->rational x)
                              (* (fp-arith-triple->rational y)
                                 (fp-arith-triple->rational z)))))))

  ;; (defret <fn>-gte-exact
  ;;   (implies (and (integerp (* (expt 2 frac-size)
  ;;                              (rational-significand r)))
  ;;                 (rationalp r)
  ;;                 (<= r (+ (fp-arith-triple->rational x)
  ;;                          (* (fp-arith-triple->rational y)
  ;;                             (fp-arith-triple->rational z))))
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z)))
  ;;            (<= r (fp-arith-triple->rational res)))
  ;;   :rule-classes nil)

  ;; (defret <fn>-lte-exact
  ;;   (implies (and (integerp (* (expt 2 frac-size)
  ;;                              (rational-significand r)))
  ;;                 (rationalp r)
  ;;                 (<= (+ (fp-arith-triple->rational x)
  ;;                          (* (fp-arith-triple->rational y)
  ;;                             (fp-arith-triple->rational z)))
  ;;                     r)
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
  ;;                 (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z)))
  ;;            (<= (fp-arith-triple->rational res) r))
  ;;   :rule-classes nil)
  )

(encapsulate
  nil

  (local (defun multiply-add-of-arith (x y z)
           (+ (fp-arith-triple->rational x)
              (* (fp-arith-triple->rational y)
                 (fp-arith-triple->rational z)))))
  (local (defthm replace-x-with-multiply-add-of-arith-sign-signif-exp
           (implies (bind-free (and (eq x 'x)
                                    '((y . y) (z . z)))
                               (y z))
                    (equal (fp-arith-triple->rational x)
                           (+ (- (* (fp-arith-triple->rational y)
                                    (fp-arith-triple->rational z)))
                              (multiply-add-of-arith x y z))))))

  (local (in-theory (disable multiply-add-of-arith)))

  (defret <fn>-relative-error

    ;; (<= (+ (- (expt 2 exp)) exact) val)
    ;; ;; if exact is positive
    ;; (<= (+ (- (/ (expt 2 exp) exact)) 1) (/ val exact))
    ;; (<= (- (/ (expt 2 exp) exact)) (- (/ val exact) 1))
    ;; ;; if exact is negative
    ;; (>= (+ (- (/ (expt 2 exp) exact)) 1) (/ val exact))
    ;; (>= (- (/ (expt 2 exp) exact)) (- (/ val exact) 1))

    ;; (<= val (+ (expt 2 exp) exact))
    ;; ;; similar positive/negative cases --
    ;; (<= (/ val exact) (+ (/ (expt 2 exp) exact) 1))
    ;; (<= (- (/ val exact) 1) (/ (expt 2 exp) exact))

    ;; ;; altogether
    ;; (<= (abs (- (/ val exact) 1)) (abs (/ (expt 2 exp) exact)))

    ;; ;; Relative error bound is (abs (/ (expt 2 exp) exact))
    ;; (abs (/ (expt 2 (- (rational-exponent exact) (+ 1 frac-size))) exact))
    ;; ;; Express exact as sign * significand * 2^exponent -- abs cancels out sign
    ;; (/ (expt 2 (- expt (+ 1 frac-size))) (* significand (expt 2 expt)))
    ;; (/ 1 (* significand (expt 2 (+ 1 frac-size))))
    ;; <= (/ 1 (expt 2 (+ 1 frac-size)))

    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne)
                  (posp frac-size))
             (b* (((fp-arith-triple res))
                  (val (fp-arith-triple->rational res))
                  (exact (+ (fp-arith-triple->rational x)
                            (* (fp-arith-triple->rational y)
                               (fp-arith-triple->rational z)))))
               (implies (not (equal exact 0))
                        (<= (abs (- (/ val exact) 1))
                            (expt 2 (- (+ 1 frac-size)))))))
    :hints (("Goal" :use ((:instance acl2::rational-sign-significand-exponent-correct
                                     (x (multiply-add-of-arith x y z)))
                          (:instance <fn>-bounds-when-rne))
             :in-theory (disable <fn>-bounds-when-rne
                                 acl2::rational-sign-significand-exponent-correct))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (acl2::exponents-add-unrestricted
                                    rational-sign)
                                   (<fn>-bounds-when-rne
                                    acl2::rational-sign-significand-exponent-correct))))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))))

;; (- (/ val exact) 1) = error
;; (/ val exact) = 1 + error

;; val = exact*(1 + error)

(define fp-muladd-arith-round-error ((x fp-arith-triple-p)
                                     (y fp-arith-triple-p)
                                     (z fp-arith-triple-p)
                                     (rc fp-rc-p) ;; we should change everything to use a more abstract rounding mode
                                     (frac-size posp))
  :guard (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z)))
  :returns (error rationalp)
  (b* ((val (fp-arith-triple->rational (fp-muladd-arith-round x y z rc frac-size)))
       (exact (+ (fp-arith-triple->rational x)
                 (* (fp-arith-triple->rational y)
                    (fp-arith-triple->rational z))))
       ((when (eql 0 exact)) 0))
    (- (/ val exact) 1))
  ///
  (defret <fn>-bounds
    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne)
                  (posp frac-size))
             (and (<= (- (expt 2 (- (+ 1 frac-size)))) error)
                  (<= error (expt 2 (- (+ 1 frac-size))))))
    :hints (("Goal" :use fp-muladd-arith-round-relative-error
             :in-theory (disable fp-muladd-arith-round-relative-error)))
    :rule-classes :linear)

  (defretd fp-muladd-arith-round-in-terms-of-error
    (implies (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z))
                  (posp frac-size))
             (equal (fp-arith-triple->rational
                     (fp-muladd-arith-round x y z rc frac-size))
                    (* (+ (fp-arith-triple->rational x)
                          (* (fp-arith-triple->rational y)
                             (fp-arith-triple->rational z)))
                       (+ 1 error)))))

  (defret <fn>-when-exact
    (implies (and (integerp (* (expt 2 frac-size)
                               (rational-significand (+ (fp-arith-triple->rational x)
                                                        (* (fp-arith-triple->rational y)
                                                           (fp-arith-triple->rational z))))))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (posp frac-size))
             (equal error 0)))

  (defret <fn>-bounds-sp
    :pre-bind ((frac-size 23))
    (implies (and (unsigned-byte-p 24 (fp-arith-triple->man x))
                  (unsigned-byte-p 24 (fp-arith-triple->man y))
                  (unsigned-byte-p 24 (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne))
             (and (<= (- (expt 2 -24)) error)
                  (<= error (expt 2 -24))))
    :hints (("Goal" :in-theory (disable <fn>)))
    :rule-classes :linear)

  (defret <fn>-bounds-dp
    :pre-bind ((frac-size 52))
    (implies (and (unsigned-byte-p 53 (fp-arith-triple->man x))
                  (unsigned-byte-p 53 (fp-arith-triple->man y))
                  (unsigned-byte-p 53 (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne))
             (and (<= (- (expt 2 -53)) error)
                  (<= error (expt 2 -53))))
    :hints (("Goal" :in-theory (disable <fn>)))
    :rule-classes :linear))


(define fp-muladd-arith-round-ulps-error ((x fp-arith-triple-p)
                                          (y fp-arith-triple-p)
                                          (z fp-arith-triple-p)
                                          (rc fp-rc-p)
                                          (frac-size posp))
  :guard (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
              (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z)))
  :returns (error rationalp)
  (b* ((val (fp-arith-triple->rational (fp-muladd-arith-round x y z rc frac-size)))
       (exact (+ (fp-arith-triple->rational x)
                 (* (fp-arith-triple->rational y)
                    (fp-arith-triple->rational z))))
       ((when (eql 0 exact)) 0))
    (* (- val exact) (expt 2 (- (lposfix frac-size) (rational-exponent exact)))))
  ///
  (defret <fn>-bounds
    (implies (and (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (eq (rc->rounding-mode rc) :rne)
                  (posp frac-size))
             (and (<= -1/2 error)
                  (<= error 1/2)))
    :hints (("Goal" :use fp-muladd-arith-round-bounds-when-rne
             :in-theory (e/d (acl2::exponents-add-unrestricted)
                             (fp-muladd-arith-round-bounds-when-rne))))
    :rule-classes :linear)

  (defretd fp-muladd-arith-round-in-terms-of-ulps-error
    (implies (and (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 frac-size) (fp-arith-triple->man z))
                  (posp frac-size))
             (equal (fp-arith-triple->rational
                     (fp-muladd-arith-round x y z rc frac-size))
                    (b* ((exact (+ (fp-arith-triple->rational x)
                                   (* (fp-arith-triple->rational y)
                                      (fp-arith-triple->rational z)))))
                      (if (equal 0 exact)
                          0
                        (+ exact
                           (* (expt 2 (- (rational-exponent exact) frac-size)) error)))))))

  (defret <fn>-when-exact
    (implies (and (integerp (* (expt 2 frac-size)
                               (rational-significand (+ (fp-arith-triple->rational x)
                                                        (* (fp-arith-triple->rational y)
                                                           (fp-arith-triple->rational z))))))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man x))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man y))
                  (unsigned-byte-p (+ 1 (acl2::pos-fix frac-size)) (fp-arith-triple->man z))
                  (posp frac-size))
             (equal error 0))))



(defsection fp-muladd-arith-round-of-left-normalize

  (encapsulate
    nil

    (local (defthmd fp-arith-triple->sign-by-rational-when-nan-nonzero
             (implies (not (equal (fp-arith-triple->man x) 0))
                      (equal (fp-arith-triple->sign x)
                             (bool->bit (< (fp-arith-triple->rational x) 0))))
             :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

    ;; (local (defthm fp-arith-triple->rational-0
    ;;          (implies (equal 0 (fp-arith-triple->man x))
    ;;                   (equal (fp-arith-triple->rational x) 0))
    ;;          :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

    (local (defthmd fp-arith-triple->rational-0-iff-man-0
             (iff (equal (fp-arith-triple->rational x) 0)
                  (equal 0 (fp-arith-triple->man x)))
             :hints (("Goal" :in-theory (enable fp-arith-triple->rational)))))

    (local (defthm sign-of-fp-add-core-naive-when-mantissa-0
             (b* (((fp-arith-triple sum)
                   (fp-add-core-naive x y rc))
                  ((fp-arith-triple x))
                  ((fp-arith-triple y)))
               (implies (equal sum.man 0)
                        (equal sum.sign
                               (if (equal x.sign y.sign)
                                   x.sign
                                 (bool->bit (eq (rc->rounding-mode rc) :rmi))))))
             :hints (("Goal" :in-theory (enable fp-add-core-naive)))))

    (defcong fp-arith-triple->rational-and-sign-equiv
      fp-arith-triple->rational-and-sign-equiv (fp-add-core-naive x y rc) 1
      :hints (("Goal"
               :in-theory (e/d (fp-arith-triple->rational-and-sign-equiv)
                               ())
               :use ((:instance fp-arith-triple->sign-by-rational-when-nan-nonzero
                                (x (fp-add-core-naive x y rc)))
                     (:instance fp-arith-triple->sign-by-rational-when-nan-nonzero
                                (x (fp-add-core-naive x-equiv y rc)))
                     (:instance fp-arith-triple->rational-0-iff-man-0
                                (x (fp-add-core-naive x y rc)))
                     (:instance fp-arith-triple->rational-0-iff-man-0
                                (x (fp-add-core-naive x-equiv y rc))))))
      :otf-flg t)

    (defcong fp-arith-triple->rational-and-sign-equiv
      fp-arith-triple->rational-and-sign-equiv (fp-add-core-naive x y rc) 2
      :hints (("Goal" :in-theory (e/d (fp-arith-triple->rational-and-sign-equiv)
                                      ())
               :use ((:instance fp-arith-triple->sign-by-rational-when-nan-nonzero
                                (x (fp-add-core-naive x y rc)))
                     (:instance fp-arith-triple->sign-by-rational-when-nan-nonzero
                                (x (fp-add-core-naive x y-equiv rc)))
                     (:instance fp-arith-triple->rational-0-iff-man-0
                                (x (fp-add-core-naive x y rc)))
                     (:instance fp-arith-triple->rational-0-iff-man-0
                                (x (fp-add-core-naive x y-equiv rc))))))
      :otf-flg t))

  (defcong fp-arith-triple->rational-and-sign-equiv
    fp-arith-triple->rational-and-sign-equiv (fp-mul-arith x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-mul-arith)))))

  (defcong fp-arith-triple->rational-and-sign-equiv
    fp-arith-triple->rational-and-sign-equiv (fp-mul-arith x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-mul-arith)))))

  (defcong fp-arith-triple->rational-and-sign-equiv
    fp-arith-triple->rational-and-sign-equiv (fp-muladd-arith-naive x y z rc) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-muladd-arith-naive)))))

  (defcong fp-arith-triple->rational-and-sign-equiv
    fp-arith-triple->rational-and-sign-equiv (fp-muladd-arith-naive x y z rc) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-muladd-arith-naive)))))

  (defcong fp-arith-triple->rational-and-sign-equiv
    fp-arith-triple->rational-and-sign-equiv (fp-muladd-arith-naive x y z rc) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable fp-muladd-arith-naive)))))

  (defthm fp-muladd-arith-round-of-left-normalize
    (b* (((fp-arith-triple a))
         ((fp-arith-triple b))
         ((fp-arith-triple c))
         (spec (fp-muladd-arith-round a b c rc frac-size))
         (norm (fp-muladd-arith-round
                (left-normalize-arith-triple a frac-size)
                (left-normalize-arith-triple b frac-size)
                (left-normalize-arith-triple c frac-size)
                rc frac-size)))
      (implies (and (unsigned-byte-p (1+ frac-size) a.man)
                    (unsigned-byte-p (1+ frac-size) b.man)
                    (unsigned-byte-p (1+ frac-size) c.man)
                    (posp frac-size))
               (equal norm spec)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-round))))

  (defthm fp-muladd-arith-round-of-left-normalize-a
    (b* (((fp-arith-triple a))
         ((fp-arith-triple b))
         ((fp-arith-triple c))
         (spec (fp-muladd-arith-round a b c rc frac-size))
         (norm (fp-muladd-arith-round
                (left-normalize-arith-triple a frac-size) b c
                rc frac-size)))
      (implies (and (unsigned-byte-p (1+ frac-size) a.man)
                    (unsigned-byte-p (1+ frac-size) b.man)
                    (unsigned-byte-p (1+ frac-size) c.man)
                    (posp frac-size))
               (equal norm spec)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-round))))

  (defthm fp-muladd-arith-round-of-left-normalize-b
    (b* (((fp-arith-triple a))
         ((fp-arith-triple b))
         ((fp-arith-triple c))
         (spec (fp-muladd-arith-round a b c rc frac-size))
         (norm (fp-muladd-arith-round
                a (left-normalize-arith-triple b frac-size) c
                rc frac-size)))
      (implies (and (unsigned-byte-p (1+ frac-size) a.man)
                    (unsigned-byte-p (1+ frac-size) b.man)
                    (unsigned-byte-p (1+ frac-size) c.man)
                    (posp frac-size))
               (equal norm spec)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-round))))

  (defthm fp-muladd-arith-round-of-left-normalize-c
    (b* (((fp-arith-triple a))
         ((fp-arith-triple b))
         ((fp-arith-triple c))
         (spec (fp-muladd-arith-round a b c rc frac-size))
         (norm (fp-muladd-arith-round
                a b (left-normalize-arith-triple c frac-size)
                rc frac-size)))
      (implies (and (unsigned-byte-p (1+ frac-size) a.man)
                    (unsigned-byte-p (1+ frac-size) b.man)
                    (unsigned-byte-p (1+ frac-size) c.man)
                    (posp frac-size))
               (equal norm spec)))
    :hints (("Goal" :in-theory (enable fp-muladd-arith-round)))))
