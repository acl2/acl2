; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../expr")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc interval-arithmetic
  :parents (lint)
  :short "A basic interval arithmetic package for integers, for use in
truncation/extension warnings."

  :long "<p>This is in many ways similar to the @('tau') book on elementary
bounders.  However, my goal here is simpler because I only care about integer
arithmetic.</p>")

(local (xdoc::set-default-parents interval-arithmetic))

(defprod interval
  ((low  integerp :rule-classes :type-prescription)
   (high integerp :rule-classes :type-prescription)))

(define in-interval ((a integerp)
                     (x interval-p))
  (b* (((interval x))
       (a (ifix a)))
    (and (<= x.low a)
         (<= a x.high))))

(local (in-theory (enable in-interval)))

(define interval-plus ((x interval-p)
                       (y interval-p))
  (b* (((interval x))
       ((interval y)))
    (make-interval
     ;; xl <= x, yl <= y --> xl+yl <= x+y
     :low  (+ x.low y.low)
     ;; x <= xh, y <= yh --> x+y <= xh+yh
     :high (+ x.high y.high)
     ))
  ///
  (defthm interval-plus-conservative
    (implies (and (in-interval a x)
                  (in-interval b y)
                  (integerp a)
                  (integerp b))
             (in-interval (+ a b) (interval-plus x y)))))

(define interval-minus ((x interval-p)
                        (y interval-p))
  (b* (((interval x))
       ((interval y)))
    (make-interval
     ;; x <= xh && yl <= y --> (x - y) <= xh - yl
     :high (- x.high y.low)
     ;; x <= xl && y <= yh --> (xl - yh) <= (x - y)
     :low  (- x.low y.high)))
  ///
  (defthm interval-minus-conservative
    (implies (and (in-interval a x)
                  (in-interval b y)
                  (integerp a)
                  (integerp b))
             (in-interval (- a b) (interval-minus x y)))))

(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(define interval-times ((x interval-p)
                        (y interval-p))
  (b* (((interval x))
       ((interval y)))

    (cond ((<= 0 x.low)
           ;; X is always positive.
           (cond ((<= 0 y.low)
                  ;; X and Y always positive.  Easy case.
                  (make-interval :low  (* x.low  y.low)
                                 :high (* x.high y.high)))
                 ((<= y.high 0)
                  ;; X always positive, Y always non-positive.
                  ;; Lower bound is "most negative" Y times biggest X.
                  ;; Upper bound is "least negative" Y times smallest X.
                  (make-interval :low  (* y.low  x.high)
                                 :high (* y.high x.low)))
                 (t
                  ;; Y can be positive or negative.
                  ;; Lower bound is "most negative" Y times biggest X.
                  ;; Upper bound is "most positive" Y times biggest X.
                  (make-interval :low  (* y.low  x.high)
                                 :high (* y.high x.high)))))

          ((<= x.high 0)
           ;; X is always non-positive.
           (cond ((<= 0 y.low)
                  ;; Y always positive, X always non-positive.
                  ;; Lower bound is "most negative" X times biggest Y
                  ;; Upper bound is "least negative" X times smallest Y.
                  (make-interval :low  (* x.low  y.high)
                                 :high (* x.high y.low)))

                 ((<= y.high 0)
                  ;; Y always non-positive, X always non-positive.
                  ;; The multiplication flips the sign to positive.
                  ;; Upper bound is "most negative" X times "most negative" Y.
                  ;; Lower bound is "least negative" X times "least negative" Y.
                  (make-interval :low (* x.high y.high)
                                 :high (* x.low y.low)))

                 (t
                  ;; Y can be positive or negative but X is always non-positive.
                  ;; Upper bound is "most negative" Y times "most negative" X.
                  ;; Lower bound is "most positive" Y times "most negative" X.
                  (make-interval :low  (* x.low y.high)
                                 :high (* x.low y.low)))))

          (t
           ;; X can be either positive or negative.
           (cond ((<= 0 y.low)
                  ;; Y is always positive
                  ;; Lower bound is "most negative" X times biggest Y.
                  ;; Upper bound is "most positive" X times biggest Y.
                  (make-interval :low (* x.low y.high)
                                 :high (* x.high y.high)))
                 ((<= y.high 0)
                  ;; Y is always non-positive but X can be positive or negative.
                  ;; Upper bound is "most negative" X times "most negative" Y.
                  ;; Lower bound is biggest X times "most negative" Y.
                  (make-interval :low  (* x.high y.low)
                                 :high (* x.low  y.low)))

                 (t
                  ;; X and Y can both be either positive or negative.
                  ;; Lower bound might be two things now.
                  ;;   Biggest X (positive) times Smallest Y (negative) is negative.
                  ;;   Biggest Y (positive) times Smallest X (negative) is negative.
                  ;; So whichever is smaller wins.
                  ;; Upper bound can similarly be two things:
                  ;;   Biggest X  (positive) times Biggest Y  (positive) is positive.
                  ;;   Smallest X (negative) times Smallest Y (negative) is positive.
                  ;; So whichever is bigger wins.
                  (make-interval :low (min (* y.low x.high)
                                           (* x.low y.high))
                                 :high (max (* x.high y.high)
                                            (* x.low  y.low)))
                  )))))
  ///
  (local (include-book "arithmetic-3/bind-free/top" :dir :system))

  (local (defthm h1
           (implies (AND (case-split (<= (* XH YH) (* XL YL)))
                         (<= XL A) (<= A XH)
                         (<= YL B) (<= B YH)
                         (< XL 0)
                         (< YL 0)
                         (INTEGERP A)
                         (INTEGERP B)
                         (integerp xl)
                         (integerp yl)
                         (integerp xh)
                         (integerp yh))
                    (<= (* A B) (* XL YL)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :nonlinearp t
                   :cases ((<= (* a b) (* xh yh)))))))

  (local (defthm h2
           (implies (AND (case-split (<= (* XL YL) (* XH YH)))
                         (<= XL A) (<= A XH)
                         (<= YL B) (<= B YH)
                         (< XL 0)
                         (< YL 0)
                         (INTEGERP A)
                         (INTEGERP B)
                         (integerp xl)
                         (integerp yl)
                         (integerp xh)
                         (integerp yh))
                    (<= (* A B) (* XH YH)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :nonlinearp t
                   :cases ((<= (* a b) (* xl yl)))))))

  (local (defthm l1
           (IMPLIES (AND (case-split (< (* XH YL) (* XL YH)))
                         (<= XL A) (<= A XH)
                         (<= YL B) (<= B YH)
                         (case-split (< 0 YH))
                         (case-split (< YL 0))
                         (INTEGERP A)
                         (INTEGERP B)
                         (integerp xl)
                         (integerp yl)
                         (integerp xh)
                         (integerp yh))
                    (<= (* XH YL) (* A B)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :nonlinearp t
                   :cases ((<= 0 a))))))

  (local (defthm l2
           (IMPLIES (AND (case-split (< (* XL YH) (* XH YL)))
                         (<= XL A) (<= A XH)
                         (<= YL B) (<= B YH)
                         (case-split (< 0 YH))
                         (case-split (< YL 0))
                         (INTEGERP A)
                         (INTEGERP B)
                         (integerp xl)
                         (integerp yl)
                         (integerp xh)
                         (integerp yh))
                    (<= (* XL YH) (* A B)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :nonlinearp t
                   :cases ((<= 0 a))))))

  (local (defthm goal2.1
           (IMPLIES (AND (< 0 B)
                         (<= (INTERVAL->LOW X) A)
                         (<= A (INTERVAL->HIGH X))
                         (<= (INTERVAL->LOW Y) B)
                         (<= B (INTERVAL->HIGH Y))
                         (INTEGERP A)
                         (INTEGERP B)
                         (< 0 (INTERVAL->HIGH X))
                         (< (INTERVAL->LOW Y) 0)
                         (< 0 (INTERVAL->HIGH Y))
                         (< (* (INTERVAL->HIGH X) (INTERVAL->LOW Y))
                            (* (INTERVAL->HIGH Y)
                               (INTERVAL->LOW X))))
                    (<= (* (INTERVAL->HIGH X) (INTERVAL->LOW Y))
                        (* A B)))
           :hints(("Goal"
                   :use ((:instance l1
                          (xh (interval->high x))
                          (yh (interval->high y))
                          (xl (interval->low x))
                          (yl (interval->low y))))))))

  (local (defthm goal4.2
           (IMPLIES (AND (< 0 A)
                         (<= (INTERVAL->LOW X) A)
                         (<= A (INTERVAL->HIGH X))
                         (<= (INTERVAL->LOW Y) B)
                         (<= B (INTERVAL->HIGH Y))
                         (INTEGERP A)
                         (INTEGERP B)
                         (< (INTERVAL->LOW X) 0)
                         (< 0 (INTERVAL->HIGH X))
                         (< 0 (INTERVAL->HIGH Y))
                         (<= (* (INTERVAL->HIGH Y) (INTERVAL->LOW X))
                             (* (INTERVAL->HIGH X)
                                (INTERVAL->LOW Y))))
                    (<= (* (INTERVAL->HIGH Y) (INTERVAL->LOW X))
                        (* A B)))
           :hints(("Goal"
                   :nonlinearp t
                   :cases ((<= 0 b))))))

  (defthm interval-times-conservative
    (implies (and (in-interval a x)
                  (in-interval b y)
                  (integerp a)
                  (integerp b))
             (in-interval (* a b)
                          (interval-times x y)))
    :hints(("Goal" :nonlinearp t)
           (and stable-under-simplificationp
                '(:nonlinearp t
                  :cases ((< 0 a) (< 0 b)))))))
