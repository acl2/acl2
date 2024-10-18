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






(local (defthm sign-0-implies-rational
         (implies (equal (fp-arith-triple->sign x) 0)
                  (<= 0 (fp-arith-triple->rational x)))
         :hints(("Goal" :in-theory (enable fp-arith-triple->rational)))
         :rule-classes :forward-chaining))

(local (defthm sign-1-implies-rational
         (implies (equal (fp-arith-triple->sign x) 1)
                  (<= (fp-arith-triple->rational x) 0))
         :hints(("Goal" :in-theory (enable fp-arith-triple->rational)))
         :rule-classes :forward-chaining))


(local (defund norm-exp (x size)
         (b* (((fp-arith-triple x))
              ((fp-size size)))
           (+ x.exp (- (integer-length x.man) (+ 2 size.frac-size))))))



(local
 (defthm normalize-round+sticky-value-decomp-in
   (b* (((mv (fp-arith-triple norm) & &)
         (normalize-arith-triple x))
        ((fp-arith-triple x))
        ((fp-size size))
        (round+sticky (normalize-arith-triple-round+sticky x size.frac-size)))
     (implies (and (syntaxp (equal x 'in)))
              (equal (fp-arith-triple->rational x)
                     (* (fp-sign-value x.sign)
                        (* (expt 2 (norm-exp x size))
                           (+ round+sticky (* 2 norm.man)))))))
   :hints(("Goal" :use normalize-round+sticky-value-decomp
           :in-theory (enable norm-exp)))))


(local (defthmd normalize-integer-length-in
         (implies (And (syntaxp (equal in 'in))
                       (bind-free '((size . size)) (size)))
                  (equal (integer-length (fp-arith-triple->man in))
                         (+ 2
                            (norm-exp in size)
                            (- (fp-arith-triple->exp in))
                            (fp-size->frac-size size))))
         :hints(("Goal" :in-theory (enable norm-exp)))))

(local (defthm integer-length-positive-forward
         (implies (posp (integer-length x))
                  (not (zip x)))
         :rule-classes ((:forward-chaining :trigger-terms ((integer-length x))))))


;; (local (defthm within-same-expt-means-at-most-double
;;          (implies (and (<= (expt 2 f) x)
;;                        ;; (<= x (+ -1 (* 2 (expt 2 f))))
;;                        ;; (<= (expt 2 f) y)
;;                        (<= y (+ -1 (* 2 (expt 2 f))))
;;                        (integerp x)
;;                        (integerp y)
;;                        (integerp f))
;;                   (< y (* 2 x)))
;;          :rule-classes nil))

(local (defthm expt-2-when-less-than-neg1
         (implies (and (< exp -1)
                       (integerp exp))
                  (<= (expt 2 exp) 1/4))
         :hints (("goal" :use ((:instance ACL2::EXPT-IS-weakly-INCREASING-FOR-BASE>1
                                (r 2) (i exp) (j -2)))
                  :in-theory (disable acl2::expt-is-weakly-increasing-for-base>1)))
         :rule-classes :linear))

(local (defthm exponent-possibilities-within-half-ulp-rel-lemma
         (IMPLIES (AND 
                   ;; (>= (expt 2 exp-diff) 4)
                   (<= 2 (expt 2 frac-size))
                   (< 0 spec.man)
                   (< spec.man (* 2 approx.man))
                   (< approx.man (* 2 spec.man))
                   (< (abs (- (* (/ spec.man) approx.man (expt 2 exp-diff)) 1))
                      (expt 2 (+ (- frac-size) -2)))
                   (NOT (ZP FRAC-SIZE))
                   (INTEGERP exp-diff)
                   ;; (INTEGERP SPEC.EXP)
                   (rationalp APPROX.MAN)
                   (INTEGERP SPEC.MAN))
                  (or (equal exp-diff -1)
                      (equal exp-diff 0)
                      (equal exp-diff 1)))
         :hints (("goal" :in-theory (enable acl2::multiply-out-<))
                 '(:cases ((< exp-diff -1)
                           (> exp-diff 1)))
                 (and stable-under-simplificationp
                      '(:nonlinearp t)))
         :otf-flg t
         :rule-classes nil))


(local (defthm exponent-possibilities-within-half-ulp-rel
         (b* ((spec-val (* (expt 2 spec.exp) spec.man))
              (approx-val (* (expt 2 approx.exp) approx.man)))
           (implies (and (<= (expt 2 frac-size) spec.man)
                         (<= spec.man (+ -1 (* 2 (expt 2 frac-size))))
                         (<= (expt 2 frac-size) approx.man)
                         (< approx.man (* 2 (expt 2 frac-size)))
                         (< (abs (- (/ approx-val spec-val) 1)) (expt 2 (+ (- frac-size) -2)))
                         (posp frac-size)
                         (integerp approx.exp)
                         (integerp spec.exp)
                         (rationalp approx.man)
                         (natp spec.man))
                    (or (equal approx.exp (+ -1 spec.exp))
                        (equal approx.exp spec.exp)
                        (equal approx.exp (+ 1 spec.exp)))))
         :hints(("Goal" :use ((:instance exponent-possibilities-within-half-ulp-rel-lemma
                               (exp-diff (- approx.exp spec.exp))))))
         :otf-flg t
         :rule-classes nil))


(local (defthm sign-possibities-within-half-ulp-rel
         (implies (and (rationalp in-val)
                       (rationalp spec-val)
                       (posp frac-size)
                       (< (abs (- (/ in-val spec-val) 1))
                          (expt 2 (+ (- frac-size) -2))))
                  (and (iff (< 0 in-val)
                            (< 0 spec-val))
                       (not (equal 0 in-val))
                       (not (equal 0 spec-val))))
         :hints ((and stable-under-simplificationp
                      '(:nonlinearp t)))
         :rule-classes nil))

(defthmd fp-arith-triple-sign-bit-possibilities-within-half-ulp-rel
  (b* ((in-val (fp-arith-triple->rational in))
       (spec-val (fp-arith-triple->rational spec)))
    (implies (and (posp frac-size)
                  (< (abs (- (/ in-val spec-val) 1))
                     (expt 2 (+ (- frac-size) -2))))
             (and (equal (fp-arith-triple->sign in)
                         (fp-arith-triple->sign spec))
                  (not (equal 0 (fp-arith-triple->man in)))
                  (not (equal 0 (fp-arith-triple->man spec))))))
  :hints (("goal" :use ((:instance sign-possibities-within-half-ulp-rel
                         (in-val (fp-arith-triple->rational in))
                         (spec-val (fp-arith-triple->rational spec))))
           :in-theory (enable fp-arith-triple->rational
                              fp-sign-value-redef))))




;; (local (defthm exponent-possibilities
;;          (b* ((in-val (fp-arith-triple->rational in))
;;               ((fp-arith-triple spec))
;;               (spec-val (fp-arith-triple->rational spec))
;;               ((fp-size size)))
;;            (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
;;                          (< 0 in-val)
;;                          (< in-val spec-val)
;;                          ;; relative error is < 2^(-f-2)
;;                          (< (abs (- (/ in-val spec-val) 1))
;;                             (expt 2 (+ (- (fp-size->frac-size size)) -2))))
;;                     (or (equal (norm-exp in size) spec.exp)
;;                         (equal (norm-exp in size) (+ -1 spec.exp))
;;                         (equal (norm-exp in size) (+ 1 spec.exp)))))
;;          :hints (("goal" :use ((:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
;;                                 (r 2)
;;                                 (i (norm-exp in size)) (j (+ -1 (fp-arith-triple->exp spec))))
;;                                (:instance ACL2::EXPT-IS-INCREASING-FOR-BASE>1
;;                                 (r 2)
;;                                 (j (norm-exp in size)) (i (+ 1 (fp-arith-triple->exp spec)))))
;;                   :expand ((fp-arith-triple->rational spec))

;;                   :in-theory (e/d (normalize-in-terms-of-round+sticky
;;                                    fp-sign-value-redef
;;                                    acl2::multiply-out-<
;;                                    equal-integer-length-of-positive
;;                                    acl2::exponents-add-unrestricted
;;                                    acl2::multiply-out-<)
;;                                   (acl2::expt-is-increasing-for-base>1)))
;;                  (and stable-under-simplificationp
;;                       '(:nonlinearp t)))))

(local (defthm rewrite-norm-exp-by-plus-1-value
         (implies (equal (+ 1 (norm-exp x size)) y)
                  (equal (norm-exp x size)
                         (+ -1 y)))))

(local (defthm crock1
         (implies (and (<= norm (+ -1 vman))
                       (not (< 1 r+s))
                       (<= vman (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (>= (+ (* 4 vman e2f)
                         (- (* 2 e2f r+s))
                         (- (* 4 e2f norm)))
                      vman))
         :hints (("goal" :nonlinearp t))))

;; (local (defthm crock11
;;          (implies (and (<= 0 r+s)
;;                        (<= e2f norm)
;;                        (<= norm (+ -1 vman))
;;                        (integerp norm)
;;                        (integerp vman)
;;                        (posp e2f)
;;                        (rationalp r+s))
;;                   (>= (+ (* 4 vman e2f)
;;                          (* 2 e2f r+s)
;;                          (* 4 e2f norm))
;;                       vman))
;;          :hints (("goal" :nonlinearp t))))

(local (defthm crock2
         (implies (and (<= norm (+ -1 (* 2 vman)))
                       (not (< 1 r+s))
                       (<= norm (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (and (>= (+ (* 4 vman e2f)
                              (- (* e2f r+s))
                              (- (* 2 e2f norm)))
                           vman)))
         :hints (("goal" :nonlinearp t))))

;; (local (defthm crock21
;;          (implies (and (<= 0 r+s)
;;                        (<= e2f norm)
;;                        (<= norm (+ -1 (* 2 vman)))
;;                        (integerp norm)
;;                        (integerp vman)
;;                        (posp e2f)
;;                        (rationalp r+s))
;;                   (>= (+ (* 4 vman e2f)
;;                          (* e2f r+s)
;;                          (* 2 e2f norm))
;;                       vman))
;;          :hints (("goal" :nonlinearp t))))


;; (local (defthm crock-man-zero
;;          (implies (and (<= e2f vman)
;;                        (<= vman (+ -1 (* 2 e2f))))
;;                   (<= 




(local
 (defthm round-arith-triple-of-normalize-exact-when-exact-triple-exists-lesser-implies-round-sticky
   (b* ((in-val (fp-arith-triple->rational in))
        ((fp-arith-triple spec))
        (spec-val (fp-arith-triple->rational spec))
        ((fp-size size)))
     (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
                   ;; (< 0 in-val)
                   (< (abs in-val) (abs spec-val))
                   ;; relative error is < 2^(-f-2)
                   (< (abs (- (/ in-val spec-val) 1))
                      (expt 2 (+ (- (fp-size->frac-size size)) -2))))
              (< 1 (normalize-arith-triple-round+sticky in (fp-size->frac-size size)))))
   :hints (("goal" :in-theory (enable normalize-in-terms-of-round+sticky
                                      fp-sign-value-redef
                                      acl2::multiply-out-<
                                      equal-integer-length-of-positive)
            :use ((:instance fp-arith-triple-sign-bit-possibilities-within-half-ulp-rel
                   (frac-size (fp-size->frac-size size))))
            :expand ((fp-arith-triple->rational spec)))
           ;; (acl2::use-termhint
           ;;  (if (equal (fp-arith-triple->man in) 0)
           ;;      '(:in-theory (enable normalize-arith-triple-round+sticky-when-0
           ;;                           normalize-arith-triple
           ;;                           acl2::divide-out-common-factors-<))
           (and stable-under-simplificationp
                '(:use ((:instance exponent-possibilities-within-half-ulp-rel
                         (spec.man (fp-arith-triple->man spec))
                         (spec.exp (fp-arith-triple->exp spec))
                         (approx.man (b* (((mv norm & &)
                                           (normalize-arith-triple in))
                                          (round+sticky (normalize-arith-triple-round+sticky
                                                         in (fp-size->frac-size size))))

                                       (+ (fp-arith-triple->man norm)
                                          (* 1/2 round+sticky))))
                         (approx.exp (+ 1 (norm-exp in size)))
                         (frac-size (fp-size->frac-size size))))
                  :in-theory (enable acl2::exponents-add-unrestricted
                                     acl2::multiply-out-<
                                     acl2::divide-out-common-factors-<)))
           ;; (and stable-under-simplificationp
           ;;      '(:nonlinearp t))
           )
   :otf-flg t))


(local (defthm crock3
         (implies (and (<= norm (+ -2 vman))
                       ;; (not (equal (+ 1 norm) vman))
                       ;; (< 1 r+s)
                       (< r+s 2)
                       ;; (<= e2f vman)
                       ;; (<= vman (+ -1 (* 2 e2f)))
                       ;; (<= e2f norm)
                       (<= norm (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (not (< (+ (* 4 vman e2f)
                             (- (* 2 e2f r+s))
                             (- (* 4 e2f norm)))
                          vman)))
         :hints (("goal" :nonlinearp t))))

(local (defthm crock4
         (implies (and (<= norm (+ -2 (* 2 vman)))
                       ;; (not (equal (+ 1 norm) vman))
                       ;; (< 1 r+s)
                       (< r+s 2)
                       ;; (<= e2f vman)
                       ;; (<= vman (+ -1 (* 2 e2f)))
                       ;; (<= e2f norm)
                       (<= norm (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (not (< (+ (* 4 vman e2f)
                             (- (* e2f r+s))
                             (- (* 2 e2f norm)))
                          vman)))
         :hints (("goal" :nonlinearp t))))

(local
 (defret round-arith-triple-of-normalize-exact-when-exact-triple-exists-lesser-implies-round-is-exact
   :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in))
              ((mv round & &) (round-arith-triple x roundp stickyp rc))
              (in-val (fp-arith-triple->rational in))
              ((fp-arith-triple spec))
              (spec-val (fp-arith-triple->rational spec))
              ((fp-size size))
              (round-val (fp-arith-triple->rational round)))
   (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
                 ;; (< 0 in-val)
                 (< (abs in-val) (abs spec-val))
                 ;; relative error is < 2^(-f-2)
                 (< (abs (- (/ in-val spec-val) 1))
                    (expt 2 (+ (- (fp-size->frac-size size)) -2)))
                 (Eq (rc->rounding-mode rc) :rne))
            (equal round-val spec-val))
   :hints (("goal" :in-theory (enable fp-sign-value-redef
                                      acl2::multiply-out-<
                                      equal-integer-length-of-positive
                                      normalize-integer-length-in
                                      round-nearest-in-terms-of-round+sticky)
            :use (round-arith-triple-of-normalize-exact-when-exact-triple-exists-lesser-implies-round-sticky
                  (:instance fp-arith-triple-sign-bit-possibilities-within-half-ulp-rel
                   (frac-size (fp-size->frac-size size))))
            :expand ((fp-arith-triple->rational spec)))
           ;; '(:cases ((equal (fp-arith-triple->man in) 0)))
           ;; Split into cases on exponent
           ;; (acl2::use-termhint
           ;;  (if (equal (fp-arith-triple->man in) 0)
           ;;      '(:in-theory (enable normalize-arith-triple-round+sticky-when-0
           ;;                           normalize-arith-triple
           ;;                           acl2::divide-out-common-factors-<))
           (and stable-under-simplificationp
                '(:use ((:instance exponent-possibilities-within-half-ulp-rel
                         (spec.man (fp-arith-triple->man spec))
                         (spec.exp (fp-arith-triple->exp spec))
                         (approx.man (b* (((mv norm & &)
                                           (normalize-arith-triple in))
                                          (round+sticky (normalize-arith-triple-round+sticky
                                                         in (fp-size->frac-size size))))

                                       (+ (fp-arith-triple->man norm)
                                          (* 1/2 round+sticky))))
                         (approx.exp (+ 1 (norm-exp in size)))
                         (frac-size (fp-size->frac-size size))))
                  :expand ((:free (sign exp man) (FP-ARITH-TRIPLE->RATIONAL (fp-arith-triple sign exp man))))
                  :in-theory (enable acl2::exponents-add-unrestricted
                                     acl2::multiply-out-<
                                     acl2::divide-out-common-factors-equal
                                     acl2::divide-out-common-factors-<))))
   :otf-flg t
   :fn round-arith-triple))


(local (defthm crock5
         (implies (and (<= vman norm)
                       (not (< r+s 1))
                       (<= vman (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (>= (+ (- (* 4 vman e2f))
                         (* 2 e2f r+s)
                         (* 4 e2f norm))
                      vman))
         :hints (("goal" :nonlinearp t))))

;; (local (defthm crock51
;;          (implies (and (not (< r+s 1))
;;                        (<= e2f norm)
;;                        (<= e2f vman)
;;                        (integerp norm)
;;                        (integerp vman)
;;                        (posp e2f)
;;                        (rationalp r+s))
;;                   (>= (+ (* 4 vman e2f)
;;                          (* 2 e2f r+s)
;;                          (* 4 e2f norm))
;;                       vman))
;;          :hints (("goal" :nonlinearp t))))

(local (defthm crock6
         (implies (and (not (< r+s 1))
                       (<= e2f norm)
                       (<= vman (+ -1 (* 2 e2f)))
                       (integerp norm)
                       (integerp vman)
                       (posp e2f)
                       (rationalp r+s))
                  (>= (+ (- (* 4 vman e2f))
                         (* 4 e2f r+s)
                         (* 8 e2f norm))
                      vman))
         :hints (("goal" :nonlinearp t))))

;; (local (defthm crock61
;;         (implies (and (< vman (+ r+s (* 2 norm)))
;;                       (< r+s 2)
;;                       (<= e2f vman)
;;                        (<= vman (+ -1 (* 2 e2f)))
;;                        (integerp norm)
;;                        (integerp vman)
;;                        (posp e2f)
;;                        (rationalp r+s))
;;                   (>= (+ (* 4 vman e2f)
;;                          (* 4 e2f r+s)
;;                          (* 8 e2f norm))
;;                       vman))
;;          :hints (("goal" :nonlinearp t))))

(local
 (defthm round-arith-triple-of-normalize-exact-when-exact-triple-exists-greater-implies-round-sticky
   (b* ((in-val (fp-arith-triple->rational in))
        ((fp-arith-triple spec))
        (spec-val (fp-arith-triple->rational spec))
        ((fp-size size)))
     (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
                   ;; (< 0 in-val)
                   (>= (abs in-val) (abs spec-val))
                   ;; relative error is < 2^(-f-2)
                   (< (abs (- (/ in-val spec-val) 1))
                      (expt 2 (+ (- (fp-size->frac-size size)) -2))))
              (> 1 (normalize-arith-triple-round+sticky in (fp-size->frac-size size)))))
   :hints (("goal" :in-theory (enable normalize-in-terms-of-round+sticky
                                      fp-sign-value-redef
                                      acl2::multiply-out-<
                                      equal-integer-length-of-positive)
            :use ((:instance fp-arith-triple-sign-bit-possibilities-within-half-ulp-rel
                   (frac-size (fp-size->frac-size size))))
            :expand ((fp-arith-triple->rational spec)))
           ;; (acl2::use-termhint
           ;;  (if (equal (fp-arith-triple->man in) 0)
           ;;      '(:in-theory (enable normalize-arith-triple-round+sticky-when-0
           ;;                           normalize-arith-triple
           ;;                           acl2::divide-out-common-factors-<))
           (and stable-under-simplificationp
                '(:use ((:instance exponent-possibilities-within-half-ulp-rel
                         (spec.man (fp-arith-triple->man spec))
                         (spec.exp (fp-arith-triple->exp spec))
                         (approx.man (b* (((mv norm & &)
                                           (normalize-arith-triple in))
                                          (round+sticky (normalize-arith-triple-round+sticky
                                                         in (fp-size->frac-size size))))

                                       (+ (fp-arith-triple->man norm)
                                          (* 1/2 round+sticky))))
                         (approx.exp (+ 1 (norm-exp in size)))
                         (frac-size (fp-size->frac-size size))))
                  :in-theory (enable acl2::exponents-add-unrestricted
                                     acl2::multiply-out-<
                                     acl2::divide-out-common-factors-<)))
           ;; (and stable-under-simplificationp
           ;;      '(:nonlinearp t))
           )
   :otf-flg t))

;; (local (thm
;;           (implies (and (< r+s 1)
;;                         (<= 0 r+s)
;;                         (<= e2f vman)
;;                         (<= vman (+ -1 (* 2 e2f)))
;;                         (<= e2f norm)
;;                         (<= norm (+ -1 (* 2 e2f)))
;;                         (< vman (+ r+s (* 2 norm)))
;;                         (not (equal vman (* 2 norm)))
;;                         (integerp norm)
;;                         (integerp vman)
;;                         (posp e2f)
;;                         (rationalp r+s))
;;                    (>= (+ (- (* 4 vman e2f))
;;                           (* 4 e2f r+s)
;;                           (* 8 e2f norm))
;;                        vman))
;;           :hints (("goal" ;; :in-theory (disable ACL2::|x < y  =>  0 < -x+y|
;;                           ;;                     acl2::posp-redefinition)
;;                    :nonlinearp t))))

; (local (in-theory (disable (tau-system))))
(local (defthm crock7
         (implies (and ; (< r+s 1)
                   (<= 0 r+s)
; (<= e2f vman)
;(<= vman (+ -1 (* 2 norm)))
                   (<= vman (+ -1 (* 2 e2f)))
                   (<= e2f norm)
;(<= norm (+ -1 (* 2 e2f)))
;  (< vman (+ r+s (* 2 norm)))
                   ;; (not (equal vman (* 2 norm)))
                   (integerp norm)
                   (integerp vman)
                   (posp e2f)
                   (rationalp r+s))
                  (>= (+ (- (* 4 vman e2f))
                         (* 4 e2f r+s)
                         (* 8 e2f norm))
                      vman))
         :hints (("goal" :nonlinearp t))))

(local (defthm crock8
         (implies (and ; (< r+s 1)
                   (<= 0 r+s)
; (<= e2f vman)
; (<= vman (+ -1 (* 2 e2f)))
; (<= e2f norm)
                   (<= norm (+ -1 (* 2 e2f)))
                   (integerp norm)
                   (integerp vman)
                   (posp e2f)
                   (rationalp r+s)
                   ;; (< vman (+ (* 1/2 r+s) norm))
                   ;; (not (equal vman norm))
                   (<= vman (+ -1 norm))
                   )
                  (>= (+ (- (* 4 vman e2f))
                         (* 2 e2f r+s)
                         (* 4 e2f norm))
                      vman))
         :hints (("goal" :nonlinearp t))))



(local (in-theory (disable FP-ARITH-TRIPLE->RATIONAL-OF-NORMALIZE-ARITH-TRIPLE-WHEN-NOT-STICKY)))

(local
 (defret round-arith-triple-of-normalize-exact-when-exact-triple-exists-greater-implies-round-is-exact
   :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in))
              ((mv round & &) (round-arith-triple x roundp stickyp rc))
              (in-val (fp-arith-triple->rational in))
              ((fp-arith-triple spec))
              (spec-val (fp-arith-triple->rational spec))
              ((fp-size size))
              (round-val (fp-arith-triple->rational round)))
   (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
                 ;; (< 0 in-val)
                 (>= (abs in-val) (abs spec-val))
                 ;; relative error is < 2^(-f-2)
                 (< (abs (- (/ in-val spec-val) 1))
                    (expt 2 (+ (- (fp-size->frac-size size)) -2)))
                 (Eq (rc->rounding-mode rc) :rne))
            (equal round-val spec-val))
   :hints (("goal" :in-theory (enable fp-sign-value-redef
                                      acl2::multiply-out-<
                                      equal-integer-length-of-positive
                                      normalize-integer-length-in
                                      round-nearest-in-terms-of-round+sticky)
            :use (round-arith-triple-of-normalize-exact-when-exact-triple-exists-greater-implies-round-sticky
                  (:instance fp-arith-triple-sign-bit-possibilities-within-half-ulp-rel
                   (frac-size (fp-size->frac-size size))))
            :expand ((fp-arith-triple->rational spec)))
           ;; (acl2::use-termhint
           ;;  (if (equal (fp-arith-triple->man in) 0)
           ;;      '(:in-theory (enable normalize-arith-triple-round+sticky-when-0
           ;;                           normalize-arith-triple
           ;;                           acl2::divide-out-common-factors-<))
           (and stable-under-simplificationp
                '(:use ((:instance exponent-possibilities-within-half-ulp-rel
                         (spec.man (fp-arith-triple->man spec))
                         (spec.exp (fp-arith-triple->exp spec))
                         (approx.man (b* (((mv norm & &)
                                           (normalize-arith-triple in))
                                          (round+sticky (normalize-arith-triple-round+sticky
                                                         in (fp-size->frac-size size))))

                                       (+ (fp-arith-triple->man norm)
                                          (* 1/2 round+sticky))))
                         (approx.exp (+ 1 (norm-exp in size)))
                         (frac-size (fp-size->frac-size size))))
                  :expand ((:free (sign exp man) (FP-ARITH-TRIPLE->RATIONAL
                                                  (mv-nth 0 (normalize-arith-triple in :verbosep nil)))))
                  :in-theory (enable acl2::exponents-add-unrestricted
                                     acl2::multiply-out-<
                                     normalize-integer-length-in
                                     ;; normalize-in-terms-of-round+sticky
                                     acl2::divide-out-common-factors-equal
                                     acl2::divide-out-common-factors-<))))
; :otf-flg t
   :fn round-arith-triple))


(defret round-arith-triple-of-normalize-exact-when-exact-triple-exists-implies-round-is-exact
  :pre-bind (((mv x roundp stickyp) (normalize-arith-triple in))
             ((mv round & &) (round-arith-triple x roundp stickyp rc))
             (in-val (fp-arith-triple->rational in))
             ((fp-arith-triple spec))
             (spec-val (fp-arith-triple->rational spec))
             ((fp-size size))
             (round-val (fp-arith-triple->rational round)))
  (implies (and (equal (integer-length spec.man) (+ 1 size.frac-size))
                ;; relative error is < 2^(-f-2)
                (< (abs (- (/ in-val spec-val) 1))
                   (expt 2 (+ (- (fp-size->frac-size size)) -2)))
                (Eq (rc->rounding-mode rc) :rne))
           (equal round-val spec-val))
  :hints (("goal" :use (round-arith-triple-of-normalize-exact-when-exact-triple-exists-greater-implies-round-is-exact
                        round-arith-triple-of-normalize-exact-when-exact-triple-exists-lesser-implies-round-is-exact)))
; :otf-flg t
  :fn round-arith-triple)


