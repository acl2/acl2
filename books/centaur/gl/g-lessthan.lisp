; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(defun g-<-of-integers (a b)
  (declare (xargs :guard (and (general-integerp a)
                              (general-integerp b))))
  (mk-g-boolean (bfr-<-ss (general-integer-bits a)
                          (general-integer-bits b))))

(defthm deps-of-g-<-of-integers
  (implies (and (not (gobj-depends-on k p a))
                (not (gobj-depends-on k p b))
                (general-integerp a)
                (general-integerp b))
           (not (gobj-depends-on k p (g-<-of-integers a b)))))

(in-theory (disable (g-<-of-integers)))

(defthm g-<-of-integers-correct
     (implies (and (general-integerp a)
                   (general-integerp b))
              (equal (eval-g-base (g-<-of-integers a b) env)
                     (< (eval-g-base a env)
                        (eval-g-base b env))))
     :hints (("goal" :do-not-induct t
              :in-theory (e/d* ((:ruleset general-object-possibilities))))))

(local
 (encapsulate nil
   (local
    (defthm rationalp-complex
      (equal (rationalp (complex a b))
             (equal (rfix b) 0))
      :hints (("goal" :use ((:instance
                             (:theorem (implies (rationalp x)
                                                (equal (imagpart x) 0)))
                             (x (complex a b))))))))


   (defthm realpart-of-complex
     (equal (realpart (complex a b))
            (rfix a))
     :hints (("goal" :cases ((rationalp b)))))

   (defthm imagpart-of-complex
     (equal (imagpart (complex a b))
            (rfix b))
     :hints (("goal" :cases ((rationalp a)))))


   (defthm complex-<-1
     (equal (< (complex a b) c)
            (or (< (rfix a) (realpart c))
                (and (equal (rfix a) (realpart c))
                     (< (rfix b) (imagpart c)))))
     :hints (("goal" :use ((:instance completion-of-<
                            (x (complex a b)) (y c))))))


   (defthm complex-<-2
     (equal (< a (complex b c))
            (or (< (realpart a) (rfix b))
                (and (equal (realpart a) (rfix b))
                     (< (imagpart a) (rfix c)))))
     :hints (("goal" :use ((:instance completion-of-<
                            (x a) (y (complex b c)))))))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm foo
         (implies (and (< n d)
                       (natp n)
                       (posp d))
                  (< (/ n d) 1))
         :hints (("goal" :nonlinearp t))
         :rule-classes nil))

(local (defun nonnegative-integer-quotient-preserves-<-ind (x i j)
         (if (or (= (nfix j) 0) (< (ifix i) j))
             x
           (nonnegative-integer-quotient-preserves-<-ind (+ -1 x) (- i j) j))))

(local (defthm nonnegative-integer-quotient-preserves-<
         (implies (and (natp n)
                       (posp d)
                       (integerp x))
                  (iff (< (nonnegative-integer-quotient n d) x)
                       (< (/ n d) x)))
         :hints(("Goal" :in-theory (enable nonnegative-integer-quotient)
                 :induct (nonnegative-integer-quotient-preserves-<-ind x n d))
                (and stable-under-simplificationp
                     '(:nonlinearp t)))))

(local (defthm nonnegative-integer-quotient-preserves->
         (implies (and (natp n)
                       (posp d)
                       (integerp x))
                  (iff (< x (nonnegative-integer-quotient n d))
                       (if (integerp (/ n d))
                           (< x (/ n d))
                         (< x (+ -1 (/ n d))))))
         :hints(("Goal" :in-theory (enable nonnegative-integer-quotient)
                 :induct (nonnegative-integer-quotient-preserves-<-ind x n d))
                (and stable-under-simplificationp
                     '(:use foo
                       :in-theory (disable ACL2::<-*-/-LEFT-COMMUTED))))))

(local (defthm switch-minus-quotient
         (and (iff (< (- (nonnegative-integer-quotient n d)) x)
                   (> (nonnegative-integer-quotient n d) (- x)))
              (iff (> (- (nonnegative-integer-quotient n d)) x)
                   (< (nonnegative-integer-quotient n d) (- x))))))

(local (defthm switch-quotient+1
         (and (iff (< (+ 1 (nonnegative-integer-quotient n d)) x)
                   (< (nonnegative-integer-quotient n d) (+ -1 x)))
              (iff (> (+ 1 (nonnegative-integer-quotient n d)) x)
                   (> (nonnegative-integer-quotient n d) (+ -1 x))))))



(local (defthm switch-quotient-minus1
         (and (iff (< (+ -1 (- (nonnegative-integer-quotient n d))) x)
                   (> (nonnegative-integer-quotient n d) (- (+ 1 x))))
              (iff (> (+ -1 (- (nonnegative-integer-quotient n d))) x)
                   (< (nonnegative-integer-quotient n d) (- (+ 1 x)))))))

(defun ceil (x)
  (declare (xargs :guard (acl2-numberp x)))
  (if (integerp (realpart x))
      (if (< 0 (imagpart x))
          (+ 1 (realpart x))
        (realpart x))
    (ceiling (realpart x) 1)))

(local (defthm <-of-ceil
         (implies (and (integerp x))
                  (equal (< x (ceil y))
                         (< x y)))
         :hints (("goal" :use completion-of-<))))

(defun flo (x)
  (declare (xargs :guard (acl2-numberp x)))
  (if (integerp (realpart x))
      (if (< (imagpart x) 0)
          (+ -1 (realpart x))
        (realpart x))
    (floor (realpart x) 1)))

(local (defthm <-of-flo
         (implies (and (integerp y))
                  (equal (< (flo x) y)
                         (< x y)))
         :hints (("goal" :use completion-of-<))))


(in-theory (disable g-<-of-integers))

(def-g-binary-op <
  (b* ((x (general-number-fix x))
       (y (general-number-fix y))
       (x-concretep (general-concretep x))
       (y-concretep (general-concretep y))
       ((when (and** x-concretep y-concretep)) (gret (ec-call (< (general-concrete-obj x)
                                                               (general-concrete-obj y)))))
       ((when (and** (not x-concretep) (not y-concretep)))
        (gret (g-<-of-integers x y)))
       (xval (if x-concretep (flo (general-concrete-obj x)) x))
       (yval (if y-concretep (ceil (general-concrete-obj y)) y)))
    (gret (g-<-of-integers xval yval))))

;; (def-gobjectp-thm <
;; :hints `(("Goal" :in-theory (e/d* (booleanp-gobjectp
;;                                    boolean-listp-bfr-listp
;;                                    gobjectp-of-atomic-constants)
;;                                   ((:definition ,gfn)
;;                                    integer-to-components
;;                                    general-concretep-def
;;                                    gobj-fix-when-not-gobjectp
;;                                    gobj-fix-when-gobjectp
;;                                    booleanp-gobjectp
;;                                    (:ruleset gl-wrong-tag-rewrites)
;;                                    (:rules-of-class :type-prescription :here)))
;;           :induct (,gfn x y hyp clk)
;;           :expand ((,gfn x y hyp clk)))))

; (local (in-theory (disable general-concrete-obj-when-atom)))
(local (in-theory (disable flo ceil)))

(verify-g-guards
 < :hints `(("Goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                     (,gfn general-concretep-def)))))

;; (local (defthm general-integerp-when-no-other-possibilities
;;          (implies (and (not (equal (tag x) :g-ite))
;;                        (not (equal (tag x) :g-var))
;;                        (not (equal (tag x) :g-apply))
;;                        (not (general-concretep x))
;;                        (not (general-consp x))
;;                        (not (general-booleanp x)))
;;                   (general-integerp x))
;;          :hints(("Goal" :in-theory (enable* (:ruleset general-object-possibilities))))))

(def-gobj-dependency-thm <
  :hints `(("goal" :induct ,gcall
            :expand (,gcall))))

(local (defcong number-equiv equal (< a b) 1))
(local (defcong number-equiv equal (< a b) 2))

(local (defthm integerp-of-eval-g-base-when-general-number-fix-not-concrete
         (implies (not (general-concretep (general-number-fix x)))
                  (integerp (eval-g-base x env)))
         :hints(("Goal" :in-theory (enable general-number-fix)
                 :expand ((:with eval-g-base (eval-g-base x env)))))))
                       

(def-g-correct-thm < eval-g-base
  :hints `(("Goal" :in-theory (e/d* (;; (:ruleset general-object-possibilities)
                                     eval-g-base-list)
                                    ;; ((:definition ,gfn)
                                    ;;  (:rules-of-class :type-prescription :here)
                                    ;;  general-concretep-def
                                    ;;  ; eval-g-base-alt-def
                                    ;;  ;; eval-g-base-non-cons
                                    ;;  acl2::/r-when-abs-numerator=1
                                    ;;  default-unary-/
                                    ;;  default-car default-cdr
                                    ;;  hons-assoc-equal)
                                    ;; ((:t ceil) (:t flo)
                                    ;;  (:t bfr-list->s)
                                    ;;  general-consp-implies-eval-g-base
                                    ;;  (:t bfr-eval)
                                    ;;  general-concrete-obj-when-atom
                                    ;;  )
                                    )
            :induct ,gcall
            :expand (,gcall))))
