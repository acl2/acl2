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
;(include-book "tools/with-arith5-help" :dir :system)

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "clause-processors/just-expand" :dir :system))
;(local (allow-arith5-help))

;; (include-book "univ-gl-eval")

(local (defthm equal-complexes-rw
         (implies (and (acl2-numberp x)
                       (rationalp a)
                       (rationalp b))
                  (equal (equal (complex a b) x)
                         (and (equal a (realpart x))
                              (equal b (imagpart x)))))
         :hints (("goal" :use ((:instance realpart-imagpart-elim))))))

(defun g-binary-+-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (equal xrd '(t))
             (equal yrd '(t))
             (equal xid '(t))
             (equal yid '(t)))
        (let* ((rsum (bfr-+-ss nil xrn yrn))
               (isum (bfr-+-ss nil xin yin)))
          (mk-g-number (list-fix rsum)
                       1
                       (list-fix isum)))
      (g-apply 'binary-+ (gl-list x y)))))

(in-theory (disable (g-binary-+-of-numbers)))


(local (defthmd bfr-eval-list-when-boolean-listp
         (implies (boolean-listp x)
                  (equal (bfr-eval-list x env)
                         x))))

;; (local (defthm rewrite-v2i-of-boolean-list
;;          (implies (and (syntaxp (not (and (consp x)
;;                                           (eq (car x) 'bfr-eval-list))))
;;                        (bind-free '((env . (car env))) (env))
;;                        (boolean-listp x))
;;                   (equal (v2i x)
;;                          (bfr-list->s x env)))
;;          :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm rewrite-v2n-of-boolean-list
;;          (implies (and (syntaxp (not (and (consp x)
;;                                           (eq (car x) 'bfr-eval-list))))
;;                        (bind-free '((env . (car env))) (env))
;;                        (boolean-listp x))
;;                   (equal (v2n x)
;;                          (bfr-list->u x env)))
;;          :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (defthm bfr-eval-list-of-bfr-ite-bvv-fn-unde
;;   (equal (bfr-list->u (bfr-ite-bvv-fn c a b) env)
;;          (if (bfr-eval c env)
;;              (bfr-list->u a env)
;;            (bfr-list->u b env))))
;;   :hints(("Goal" :in-theory (enable bfr-ite-bvv-fn v2n)
;;           :induct t)
;;          (bfr-reasoning)))


(local
 (defthm g-binary-+-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-binary-+-of-numbers x y) env)
                   (+ (eval-g-base x env)
                      (eval-g-base y env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-numberp
                                     general-number-components))
            :do-not-induct t))))

(local
 (defthm dependencies-of-g-binary-+-of-numbers
   (implies (and (general-numberp x)
                 (general-numberp y)
                 (not (gobj-depends-on n p x))
                 (not (gobj-depends-on n p y)))
            (not (gobj-depends-on n p (g-binary-+-of-numbers x y))))
   :hints (("goal" :do-not-induct t))
   :otf-flg t))

(in-theory (disable g-binary-+-of-numbers))

(def-g-binary-op binary-+
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (gret (g-binary-+-of-numbers x-num y-num))))





(verify-g-guards
 binary-+
 :hints `(("goal" :in-theory (disable* ,gfn
                                       (:rules-of-class :type-prescription
                                                        :here)))))


(local (defthm +-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (+ x y)
                              (+ 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (+ x y)
                              (+ x 0))))))

(def-gobj-dependency-thm binary-+
  :hints `(("goal" :in-theory (disable (:d ,gfn)
                                       gobj-depends-on)
            :induct ,gcall
            :expand (,gcall))))

(def-g-correct-thm binary-+ eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              (:ruleset general-object-possibilities))
                             ((:definition ,gfn)
                              i2v n2v
                              general-numberp-eval-to-numberp
                              general-boolean-value-correct
                              bool-cond-itep-eval
                              general-consp-car-correct-for-eval-g-base
                              general-consp-cdr-correct-for-eval-g-base
                              boolean-listp
                              components-to-number-alt-def
                              member-equal
                              general-number-components-ev
                              general-concretep-def
                              general-concretep-def
                              logcons bfr-list->s bfr-list->u
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)
                              (:type-prescription components-to-number-fn)))
     :induct ,gcall
     :do-not-induct t
     :expand (,gcall))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))



(defun g-binary---of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (equal xrd '(t))
             (equal yrd '(t))
             (equal xid '(t))
             (equal yid '(t)))
        (let* ((rsum (bfr-+-ss t xrn (bfr-lognot-s yrn)))
               (isum (bfr-+-ss t xin (bfr-lognot-s yin))))
          (mk-g-number (list-fix rsum)
                       1
                       (list-fix isum)))
      (g-apply 'binary-minus-for-gl (gl-list x y)))))

(in-theory (disable (g-binary---of-numbers)))


(local (defthmd bfr-eval-list-when-boolean-listp
         (implies (boolean-listp x)
                  (equal (bfr-eval-list x env)
                         x))))

;; (local (defthm rewrite-v2i-of-boolean-list
;;          (implies (and (syntaxp (not (and (consp x)
;;                                           (eq (car x) 'bfr-eval-list))))
;;                        (bind-free '((env . (car env))) (env))
;;                        (boolean-listp x))
;;                   (equal (v2i x)
;;                          (bfr-list->s x env)))
;;          :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm rewrite-v2n-of-boolean-list
;;          (implies (and (syntaxp (not (and (consp x)
;;                                           (eq (car x) 'bfr-eval-list))))
;;                        (bind-free '((env . (car env))) (env))
;;                        (boolean-listp x))
;;                   (equal (v2n x)
;;                          (bfr-list->u x env)))
;;          :hints(("Goal" :in-theory (enable bfr-eval-list-when-boolean-listp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (defthm bfr-eval-list-of-bfr-ite-bvv-fn-unde
;;   (equal (bfr-list->u (bfr-ite-bvv-fn c a b) env)
;;          (if (bfr-eval c env)
;;              (bfr-list->u a env)
;;            (bfr-list->u b env))))
;;   :hints(("Goal" :in-theory (enable bfr-ite-bvv-fn v2n)
;;           :induct t)
;;          (bfr-reasoning)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local
 (defthm realpart-of-minus
   (equal (realpart (- x))
          (- (realpart x)))
   :hints (("goal" :cases ((acl2-count x)))
           '(:use ((:instance acl2::realpart-+
                    (x x) (y (- x))))
             :in-theory (disable acl2::realpart-+)))))

(local
 (defthm imagpart-of-minus
   (equal (imagpart (- x))
          (- (imagpart x)))
   :hints (("goal" :cases ((acl2-count x)))
           '(:use ((:instance acl2::imagpart-+
                    (x x) (y (- x))))
             :in-theory (disable acl2::imagpart-+)))))

(local
 (defthm g-binary---of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-binary---of-numbers x y) env)
                   (binary-minus-for-gl (eval-g-base x env)
                                        (eval-g-base y env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-numberp
                                     general-number-components))
            :do-not-induct t))))

(local
 (defthm dependencies-of-g-binary---of-numbers
   (implies (and (general-numberp x)
                 (general-numberp y)
                 (not (gobj-depends-on n p x))
                 (not (gobj-depends-on n p y)))
            (not (gobj-depends-on n p (g-binary---of-numbers x y))))
   :hints (("goal" :do-not-induct t))
   :otf-flg t))

(in-theory (disable g-binary---of-numbers))

(def-g-binary-op binary-minus-for-gl
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (gret (g-binary---of-numbers x-num y-num))))





(verify-g-guards
 binary-minus-for-gl
 :hints `(("goal" :in-theory (disable* ,gfn
                                       (:rules-of-class :type-prescription
                                                        :here)))))


(local (defthm +-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (+ x y)
                              (+ 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (+ x y)
                              (+ x 0))))))

(def-gobj-dependency-thm binary-minus-for-gl
  :hints `(("goal" :in-theory (disable (:d ,gfn)
                                       gobj-depends-on)
            :induct ,gcall
            :expand (,gcall))))

(local
 (defthm binary---of-non-number-1
   (implies (not (acl2-numberp x))
            (equal (binary-minus-for-gl x y) (binary-minus-for-gl 0 y)))))

(local
 (defthm binary---of-non-number-2
   (implies (not (acl2-numberp y))
            (equal (binary-minus-for-gl x y) (binary-minus-for-gl x 0)))))

(def-g-correct-thm binary-minus-for-gl eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              (:ruleset general-object-possibilities))
                             ((:definition ,gfn)
                              i2v n2v
                              general-numberp-eval-to-numberp
                              general-boolean-value-correct
                              bool-cond-itep-eval
                              general-consp-car-correct-for-eval-g-base
                              general-consp-cdr-correct-for-eval-g-base
                              boolean-listp
                              components-to-number-alt-def
                              member-equal
                              general-number-components-ev
                              general-concretep-def
                              general-concretep-def
                              binary-minus-for-gl
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)
                              (:type-prescription components-to-number-fn)))
     :induct ,gcall
     :do-not-induct t
     :expand (,gcall))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
