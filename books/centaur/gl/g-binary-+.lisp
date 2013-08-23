; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
(local (include-book "clause-processors/just-expand" :dir :system))
;(local (allow-arith5-help))

;; (include-book "univ-gl-eval")

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
          (mk-g-number rsum 1 isum))
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
    (g-binary-+-of-numbers x-num y-num)))





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
                              i2v n2v bfr-+-ss
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
