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
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(set-inhibit-warnings "theory")

(defun g-logbitp-of-numbers (a b)
  (declare (xargs :guard (and (general-numberp a)
                              (general-numberp b))))
  (b* (((mv arn ard ain aid)
        (general-number-components a))
       ((mv brn brd bin bid)
        (general-number-components b))
       ((mv aintp aintp-known)
        (if (equal ard '(t))
            (mv (bfr-or (bfr-=-ss ain nil) (bfr-=-uu aid nil)) t)
          (mv nil nil)))
       ((mv bintp bintp-known)
        (if (equal brd '(t))
            (mv (bfr-or (bfr-=-ss bin nil) (bfr-=-uu bid nil)) t)
          (mv nil nil))))
    (if (and bintp-known aintp-known)
        (mk-g-boolean
         (bfr-logbitp-n2v 1
                      (bfr-ite-bvv-fn (bfr-and
                                     aintp (bfr-not (bfr-sign-s arn)))
                                    arn nil)
                      (bfr-ite-bss-fn bintp brn nil)))
      (g-apply 'logbitp (gl-list a b)))))

(in-theory (disable (g-logbitp-of-numbers)))


(defthm deps-of-g-logbitp-of-numbers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-numberp x)
                (general-numberp y))
           (not (gobj-depends-on k p (g-logbitp-of-numbers x y)))))

;; (local
;;  (defthm gobjectp-g-logbitp-of-numbers
;;    (implies (and (gobjectp a)
;;                  (general-numberp a)
;;                  (gobjectp b)
;;                  (general-numberp b))
;;             (gobjectp (g-logbitp-of-numbers a b)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm logbitp-when-not-integers
         (and (implies (not (natp a))
                       (equal (logbitp a b) (logbitp 0 b)))
              (implies (not (integerp b))
                       (equal (logbitp a b) (logbitp a 0))))
         :hints(("Goal" :in-theory (enable logbitp)))))

(local (defthm bfr-list->s-when-positive
         (implies (<= 0 (bfr-list->s x env))
                  (equal (bfr-list->s x env)
                         (bfr-list->u x env)))
         :hints(("Goal" :in-theory (enable scdr s-endp)))))

(local
 (defthm g-logbitp-of-numbers-correct
   (implies (and (general-numberp a)
                 (general-numberp b))
            (equal (eval-g-base (g-logbitp-of-numbers a b) env)
                   (logbitp (eval-g-base a env)
                            (eval-g-base b env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-numberp
                                     general-number-components
                                     logbitp))
            :do-not-induct t))))

(in-theory (disable g-logbitp-of-numbers))

(def-g-binary-op logbitp
  (b* ((i-num (if (general-numberp i) i 0))
       (j-num (if (general-numberp j) j 0)))
    (gret (g-logbitp-of-numbers i-num j-num))))

;; (def-gobjectp-thm logbitp
;;   :hints `(("Goal" :in-theory
;;             (e/d* (general-concretep-atom)
;;                   ((:definition ,gfn) (force)
;;                    (:rules-of-class :type-prescription :here)
;;                    (:ruleset gl-wrong-tag-rewrites)
;;                    general-concretep-def
;;                    gobj-fix-when-not-gobjectp
;;                    gobj-fix-when-gobjectp
;;                    equal-of-booleans-rewrite
;;                    (:ruleset gl-tag-rewrites)
;;                    mv-nth-cons-meta
;;                    bfr-ite-bss-fn))
;;             :induct (,gfn i j . ,params)
;;             :expand ((,gfn i j . ,params)))))

(verify-g-guards
 logbitp
 :hints `(("Goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))


(def-gobj-dependency-thm logbitp
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm logbitp-when-not-numbers
         (and (implies (not (acl2-numberp a))
                       (equal (logbitp a b) (logbitp 0 b)))
              (implies (not (acl2-numberp b))
                       (equal (logbitp a b) (logbitp a 0))))
         :hints(("Goal" :in-theory (enable logbitp)))))

(def-g-correct-thm logbitp eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      general-numberp-eval-to-numberp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      components-to-number-alt-def
                                      member-equal
                                      general-number-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      rationalp-implies-acl2-numberp
                                      hons-assoc-equal
                                      default-car default-cdr
                                      mv-nth-cons-meta
                                      possibilities-for-x-5
                                      possibilities-for-x-3
                                      general-boolean-value-cases
                                      logbitp bfr-list->s bfr-list->u
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription bfr-eval)))
             :induct (,gfn i j . ,params)
             :expand ((,gfn i j . ,params)))))
