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

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(set-inhibit-warnings "theory")

(defun g-logbitp-of-integers (a b)
  (declare (xargs :guard (and (general-integerp a)
                              (general-integerp b))))
  (b* ((abits (general-integer-bits a)))
    (mk-g-boolean (bfr-logbitp-n2v
                   1
                   (bfr-ite-bvv-fn (bfr-sign-s abits) nil abits)
                   (general-integer-bits b)))))

(in-theory (disable (g-logbitp-of-integers)))


(local (defthm pbfr-list-depends-on-of-nil
         (not (pbfr-list-depends-on k p nil))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(defthm deps-of-g-logbitp-of-integers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-integerp x)
                (general-integerp y))
           (not (gobj-depends-on k p (g-logbitp-of-integers x y)))))

;; (local
;;  (defthm gobjectp-g-logbitp-of-integers
;;    (implies (and (gobjectp a)
;;                  (general-integerp a)
;;                  (gobjectp b)
;;                  (general-integerp b))
;;             (gobjectp (g-logbitp-of-integers a b)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm logbitp-when-zp
         (implies (and (syntaxp (not (equal x ''0)))
                       (zp x))
                  (equal (logbitp x y) (logbitp 0 y)))))
                  

;; (local (defthm logbitp-when-not-integers
;;          (and (implies (not (natp a))
;;                        (equal (logbitp a b) (logbitp 0 b)))
;;               (implies (not (integerp b))
;;                        (equal (logbitp a b) (logbitp a 0))))
;;          :hints(("Goal" :in-theory (enable logbitp)))))

(local (defthm bfr-list->s-when-positive
         (implies (<= 0 (bfr-list->s x env))
                  (equal (bfr-list->s x env)
                         (bfr-list->u x env)))
         :hints(("Goal" :in-theory (e/d (scdr s-endp)
; Matt K. mod April 2016: The rule acl2::bfix-bitp is now applied, after the
; ACL2 change that adds a type-set bit for {1}, where previously it wasn't
; applied.  That application makes the proof fail, so we disable the rule.
                                        (acl2::bfix-bitp))))))

(local
 (defthm g-logbitp-of-integers-correct
   (implies (and (general-integerp a)
                 (general-integerp b))
            (equal (eval-g-base (g-logbitp-of-integers a b) env)
                   (logbitp (eval-g-base a env)
                            (eval-g-base b env))))
   :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                    (general-integerp
                                     general-integer-bits
                                     logbitp))
            :do-not-induct t))))

(in-theory (disable g-logbitp-of-integers))

(def-g-binary-op logbitp
  (b* ((i-num (if (general-integerp i) i 0))
       (j-num (if (general-integerp j) j 0)))
    (gret (g-logbitp-of-integers i-num j-num))))

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

(local (defthm logbitp-when-not-integers
         (and (implies (not (integerp a))
                       (equal (logbitp a b) (logbitp 0 b)))
              (implies (not (integerp b))
                       (equal (logbitp a b) (logbitp a 0))))
         :hints(("Goal" :in-theory (enable logbitp)))))



;; (local (defthm bfr-list->s-of-empty
;;          (Equal (bfr-list->s '(nil) env) 0)
;;          :hints(("Goal" :in-theory (enable bfr-list->s)))))

(def-g-correct-thm logbitp eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                      (:ruleset general-object-possibilities))
                                     ((:definition ,gfn)
                                      general-integerp-eval-to-integerp
                                      general-boolean-value-correct
                                      bool-cond-itep-eval
                                      boolean-listp
                                      member-equal
                                      ;; general-integer-components-ev
                                      general-concretep-def
                                      general-concretep-def
                                      ;; rationalp-implies-acl2-integerp
                                      equal-of-booleans-rewrite
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
