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

(defun g-mod-of-numbers (x y)
  (declare (xargs :guard (and (general-numberp x)
                              (general-numberp y))))
  (b* (((mv xrn xrd xin xid)
        (general-number-components x))
       ((mv yrn yrd yin yid)
        (general-number-components y)))
    (if (and (eq (bfr-=-uu xrd '(t)) t)
             (eq (bfr-=-uu yrd '(t)) t)
             (eq (bfr-or (bfr-=-ss xin nil)
                         (bfr-=-uu xid nil)) t)
             (eq (bfr-or (bfr-=-ss yin nil)
                         (bfr-=-uu yid nil)) t))
        (mk-g-number (list-fix (bfr-mod-ss xrn yrn)))
      (g-apply 'mod (gl-list x y)))))

(in-theory (disable (g-mod-of-numbers)))

(defthm deps-of-g-mod-of-numbers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-numberp x)
                (general-numberp y))
           (not (gobj-depends-on k p (g-mod-of-numbers x y)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; (local (defthm not-integerp-bfr-mod-ss
;;          (implies (and (bfr-listp a) (bfr-listp b))
;;                   (not (integerp (bfr-mod-ss a b))))
;;          :hints (("goal" :use ((:instance bfr-listp-bfr-mod-ss))
;;                   :in-theory (e/d (bfr-listp) (bfr-listp-bfr-mod-ss))))))

(local (defthm rationalp-mod
         (implies (and (integerp x) (integerp y))
                  (rationalp (mod x y)))))

(local (add-bfr-fn-pat bfr-=-uu))
(local (add-bfr-fn-pat bfr-=-ss))

(local
 (defthm g-mod-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-mod-of-numbers x y) env)
                   (mod (eval-g-base x env)
                          (eval-g-base y env))))
   :hints (("goal" :in-theory
            (e/d* ((:ruleset general-object-possibilities))
                  (general-numberp
                   general-number-components
                   mod))
            :do-not-induct t)
           (bfr-reasoning))))

(in-theory (disable g-mod-of-numbers))




(def-g-binary-op mod
  (b* ((x-num (if (general-numberp x) x 0))
       (y-num (if (general-numberp y) y 0)))
    (gret (g-mod-of-numbers x-num y-num))))

;; (def-gobjectp-thm mod
;;   :hints `(("goal" :in-theory (e/d* (general-concretep-atom)
;;                                     ((:definition ,gfn)
;;                                      (force)
;;                                      general-concretep-def
;;                                      hyp-fix
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)))
;;             :induct (,gfn x y . ,params)
;;             :do-not-induct t
;;             :expand ((,gfn x y . ,params)
;;                      (gobjectp (mod (gobj-fix i) (gobj-fix j)))))))

(verify-g-guards
 mod
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(def-gobj-dependency-thm mod
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm mod-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (mod x y) (mod 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (mod x y) (mod x 0))))))

(def-g-correct-thm mod eval-g-base
  :hints
  `(("goal" :in-theory (e/d* (general-concretep-atom
                              (:ruleset general-object-possibilities))
                             ((:definition ,gfn)
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
                              mod floor
                              hons-assoc-equal
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn x y . ,params)
     :do-not-induct t
     :expand ((,gfn x y . ,params)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
