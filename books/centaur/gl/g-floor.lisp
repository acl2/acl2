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
(local (include-book "bfr-reasoning"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(defun g-floor-of-numbers (x y)
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
        (mk-g-number (list-fix (bfr-floor-ss xrn yrn)))
      (g-apply 'floor (gl-list x y)))))

(in-theory (disable (g-floor-of-numbers)))

(defthm deps-of-g-floor-of-numbers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-numberp x)
                (general-numberp y))
           (not (gobj-depends-on k p (g-floor-of-numbers x y)))))

;; (local
;;  (defthm gobjectp-g-floor-of-numbers
;;    (implies (and (gobjectp x)
;;                  (general-numberp x)
;;                  (gobjectp y)
;;                  (general-numberp y))
;;             (gobjectp (g-floor-of-numbers x y)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

;; (local (defthm not-integerp-bfr-floor-ss
;;          (implies (and (bfr-listp a) (bfr-listp b))
;;                   (not (integerp (bfr-floor-ss a b))))
;;          :hints (("goal" :use ((:instance bfr-listp-bfr-floor-ss))
;;                   :in-theory (e/d (bfr-listp) (bfr-listp-bfr-floor-ss))))))

(local (add-bfr-fn-pat bfr-=-uu))
(local (add-bfr-fn-pat bfr-=-ss))

(local
 (defthm g-floor-of-numbers-correct
   (implies (and (general-numberp x)
                 (general-numberp y))
            (equal (eval-g-base (g-floor-of-numbers x y) env)
                   (floor (eval-g-base x env)
                          (eval-g-base y env))))
   :hints (("goal" :in-theory
            (e/d* ((:ruleset general-object-possibilities))
                  (general-numberp
                   general-number-components
                   floor))
            :do-not-induct t)
           (bfr-reasoning))))

(in-theory (disable g-floor-of-numbers))




(def-g-binary-op floor
  (b* ((i-num (if (general-numberp i) i 0))
       (j-num (if (general-numberp j) j 0)))
    (gret (g-floor-of-numbers i-num j-num))))

;; (def-gobjectp-thm floor
;;   :hints `(("goal" :in-theory (e/d* (general-concretep-atom)
;;                                     ((:definition ,gfn)
;;                                      (force)
;;                                      general-concretep-def
;;                                      hyp-fix
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)))
;;             :induct (,gfn i j . ,params)
;;             :do-not-induct t
;;             :expand ((,gfn i j . ,params)
;;                      (gobjectp (floor (gobj-fix i) (gobj-fix j)))))))

(verify-g-guards
 floor
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))

(def-gobj-dependency-thm floor
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local (defthm floor-when-not-numberp
         (and (implies (not (acl2-numberp i))
                       (equal (floor i j) (floor 0 j)))
              (implies (not (acl2-numberp j))
                       (equal (floor i j) (floor i 0))))))

(def-g-correct-thm floor eval-g-base
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
                              floor
                              eval-g-base-alt-def
                              logcons
                              default-car default-cdr
                              set::double-containment
                              hons-assoc-equal
                              equal-of-booleans-rewrite
                              rationalp-implies-acl2-numberp
                              (:rules-of-class :type-prescription :here))
                             ((:type-prescription bfr-eval)))
     :induct (,gfn i j . ,params)
     :do-not-induct t
     :expand ((,gfn i j . ,params)))
    (and stable-under-simplificationp
         (flag::expand-calls-computed-hint
          clause '(eval-g-base)))))
