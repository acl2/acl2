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
;(include-book "tools/with-arith5-help" :dir :system)

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
;(local (allow-arith5-help))

(defun g-binary-*-of-integers (x y)
  (declare (xargs :guard (and (general-integerp x)
                              (general-integerp y))))
  (b* ((xbits (general-integer-bits x))
       (ybits (general-integer-bits y)))
    (mk-g-integer (bfr-*-ss xbits ybits))))

(in-theory (disable (g-binary-*-of-integers)))

(defthm deps-of-g-binary-*-of-integers
  (implies (and (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-integerp x)
                (general-integerp y))
           (not (gobj-depends-on k p (g-binary-*-of-integers x y)))))

(local
 (progn
   ;; (defthm gobjectp-g-binary-*-of-numbers
   ;;   (implies (and (gobjectp x)
   ;;                 (general-numberp x)
   ;;                 (gobjectp y)
   ;;                 (general-numberp y))
   ;;            (gobjectp (g-binary-*-of-numbers x y)))
   ;;   :hints(("Goal" :in-theory (disable general-numberp
   ;;                                      general-number-components))))

   ;; (include-book "arithmetic/top-with-meta" :dir :system)

   (defthm g-binary-*-of-integers-correct
     (implies (and (general-integerp x)
                   (general-integerp y))
              (equal (eval-g-base (g-binary-*-of-integers x y) env)
                     (* (eval-g-base x env)
                        (eval-g-base y env))))
     :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                      (general-integerp
                                       general-integer-bits))
              :do-not-induct t)))))

(in-theory (disable g-binary-*-of-integers))

(def-g-binary-op binary-*
  (b* ((x (general-number-fix x))
       (y (general-number-fix y)))
    (cond ((and** (general-integerp x) (general-integerp y))
           (gret (g-binary-*-of-integers x y)))
          ((or (and** (general-concretep x)
                    (eql (general-concrete-obj x) 0))
               (and** (general-concretep y)
                      (eql (general-concrete-obj y) 0)))
           (gret 0))
          (t (gret (g-apply 'binary-* (list x y)))))))

(local (defthmd general-concretep-atom
         (implies (and (not (consp x)))
                  (general-concretep x))
         :hints(("Goal" :in-theory (enable general-concretep-def
                                           gobjectp-def)))
         :rule-classes ((:rewrite :backchain-limit-lst (0)))))

(verify-g-guards
 binary-*
 :hints `(("goal" :in-theory
           (disable* ,gfn
                     (:rules-of-class :type-prescription :here)))))




(local (defthm *-when-not-numberp
         (and (implies (not (acl2-numberp x))
                       (equal (* x y)
                              (* 0 y)))
              (implies (not (acl2-numberp y))
                       (equal (* x y)
                              (* x 0))))))

(local (defthm pbfr-list-depends-on-of-empty
         (not (pbfr-list-depends-on k p '(nil)))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(local (defthm bfr-list->s-of-empty
         (equal (bfr-list->s '(nil) env) 0)
         :hints(("Goal" :in-theory (enable bfr-list->s)))))

(local (in-theory (disable general-concretep-def
                           general-integerp-of-atom
                           general-concrete-obj-when-atom)))


(def-gobj-dependency-thm binary-*
  :hints `(("goal" :induct ,gcall
           :expand (,gcall)
           :do-not-induct t
           :in-theory (disable (:d ,gfn)
                               gobj-depends-on))))

(local (defcong number-equiv equal (* x y) 1))
(local (defcong number-equiv equal (* x y) 2))


(def-g-correct-thm binary-* eval-g-base
  :hints
  `(("goal" :in-theory (e/d (eval-g-base-list
                             (general-concrete-obj))
                            ())
     :induct ,gcall
     :do-not-induct t
     :expand (,gcall))))
