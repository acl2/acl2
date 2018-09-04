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
(include-book "centaur/misc/outer-local" :dir :system)
(local (include-book "eval-g-base-help"))

(local (include-book "hyp-fix"))
(local (include-book "var-bounds"))

(set-inhibit-warnings "theory")

(local (defthm eval-g-base-apply-of-equal
         (equal (eval-g-base-ev (cons 'equal (kwote-lst (list x y))) a)
                (equal x y))))

(local (in-theory (disable acl2-count)))

(define g-equal-of-integers ((x general-integerp)
                           (y general-integerp))
  :returns (equiv)
  (mk-g-boolean (bfr-=-ss (general-integer-bits x)
                          (general-integer-bits y)))
  ///
  (std::defret dependencies-of-<fn>
    (implies (and (general-integerp x)
                  (general-integerp y)
                  (not (gobj-depends-on k p x))
                  (not (gobj-depends-on k p y)))
             (not (gobj-depends-on k p equiv))))

  (std::defret <fn>-correct
    (implies (and (general-integerp x)
                  (general-integerp y))
             (equal (eval-g-base equiv env)
                    (equal (eval-g-base x env)
                           (eval-g-base y env))))))

(def-g-fn equal
  ;; Once we've ruled out the case where they're both atoms, start by recurring
  ;; down to non-ITEs on both a and b:
  `(let ((a x) (b y))
     (cond ((hqual a b) (gret t))
           ((and (general-concretep a) (general-concretep b))
            (gret (hons-equal (general-concrete-obj a) (general-concrete-obj b))))
           ((mbe :logic (equal (tag a) :g-ite)
                 :exec (and (consp a) (eq (tag a) :g-ite)))
            (if (zp clk)
                (gret (g-apply 'equal (gl-list a b)))
              (let* ((test (g-ite->test a))
                     (then (g-ite->then a))
                     (else (g-ite->else a)))
                (g-if (gret test)
                      (,gfn then b hyp clk config bvar-db state)
                      (,gfn else b hyp clk config bvar-db state)))))
           ((mbe :logic (equal (tag b) :g-ite)
                 :exec (and (consp b) (eq (tag b) :g-ite)))
            (if (zp clk)
                (gret (g-apply 'equal (gl-list a b)))
              (let* ((test (g-ite->test b))
                     (then (g-ite->then b))
                     (else (g-ite->else b)))
                (g-if (gret test)
                      (,gfn a then hyp clk config bvar-db state)
                      (,gfn a else hyp clk config bvar-db state)))))
           ((mbe :logic (not (member-eq (tag a) '(:g-var :g-apply)))
                 :exec (or (atom a)
                           (not (member-eq (tag a) '(:g-var :g-apply)))))
            (cond ((mbe :logic (not (member-eq (tag b) '(:g-var :g-apply)))
                        :exec (or (atom b)
                                  (not (member-eq (tag b) '(:g-var :g-apply)))))
                   (cond ((general-booleanp a)
                          (gret (and (general-booleanp b)
                                     (mk-g-boolean (bfr-iff (general-boolean-value a)
                                                            (general-boolean-value b))))))
                         ((general-integerp a)
                          (if (general-integerp b)
                              (gret (g-equal-of-integers a b))
                            (gret nil)))
                         ((general-consp a)
                          (if (general-consp b)
                              (g-if (,gfn (general-consp-car a)
                                          (general-consp-car b)
                                          hyp clk config bvar-db state)
                                    (,gfn (general-consp-cdr a)
                                          (general-consp-cdr b)
                                          hyp clk config bvar-db state)
                                    (gret nil))
                            (gret nil)))
                         (t (gret nil))))
                  (t (gret (g-apply 'equal (gl-list a b))))))
           (t (gret (g-apply 'equal (gl-list a b))))))
  :hyp-hints `(("goal" :induct ,gcall
                :in-theory (disable (:d ,gfn)
                                    set::double-containment
                                    equal-of-booleans-rewrite)
                :expand ((:free (hyp) ,gcall)
                         (:free (hyp) ,(subst 'x 'y gcall))))))

(verify-g-guards
 equal
 :hints `(("Goal" :in-theory (disable ,gfn))))






(local (include-book "clause-processors/just-expand" :dir :System))



(def-gobj-dependency-thm equal
    :hints `((acl2::just-induct-and-expand ,gcall)))



(local (defthm general-consp-implies-general-consp
         (implies (general-consp x)
                  (general-consp x))))

(local (defthm equal-cons-when-not-consp
         (implies (not (consp x))
                  (not (equal x (cons a b))))))

(local (defthm equal-bfr-list->s-when-not-integerp
         (implies (not (integerp x))
                  (not (equal x (bfr-list->s a b))))))

(local (defthm equal-bfr-eval-when-not-booleanp
         (implies (not (booleanp x))
                  (not (equal x (bfr-eval a b))))))


(local (include-book "std/util/termhints" :dir :system))

(def-g-correct-thm equal eval-g-base
  :hints `((acl2::just-induct-and-expand ,gcall)
           (and stable-under-simplificationp
                `(:in-theory (enable eval-g-base-list
                                     possibilities-for-x-10)
                  :do-not-induct t))
           ;; (and stable-under-simplificationp
           ;;      '(:cases ((consp (eval-g-base x env))
           ;;                (integerp (eval-g-base x env))
           ;;                (booleanp (eval-g-base x env)))))
           (and stable-under-simplificationp
                (acl2::use-termhint
                 (acl2::termhint-seq
                  (cond ((equal (tag y) :g-ite)
                         ''(:cases ((eval-g-base (g-ite->test y) env))))
                        (t ''(:cases ((general-consp y)
                                      (general-integerp y)
                                      (general-booleanp y)))))
                  (and (equal (tag x) :g-ite)
                       ''(:cases ((eval-g-base (g-ite->test x) env)))))))))
