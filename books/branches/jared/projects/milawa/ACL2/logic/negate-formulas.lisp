; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(deflist logic.all-negationsp (x)
  (equal (logic.fmtype x) 'pnot*)
  :elementp-of-nil nil
  :guard (logic.formula-listp x))


;; Some of the rules that are generated aren't very good because they're
;; for the general case; we replace them.
(in-theory (disable equal-of-car-when-logic.all-negationsp
                    equal-when-memberp-of-logic.all-negationsp
                    equal-when-memberp-of-logic.all-negationsp-alt))

(defthm logic.fmtype-of-car-when-logic.all-negationsp
  (implies (and (logic.all-negationsp x)
                (consp x))
           (equal (logic.fmtype (car x))
                  'pnot*)))

(defthm logic.fmtype-when-memberp-of-logic.all-negationsp
  (implies (and (memberp a x)
                (logic.all-negationsp x))
           (equal (logic.fmtype a)
                  'pnot*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-when-memberp-of-logic.all-negationsp-alt
  (implies (and (logic.all-negationsp x)
                (memberp a x))
           (equal (logic.fmtype a)
                  'pnot*)))





(defprojection :list (logic.~args x)
               :element (logic.~arg x)
               :guard (and (logic.formula-listp x)
                           (logic.all-negationsp x))
               :nil-preservingp t)

(defthm forcing-logic.formula-listp-of-logic.~args
  (implies (and (force (logic.all-negationsp x))
                (force (logic.formula-listp x)))
           (equal (logic.formula-listp (logic.~args x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-logic.~args
  (implies (and (force (logic.all-negationsp x))
                (force (logic.formula-list-atblp x atbl)))
           (equal (logic.formula-list-atblp (logic.~args x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.~arg-of-car-when-all-equalp-of-logic.~args
  (implies (all-equalp p (logic.~args x))
           (equal (logic.~arg (car x))
                  (if (consp x)
                      p
                    nil))))


;; (logic.negate-formulas x) takes a list of formulas [A1, ..., An] and
;; produces the list [~A1, ..., ~An].

(encapsulate
 ()

 (local (in-theory (disable forcing-equal-of-logic.pnot-rewrite
                            forcing-equal-of-logic.pnot-rewrite-two)))

 (defprojection :list (logic.negate-formulas x)
                :element (logic.pnot x)
                :guard (logic.formula-listp x)))



(defthm memberp-of-logic.pnot-in-logic.negate-formulas
  ;; BOZO.  We can develop a stronger version of what the macro generated
  ;; because our transformer was one-to-one.  Maybe we should add a flag to
  ;; deflist for this?
  (equal (memberp (logic.pnot a) (logic.negate-formulas x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(in-theory (disable memberp-of-logic.pnot-in-logic.negate-formulas-when-memberp))


(defthm logic.formula-listp-of-logic.negate-formulas
  (implies (force (logic.formula-listp x))
           (equal (logic.formula-listp (logic.negate-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.formula-list-atblp-of-logic.negate-formulas
  (implies (force (logic.formula-list-atblp x atbl))
           (equal (logic.formula-list-atblp (logic.negate-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm equal-of-logic.negate-formulas-and-logic.negate-formulas
  (equal (equal (logic.negate-formulas x)
                (logic.negate-formulas y))
         (equal (list-fix x)
                (list-fix y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.~args-of-logic.negate-formulas
  (implies (force (logic.formula-listp x))
           (equal (logic.~args (logic.negate-formulas x))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.~args-of-logic.negate-formulas-free
  (implies (and (equal x (logic.negate-formulas y))
                (force (logic.formula-listp y)))
           (equal (logic.~args x)
                  (list-fix y))))

(defthm forcing-logic.all-negationsp-of-logic.negate-formulas
  (equal (logic.all-negationsp (logic.negate-formulas x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.all-negationsp-of-logic.negate-formulas-free
  (implies (equal x (logic.negate-formulas y))
           (equal (logic.all-negationsp x)
                  t)))




;; Smart-negate-formulas is the same as negate-formulas, except that it
;; converts formulas of the form ~A into A instead of ~~A.

(defund logic.smart-negate-formulas (x)
  (declare (xargs :guard (logic.formula-listp x)))
  (if (consp x)
      (cons (if (equal (logic.fmtype (car x)) 'pnot*)
                (logic.~arg (car x))
              (logic.pnot (car x)))
            (logic.smart-negate-formulas (cdr x)))
    nil))

(defthm logic.smart-negate-formulas-when-not-consp
  (implies (not (consp x))
           (equal (logic.smart-negate-formulas x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.smart-negate-formulas))))

(defthm logic.smart-negate-formulas-of-cons
  (equal (logic.smart-negate-formulas (cons a x))
         (cons (if (equal (logic.fmtype a) 'pnot*)
                   (logic.~arg a)
                 (logic.pnot a))
               (logic.smart-negate-formulas x)))
  :hints(("Goal" :in-theory (enable logic.smart-negate-formulas))))

(defthm true-listp-of-logic.smart-negate-formulas
  (equal (true-listp (logic.smart-negate-formulas x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.smart-negate-formulas-of-list-fix
  (equal (logic.smart-negate-formulas (list-fix x))
         (logic.smart-negate-formulas x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.smart-negate-formulas-of-app
  (equal (logic.smart-negate-formulas (app x y))
         (app (logic.smart-negate-formulas x)
              (logic.smart-negate-formulas y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-logic.smart-negate-formulas
  (equal (len (logic.smart-negate-formulas x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-logic.smart-negate-formulas
  (equal (consp (logic.smart-negate-formulas x))
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.smart-negate-formulas-under-iff
  (iff (logic.smart-negate-formulas x)
       (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-listp-of-logic.smart-negate-formulas
  (implies (force (logic.formula-listp x))
           (equal (logic.formula-listp (logic.smart-negate-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-logic.smart-negate-formulas
  (implies (force (logic.formula-list-atblp x atbl))
           (equal (logic.formula-list-atblp (logic.smart-negate-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

;; Reasoning about membership in smart-negate-formulas is tricky because you
;; could obtain ~A from either A or ~~A.

(defthm memberp-of-logic.pnot-in-logic.smart-negate-formulas
  (implies (and (equal (logic.fmtype a) 'pequal*)
                (memberp a x))
           (equal (memberp (logic.pnot a) (logic.smart-negate-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.pequal-in-logic.smart-negate-formulas
  (implies (and (memberp (logic.pnot (logic.pequal a b)) x)
                (force (logic.termp a))
                (force (logic.termp b)))
           (equal (memberp (logic.pequal a b) (logic.smart-negate-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.~arg-in-logic.smart-negate-formulas
  (implies (and (equal (logic.fmtype a) 'pnot*)
                (memberp a x))
           (equal (memberp (logic.~arg a) (logic.smart-negate-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
