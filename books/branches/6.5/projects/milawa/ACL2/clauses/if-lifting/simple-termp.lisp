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
(include-book "../../logic/terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (clause.simple-termp x)
;;
;; A term is "simple" if it contains no if-expressions.  As a slight hack, we
;; consider degenerate terms to be simple, so this definition lines up
;; perfectly with clause.depth.

(defund clause.flag-simple-termp (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (and (equal flag 'list)
                                (logic.term-listp x)))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) t)
            ((logic.variablep x) t)
            ((logic.functionp x)
             (if (and (equal (logic.function-name x) 'if)
                      (equal (len (logic.function-args x)) 3))
                 nil
               (clause.flag-simple-termp 'list (logic.function-args x))))
            ((logic.lambdap x)
             (clause.flag-simple-termp 'list (logic.lambda-actuals x)))
         (t t))
    (if (consp x)
        (and (clause.flag-simple-termp 'term (car x))
             (clause.flag-simple-termp 'list (cdr x)))
      t)))

(definlined clause.simple-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (clause.flag-simple-termp 'term x))

(definlined clause.simple-term-listp (x)
  (declare (xargs :guard (logic.term-listp x)))
  (clause.flag-simple-termp 'list x))

(defthmd definition-of-clause.simple-termp
  (equal (clause.simple-termp x)
         (cond ((logic.constantp x) t)
               ((logic.variablep x) t)
               ((logic.functionp x)
                (if (and (equal (logic.function-name x) 'if)
                         (equal (len (logic.function-args x)) 3))
                    nil
                  (clause.simple-term-listp (logic.function-args x))))
               ((logic.lambdap x)
                (clause.simple-term-listp (logic.lambda-actuals x)))
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.simple-termp
                                    clause.simple-term-listp
                                    clause.flag-simple-termp))))

(defthmd definition-of-clause.simple-term-listp
  (equal (clause.simple-term-listp x)
         (if (consp x)
             (and (clause.simple-termp (car x))
                  (clause.simple-term-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.simple-termp
                                    clause.simple-term-listp
                                    clause.flag-simple-termp))))

(defthm clause.flag-simple-termp-of-term-removal
  (equal (clause.flag-simple-termp 'term x)
         (clause.simple-termp x))
  :hints(("Goal" :in-theory (enable clause.simple-termp))))

(defthm clause.flag-simple-termp-of-list-removal
  (equal (clause.flag-simple-termp 'list x)
         (clause.simple-term-listp x))
  :hints(("Goal" :in-theory (enable clause.simple-term-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-termp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-term-listp))))

(defthm clause.simple-termp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))




(defun clause.simple-term-induction (flag x)
  (declare (xargs :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) nil)
            ((logic.functionp x)
             (if (and (equal (logic.function-name x) 'if)
                      (equal (len (logic.function-args x)) 3))
                 (list (clause.simple-term-induction 'term (first (logic.function-args x)))
                       (clause.simple-term-induction 'term (second (logic.function-args x)))
                       (clause.simple-term-induction 'term (third (logic.function-args x))))
               (clause.simple-term-induction 'list (logic.function-args x))))
            ((logic.lambdap x)
             (clause.simple-term-induction 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (list (clause.simple-term-induction 'term (car x))
              (clause.simple-term-induction 'list (cdr x)))
      nil)))

(defthm clause.simple-term-listp-when-not-consp
  (implies (not (consp x))
           (equal (clause.simple-term-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-term-listp))))

(defthm clause.simple-term-listp-of-cons
  (equal (clause.simple-term-listp (cons a x))
         (and (clause.simple-termp a)
              (clause.simple-term-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-term-listp))))

(defthms-flag
  :thms ((term booleanp-of-clause.simple-termp
               (equal (booleanp (clause.simple-termp x))
                      t))
         (t booleanp-of-clause.simple-term-listp
            (equal (booleanp (clause.simple-term-listp x))
                   t)))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(deflist clause.simple-term-listp (x)
  (clause.simple-termp x)
  :elementp-of-nil t
  :already-definedp t)

(defthm clause.simple-term-listp-when-length-three
  (implies (equal (len x) 3)
           (equal (clause.simple-term-listp x)
                  (and (clause.simple-termp (first x))
                       (clause.simple-termp (second x))
                       (clause.simple-termp (third x))))))

(deflist clause.simple-term-list-listp (x)
  (clause.simple-term-listp x)
  :elementp-of-nil t
  :guard (logic.term-list-listp x))
