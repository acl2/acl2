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
(include-book "simple-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (clause.lifted-termp x)
;;
;; We say x is a "lifted" term if it has no subterms of the form (f ... (if
;; ...)  ...) unless f is if.  We call such subterms the "unlifted" parts of a
;; term.

(defund clause.lifted-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (cond ((logic.constantp x) t)
        ((logic.variablep x) t)
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (if (and (equal name 'if)
                    (equal (len args) 3))
               (and (clause.lifted-termp (first args))
                    (clause.lifted-termp (second args))
                    (clause.lifted-termp (third args)))
             (clause.simple-term-listp (logic.function-args x)))))
        ((logic.lambdap x)
         (clause.simple-term-listp (logic.lambda-actuals x)))
        (t t)))

(defthm clause.lifted-termp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-not-if
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (and (clause.lifted-termp (first (logic.function-args x)))
                       (clause.lifted-termp (second (logic.function-args x)))
                       (clause.lifted-termp (third (logic.function-args x))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-if-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))


(defun clause.lifted-termp-induction (x)
  (declare (xargs :verify-guards nil))
  (cond ((logic.constantp x) nil)
        ((logic.variablep x) nil)
        ((and (logic.functionp x)
              (equal (logic.function-name x) 'if)
              (equal (len (logic.function-args x)) 3))
         (list (clause.lifted-termp-induction (first (logic.function-args x)))
               (clause.lifted-termp-induction (second (logic.function-args x)))
               (clause.lifted-termp-induction (third (logic.function-args x)))))
        ((logic.functionp x)
         nil)
        ((logic.lambdap x)
         nil)
        (t nil)))

(defthm clause.lifted-termp-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.lifted-termp x)
                  t))
  :hints(("Goal" :induct (clause.lifted-termp-induction x))))

(defthm booleanp-of-clause.lifted-termp
  (equal (booleanp (clause.lifted-termp x))
         t)
  :hints(("Goal" :induct (clause.lifted-termp-induction x))))

(deflist clause.lifted-term-listp (x)
  (clause.lifted-termp x)
  :elementp-of-nil t
  :guard (logic.term-listp x))
