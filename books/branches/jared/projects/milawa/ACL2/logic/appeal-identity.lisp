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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund logic.appeal-identity (x)
  (declare (xargs :guard (logic.appealp x)))
  (if (consp x)
      x
    (cons nil nil)))

(defthm logic.appeal-identity-under-iff
  (iff (logic.appeal-identity x)
       t)
  :hints(("Goal" :in-theory (enable logic.appeal-identity))))

(defthm logic.method-of-logic.appeal-identity
  (equal (logic.method (logic.appeal-identity x))
         (logic.method x))
  :hints(("Goal" :in-theory (enable logic.method logic.appeal-identity))))

(defthm logic.conclusion-of-logic.appeal-identity
  (equal (logic.conclusion (logic.appeal-identity x))
         (logic.conclusion x))
  :hints(("Goal" :in-theory (enable logic.conclusion logic.appeal-identity))))

(defthm logic.subproofs-of-logic.appeal-identity
  (equal (logic.subproofs (logic.appeal-identity x))
         (logic.subproofs x))
  :hints(("Goal" :in-theory (enable logic.subproofs logic.appeal-identity))))

(defthm logic.extras-of-logic.appeal-identity
  (equal (logic.extras (logic.appeal-identity x))
         (logic.extras x))
  :hints(("Goal" :in-theory (enable logic.extras logic.appeal-identity))))

(local (in-theory (disable forcing-true-listp-of-logic.subproofs)))

(defthm logic.skip-okp-of-logic.appeal-identity
  (equal (logic.skip-okp (logic.appeal-identity x) atbl)
         (logic.skip-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.skip-okp))))

(defthm logic.axiom-okp-of-logic.appeal-identity
  (equal (logic.axiom-okp (logic.appeal-identity x) axioms atbl)
         (logic.axiom-okp x axioms atbl))
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))

(defthm logic.theorem-okp-of-logic.appeal-identity
  (equal (logic.theorem-okp (logic.appeal-identity x) theorems atbl)
         (logic.theorem-okp x theorems atbl))
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))

(defthm logic.propositional-schema-okp-of-logic.appeal-identity
  (equal (logic.propositional-schema-okp (logic.appeal-identity x) atbl)
         (logic.propositional-schema-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.propositional-schema-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.functional-equality-okp-of-logic.appeal-identity
  (equal (logic.functional-equality-okp (logic.appeal-identity x) atbl)
         (logic.functional-equality-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.functional-equality-okp))))

(defthm logic.expansion-okp-of-logic.appeal-identity
  (equal (logic.expansion-okp (logic.appeal-identity x) atbl)
         (logic.expansion-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.expansion-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.contraction-okp-of-logic.appeal-identity
  (equal (logic.contraction-okp (logic.appeal-identity x))
         (logic.contraction-okp x))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))

(defthm logic.associativity-okp-of-logic.appeal-identity
  (equal (logic.associativity-okp (logic.appeal-identity x))
         (logic.associativity-okp x))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))

(defthm logic.cut-okp-of-logic.appeal-identity
  (equal (logic.cut-okp (logic.appeal-identity x))
         (logic.cut-okp x))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm logic.instantiation-okp-of-logic.appeal-identity
  (equal (logic.instantiation-okp (logic.appeal-identity x) atbl)
         (logic.instantiation-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.instantiation-okp))))

(defthm logic.beta-reduction-okp-of-logic.appeal-identity
  (equal (logic.beta-reduction-okp (logic.appeal-identity x) atbl)
         (logic.beta-reduction-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.beta-reduction-okp))))

(defthm logic.induction-okp-of-logic.appeal-identity
  (equal (logic.induction-okp (logic.appeal-identity x))
         (logic.induction-okp x))
  :hints(("Goal" :in-theory (enable logic.induction-okp))))

(defthm logic.base-eval-okp-of-logic.appeal-identity
  (equal (logic.base-eval-okp (logic.appeal-identity x) atbl)
         (logic.base-eval-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.base-eval-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.appeal-step-okp-of-logic.appeal-identity
  (equal (logic.appeal-step-okp (logic.appeal-identity x) axioms thms atbl)
         (logic.appeal-step-okp x axioms thms atbl))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appealp-of-logic.appeal-identity
  (equal (logic.appealp (logic.appeal-identity x))
         (logic.appealp x))
  :hints(("Goal" :in-theory (enable logic.appeal-identity
                                    definition-of-logic.appealp))))

(defthm logic.proofp-of-logic.appeal-identity
  (equal (logic.proofp (logic.appeal-identity x) axioms thms atbl)
         (logic.proofp x axioms thms atbl))
  :hints(("Goal" :use ((:instance definition-of-logic.proofp (x (logic.appeal-identity x)))
                       (:instance definition-of-logic.proofp)))))

