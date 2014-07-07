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
(include-book "basic")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund build.skip (a)
  (declare (xargs :guard (logic.formulap a)))
  (logic.appeal 'skip a nil nil))

(encapsulate
 ()
 (local (in-theory (enable build.skip)))

 (defthm build.skip-under-iff
   (iff (build.skip a)
        t))

 (defthm logic.method-of-build.skip
   (equal (logic.method (build.skip a))
          'skip))

 (defthm logic.conclusion-of-build.skip
   (equal (logic.conclusion (build.skip a))
          a))

 (defthm logic.subproofs-of-build.skip
   (equal (logic.subproofs (build.skip a))
          nil))

 (defthm logic.extras-of-build.skip
   (equal (logic.extras (build.skip a))
          nil))

 (defthm forcing-logic.appealp-of-build.skip
   (implies (force (logic.formulap a))
            (equal (logic.appealp (build.skip a))
                   t)))

 (defthm forcing-logic.proofp-of-build.skip
   (implies (force (logic.formula-atblp a atbl))
            (equal (logic.proofp (build.skip a) skips thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.skip-okp)))))


(defprojection :list (build.skip-list x)
               :element (build.skip x)
               :guard (logic.formula-listp x))

(defthm forcing-logic.appeal-listp-of-build.skip-list
  (implies (force (logic.formula-listp x))
           (equal (logic.appeal-listp (build.skip-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-conclusions-of-build.skip-list
  (implies (force (logic.formula-listp x))
           (equal (logic.strip-conclusions (build.skip-list x))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.proof-listp-of-build.skip-list
  (implies (force (logic.formula-list-atblp x atbl))
           (equal (logic.proof-listp (build.skip-list x) axioms thms atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
