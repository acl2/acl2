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
(include-book "colors")
(include-book "skeletonp")
(include-book "../build/skip")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund tactic.skip-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'skip-all)
         (not extras)
         (not goals)
         (let ((prev-goals (tactic.skeleton->goals history)))
           (consp prev-goals)))))

(defthm booleanp-of-tactic.skip-all-okp
  (equal (booleanp (tactic.skip-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.skip-all-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.skip-all-tac (x)
  ;; Replace occurrences of expr with var, a new variable
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0skip-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (tactic.extend-skeleton nil 'skip-all nil x))))

(defthm forcing-tactic.skeletonp-of-tactic.skip-all-tac
  (implies (and (tactic.skip-all-tac x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.skip-all-tac x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skip-all-tac))))

(defthm forcing-tactic.skip-all-okp-of-tactic.skip-all-tac
  (implies (and (tactic.skip-all-tac x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skip-all-okp (tactic.skip-all-tac x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skip-all-tac tactic.skip-all-okp))))




(defund tactic.skip-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.skip-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil)
           (ignore proofs))
  (let* ((history    (tactic.skeleton->history x))
         (prev-goals (tactic.skeleton->goals history)))
    (build.skip-list (clause.clause-list-formulas prev-goals))))

(defobligations tactic.skip-all-compile
  (build.skip-all))

(encapsulate
 ()
 (local (in-theory (enable tactic.skip-all-okp tactic.skip-all-compile)))

 (verify-guards tactic.skip-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.skip-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.skip-all-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.skip-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.skip-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.skip-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.skip-all-compile)))
            (equal (logic.proof-listp (tactic.skip-all-compile x proofs) axioms thms atbl)
                   t))))
