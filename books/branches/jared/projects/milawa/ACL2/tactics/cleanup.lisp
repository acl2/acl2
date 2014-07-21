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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund tactic.cleanup-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'cleanup)
         (not extras)
         (let* ((old-goals   (tactic.skeleton->goals history))
                (cleanup     (clause.fast-clean-clauses old-goals))
                (unprovablep (first cleanup))
                (progressp   (second cleanup))
                (new-goals   (third cleanup)))
           (and (not unprovablep)
                progressp
                (equal goals new-goals))))))

(defthm booleanp-of-tactic.cleanup-okp
  (equal (booleanp (tactic.cleanup-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.cleanup-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.cleanup-tac (x warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (booleanp warnp))))
  (let* ((goals       (tactic.skeleton->goals x))
         (cleanup     (clause.fast-clean-clauses goals))
         (unprovablep (first cleanup))
         (progressp   (second cleanup))
         (new-goals   (third cleanup)))
    (cond (unprovablep
           ;; We print this out even if the warnings are off.
           (ACL2::cw "~s0Cleanup-tac failure~s1: unprovable clause discovered.~%" *red* *black*))
          ((not progressp)
           (and warnp
                (ACL2::cw "~s0Cleanup-tac failure~s1: the goal is already clean.~%" *red* *black*)))
          (t
           (tactic.extend-skeleton new-goals 'cleanup nil x)))))

(defthm forcing-tactic.skeletonp-of-tactic.cleanup-tac
  (implies (and (tactic.cleanup-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.cleanup-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cleanup-tac))))

(defthm forcing-tactic.cleanup-okp-of-tactic.cleanup-tac
  (implies (and (tactic.cleanup-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.cleanup-okp (tactic.cleanup-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cleanup-tac tactic.cleanup-okp))))




(defund tactic.cleanup-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.cleanup-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history   (tactic.skeleton->history x))
         (old-goals (tactic.skeleton->goals history)))
    (clause.clean-clauses-bldr old-goals proofs)))

(defobligations tactic.cleanup-compile
  (clause.clean-clauses-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.cleanup-okp tactic.cleanup-compile)))

 (verify-guards tactic.cleanup-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.cleanup-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.cleanup-compile x proofs))
                   (clause.clause-list-formulas
                    (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.cleanup-compile)
                        ))
            (equal (logic.proof-listp (tactic.cleanup-compile x proofs) axioms thms atbl)
                   t))))
