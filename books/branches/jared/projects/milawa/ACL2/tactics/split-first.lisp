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
(include-book "../clauses/split-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund tactic.split-first-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'split-first)
         (tuplep 4 extras)
         (let ((old-goals  (tactic.skeleton->goals history))
               (liftp      (first extras))
               (liftlimit  (second extras))
               (splitlimit (third extras))
               (split-len  (fourth extras)))
           (and (consp old-goals)
                (booleanp liftp)
                (natp liftlimit)
                (natp splitlimit)
                (let* ((clause1       (list-fix (car old-goals)))
                       (clause1-split (clause.split liftp liftlimit splitlimit clause1)))
                  (and (car clause1-split)
                       (equal split-len (len (cdr clause1-split)))
                       (equal (firstn split-len goals) (cdr clause1-split))
                       (equal (restn split-len goals) (cdr old-goals)))))))))

(defthm booleanp-of-tactic.split-first-okp
  (equal (booleanp (tactic.split-first-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.split-first-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.split-first-tac (liftp liftlimit splitlimit x)
  (declare (xargs :guard (and (booleanp liftp)
                              (natp liftlimit)
                              (natp splitlimit)
                              (tactic.skeletonp x))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0Split-first-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((clause1       (list-fix (car goals)))
             (clause1-split (clause.split liftp liftlimit splitlimit clause1))
             (split-len     (len (cdr clause1-split))))
        (if (not (car clause1-split))
            (ACL2::cw "~s0Split-first-tac failure~s1: the clause cannot be split further.~%" *red* *black*)
          (tactic.extend-skeleton (app (cdr clause1-split) (cdr goals))
                                  'split-first
                                  (list liftp liftlimit splitlimit split-len)
                                  x))))))

(defthm forcing-tactic.skeletonp-of-tactic.split-first-tac
  (implies (and (tactic.split-first-tac liftp liftlimit splitlimit x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.split-first-tac liftp liftlimit splitlimit x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.split-first-tac))))

(defthm forcing-tactic.split-first-okp-of-tactic.split-first-tac
  (implies (and (tactic.split-first-tac liftp liftlimit splitlimit x)
                (force (booleanp liftp))
                (force (natp liftlimit))
                (force (natp splitlimit))
                (force (tactic.skeletonp x)))
           (equal (tactic.split-first-okp (tactic.split-first-tac liftp liftlimit splitlimit x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.split-first-tac tactic.split-first-okp))))




(defund tactic.split-first-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.split-first-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history       (tactic.skeleton->history x))
         (old-goals     (tactic.skeleton->goals history))
         (clause1       (list-fix (car old-goals)))
         (extras        (tactic.skeleton->extras x))
         (liftp         (first extras))
         (liftlimit     (second extras))
         (splitlimit    (third extras))
         (len           (fourth extras))
         (split-proofs  (firstn len proofs))
         (other-proofs  (restn len proofs))
         (clause1-proof (clause.split-bldr liftp liftlimit splitlimit clause1 split-proofs)))
    (cons clause1-proof other-proofs)))

(defobligations tactic.split-first-compile
  (clause.split-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.split-first-okp tactic.split-first-compile)))

 (local (defthm crock
          (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                               (logic.strip-conclusions proofs))
                        (equal (firstn n goals) y))
                   (equal (logic.strip-conclusions (firstn n proofs))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
          :hints(("Goal"
                  :in-theory (disable firstn-of-logic.disjoin-each-formula-list)
                  :use ((:instance firstn-of-logic.disjoin-each-formula-list
                                   (x (logic.term-list-list-formulas goals))
                                   (y n)))))))

 (local (defthm crock2
          (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                               (logic.strip-conclusions proofs))
                        (equal (restn n goals) y))
                   (equal (logic.strip-conclusions (restn n proofs))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
          :hints(("Goal"
                  :in-theory (disable restn-of-logic.disjoin-each-formula-list)
                  :use ((:instance restn-of-logic.disjoin-each-formula-list
                                   (x (logic.term-list-list-formulas goals))
                                   (y n)))))))

 (verify-guards tactic.split-first-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.split-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.split-first-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.split-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.split-first-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.split-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.split-first-compile)))
            (equal (logic.proof-listp (tactic.split-first-compile x proofs) axioms thms atbl)
                   t))))
