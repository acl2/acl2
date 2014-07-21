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
(include-book "rewrite-world")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


; NOTE: see also the comments at the beginning of urewrite-first.lisp.

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defund tactic.urewrite-all-okp (x worlds)
   (declare (xargs :guard (and (tactic.skeletonp x)
                               (tactic.world-listp worlds))))
   (let ((goals   (tactic.skeleton->goals x))
         (tacname (tactic.skeleton->tacname x))
         (extras  (tactic.skeleton->extras x))
         (history (tactic.skeleton->history x)))
     (and (equal tacname 'urewrite-all)
          (tuplep 4 extras)
          (let* ((theoryname (first extras))
                 (fastp      (second extras))
                 (windex     (third extras))
                 (traces     (fourth extras)) ;; nil when fastp
                 (world      (tactic.find-world windex worlds))
                 (old-goals  (tactic.skeleton->goals history)))
            (and world
                 (booleanp fastp)
                 (if fastp
                     (and (equal goals (rw.fast-world-urewrite-list-list old-goals theoryname world))
                          (not (equal old-goals goals)))
                   (and (equal traces (rw.world-urewrite-list-list old-goals theoryname world))
                        (equal goals (rw.trace-list-list-rhses traces))
                        (not (equal old-goals goals))))))))))

(defthm booleanp-of-tactic.urewrite-all-okp
  (equal (booleanp (tactic.urewrite-all-okp x worlds))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.urewrite-all-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.urewrite-all-tac (x theoryname fastp world warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp world)
                              (booleanp warnp))))
  (let ((goals      (tactic.skeleton->goals x))
        (findtheory (lookup theoryname (tactic.world->theories world)))
        (windex     (tactic.world->index world)))
    (cond ((not (consp goals))
           (and warnp
                (ACL2::cw "~s0urewrite-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)))
          ((not findtheory)
           (and warnp
                (ACL2::cw "~s0urewrite-all-tac failure~s1: no theory named ~s2 is defined.~%" *red* *black* theoryname)))
          (fastp
           (let* ((new-goals (rw.fast-world-urewrite-list-list goals theoryname world)))
             (cond ((equal new-goals goals)
                    (and warnp
                         (ACL2::cw "~s0urewrite-all-tac failure~s1: no progress was made.~%" *red* *black*)))
                   (t
                    (tactic.extend-skeleton new-goals
                                            'urewrite-all
                                            (list theoryname t windex nil)
                                            x)))))
          (t
           (let* ((traces    (rw.world-urewrite-list-list goals theoryname world))
                  (new-goals (rw.trace-list-list-rhses traces)))
             (cond ((equal new-goals goals)
                    (and warnp
                         (ACL2::cw "~s0urewrite-all-tac failure~s1: no progress was made.~%" *red* *black*)))
                   (t
                    (tactic.extend-skeleton new-goals
                                            'urewrite-all
                                            (list theoryname nil windex traces)
                                            x))))))))

(defthm forcing-tactic.skeletonp-of-tactic.urewrite-all-tac
  (implies (and (tactic.urewrite-all-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.urewrite-all-tac x theoryname fastp world warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.urewrite-all-tac))))

(defthm forcing-tactic.urewrite-all-okp-of-tactic.urewrite-all-tac
  (implies (and (tactic.urewrite-all-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.world-listp worlds))
                (force (tactic.skeletonp x))
                (force (booleanp fastp))
                (force (equal world (tactic.find-world (tactic.world->index world) worlds))))
           (equal (tactic.urewrite-all-okp
                   (tactic.urewrite-all-tac x theoryname fastp world warnp)
                   worlds)
                  t))
  :hints(("Goal" :in-theory (enable tactic.urewrite-all-tac
                                    tactic.urewrite-all-okp))))


(defund tactic.urewrite-all-compile (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.urewrite-all-okp x worlds)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history      (tactic.skeleton->history x))
         (goals        (tactic.skeleton->goals x))
         (old-goals    (tactic.skeleton->goals history))
         (extras       (tactic.skeleton->extras x))
         (theoryname   (first extras))
         (fastp        (second extras))
         (windex       (third extras))
         (traces       (fourth extras))
         (world        (tactic.find-world windex worlds)))
    (rw.world-urewrite-list-list-bldr old-goals goals fastp theoryname world traces proofs)))

(defobligations tactic.urewrite-all-compile
  (rw.world-urewrite-list-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.urewrite-all-okp
                           tactic.urewrite-all-compile)))

 (verify-guards tactic.urewrite-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.urewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-all-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.urewrite-all-compile x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.urewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-all-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.urewrite-all-compile x worlds proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.urewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-all-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.world-list-atblp worlds atbl)
                        (tactic.world-list-env-okp worlds axioms thms)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.urewrite-all-compile)))
            (equal (logic.proof-listp (tactic.urewrite-all-compile x worlds proofs) axioms thms atbl)
                   t))))

