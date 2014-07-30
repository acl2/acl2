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


; We combine fast and slow unconditional rewriting into a single tactic.
;
; Why not just use fast rewriting everywhere?  Fast rewriting is fine, but to
; emit proofs we need to call the slow rewriter anyway.  So, when we are doing
; the bootstrapping but before the rewriter is verified, if we used the fast
; rewriter we'd end up having to run the slow rewriter later on, anyway.  (This
; is actually convenient if we're just trying to find proofs, but overall it
; slows us down if we're also building proofs).
;
; Instead, we take a fastp flag and only use the fast rewriter if it is set.
; Effectively, this allows us to avoid the unnecessary "fast" rewrite and just
; use the slow rewriter to begin with; we then save the traces for the
; compiler.
;
; This approach also gives us a convenient target for redefinition.  That is,
; the tactic.urewrite-first-compile function can be redefined to build a high
; level, one-step proof in the later stages of bootstrapping when the rewriter
; is already verified.  But until then, it'll work just fine and emit low level
; proofs.

(defund tactic.urewrite-first-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'urewrite-first)
         (tuplep 4 extras)
         (let* ((theoryname (first extras))
                (fastp      (second extras))
                (windex     (third extras))
                (traces     (fourth extras)) ;; nil when fastp
                (world      (tactic.find-world windex worlds))
                (old-goals  (tactic.skeleton->goals history))
                (clause1    (car old-goals)))
           (and world
                (consp old-goals)
                (booleanp fastp)
                (if fastp
                    (let* ((rhses     (rw.fast-world-urewrite-list clause1 theoryname world))
                           (progressp (not (equal clause1 rhses))))
                      (and progressp
                           (equal (car goals) rhses)
                           (equal (cdr goals) (cdr old-goals))))
                  (let* ((clause1-rw (rw.world-urewrite-list clause1 theoryname world))
                         (rhses      (rw.trace-list-rhses clause1-rw))
                         (progressp  (not (equal clause1 rhses))))
                    (and progressp
                         (equal traces clause1-rw)
                         (equal (car goals) rhses)
                         (equal (cdr goals) (cdr old-goals))))))))))

(defthm booleanp-of-tactic.urewrite-first-okp
  (equal (booleanp (tactic.urewrite-first-okp x worlds))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.urewrite-first-okp)
                                 ((:executable-counterpart acl2::force))))))


(defund tactic.urewrite-first-tac (x theoryname fastp world warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (booleanp fastp)
                              (tactic.worldp world)
                              (booleanp warnp))))
  (let ((goals      (tactic.skeleton->goals x))
        (findtheory (lookup theoryname (tactic.world->theories world)))
        (windex     (tactic.world->index world)))
    (cond ((not (consp goals))
           (and warnp
                (ACL2::cw "~s0urewrite-first-tac failure~s1: all clauses have already been proven.~%" *red* *black*)))
          ((not findtheory)
           (and warnp
                (ACL2::cw "~s0urewrite-first-tac failure~s1: no theory named ~s2 is defined.~%" *red* *black* theoryname)))
          (fastp
           (let* ((clause1       (car goals))
                  (clause1-prime (rw.fast-world-urewrite-list clause1 theoryname world))
                  (progressp     (not (equal clause1 clause1-prime))))
             (cond ((not progressp)
                    (and warnp
                         (ACL2::cw "~s0urewrite-first-tac failure~s1: no progress was made.~%" *red* *black*)))
                   (t
                    (tactic.extend-skeleton (cons clause1-prime (cdr goals))
                                            'urewrite-first
                                            (list theoryname t windex nil)
                                            x)))))
          (t
           (let* ((clause1       (car goals))
                  (traces        (rw.world-urewrite-list clause1 theoryname world))
                  (clause1-prime (rw.trace-list-rhses traces))
                  (progressp     (not (equal clause1 clause1-prime))))
             (cond ((not progressp)
                    (and warnp
                         (ACL2::cw "~s0urewrite-first-tac failure~s1: no progress was made.~%" *red* *black*)))
                   (t
                    (tactic.extend-skeleton (cons clause1-prime (cdr goals))
                                            'urewrite-first
                                            (list theoryname nil windex traces)
                                            x))))))))

(defthm forcing-tactic.skeletonp-of-tactic.urewrite-first-tac
  (implies (and (tactic.urewrite-first-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.urewrite-first-tac x theoryname fastp world warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.urewrite-first-tac))))

(defthm forcing-tactic.urewrite-first-okp-of-tactic.urewrite-first-tac
  (implies (and (tactic.urewrite-first-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.world-listp worlds))
                (force (tactic.skeletonp x))
                (force (booleanp fastp))
                (force (equal world (tactic.find-world (tactic.world->index world) worlds))))
           (equal (tactic.urewrite-first-okp
                   (tactic.urewrite-first-tac x theoryname fastp world warnp)
                   worlds)
                  t))
  :hints(("Goal" :in-theory (enable tactic.urewrite-first-tac
                                    tactic.urewrite-first-okp))))




(defund tactic.urewrite-first-compile (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.urewrite-first-okp x worlds)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history      (tactic.skeleton->history x))
         (goals        (tactic.skeleton->goals x))
         (old-goals    (tactic.skeleton->goals history))
         (orig-goal1   (car old-goals))
         (extras       (tactic.skeleton->extras x))
         (theoryname   (first extras))
         (fastp        (second extras))
         (windex       (third extras))
         (traces       (fourth extras))
         (world        (tactic.find-world windex worlds)))
    (cons (rw.world-urewrite-list-bldr orig-goal1 (car goals) fastp theoryname world traces (car proofs))
          (cdr proofs))))

(defobligations tactic.urewrite-first-compile
  (rw.world-urewrite-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.urewrite-first-okp
                           tactic.urewrite-first-compile)))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.urewrite-first-compile
                :hints(("Goal" :do-not-induct t)))

 (defthm forcing-logic.appeal-listp-of-tactic.urewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.urewrite-first-compile x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.urewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.urewrite-first-compile x worlds proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.urewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.urewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.world-list-atblp worlds atbl)
                        (tactic.world-list-env-okp worlds axioms thms)
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.urewrite-first-compile)))
            (equal (logic.proof-listp (tactic.urewrite-first-compile x worlds proofs) axioms thms atbl)
                   t))))
