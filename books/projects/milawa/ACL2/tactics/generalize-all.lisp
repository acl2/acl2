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



(defund tactic.generalize-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'generalize-all)
         (consp extras)
         (let ((expr       (car extras)) ;; the term to generalize
               (var        (cdr extras)) ;; the new variable to generalize to
               (prev-goals (tactic.skeleton->goals history)))
           (and (consp prev-goals)
                (logic.termp expr)
                (logic.variablep var)
                (not (memberp var (logic.term-list-list-vars prev-goals)))
                (equal goals (logic.replace-subterm-list-list prev-goals expr var)))))))

(defund tactic.generalize-all-env-okp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.generalize-all-okp x)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.generalize-all-okp)))))
  (let* ((extras  (tactic.skeleton->extras x))
         (expr    (car extras)))
    (logic.term-atblp expr atbl)))


(defthm booleanp-of-tactic.generalize-all-okp
  (equal (booleanp (tactic.generalize-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.generalize-all-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm booleanp-of-tactic.generalize-all-env-okp
  (equal (booleanp (tactic.generalize-all-env-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.generalize-all-env-okp)
                                 ((:executable-counterpart acl2::force))))))




(defund tactic.generalize-all-tac (x expr var)
  ;; Replace occurrences of expr with var, a new variable
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.termp expr)
                              (logic.variablep var))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0generalize-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((clause-vars  (logic.term-list-list-vars goals))
             (replacements (logic.replace-subterm-list-list goals expr var)))
        (cond ((memberp var clause-vars)
               (ACL2::cw "~s0generalize-all-tac failure~s1: we need to use a fresh variable, but ~x2 ~
                          is already mentioned in some clause.~%" *red* *black* var))
              ((equal replacements goals)
               (ACL2::cw "~s0generalize-all-tac failure~s1: the clauses did not change due to this ~
                          generalization.~%" *red* *black*))
              (t
               (tactic.extend-skeleton replacements
                                       'generalize-all
                                       (cons expr var)
                                       x)))))))

(defthm forcing-tactic.skeletonp-of-tactic.generalize-all-tac
  (implies (and (tactic.generalize-all-tac x expr var)
                (force (logic.variablep var))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.generalize-all-tac x expr var))
                  t))
  :hints(("Goal" :in-theory (enable tactic.generalize-all-tac))))

(defthm forcing-tactic.generalize-all-okp-of-tactic.generalize-all-tac
  (implies (and (tactic.generalize-all-tac x expr var)
                (force (logic.termp expr))
                (force (logic.variablep var))
                (force (tactic.skeletonp x)))
           (equal (tactic.generalize-all-okp (tactic.generalize-all-tac x expr var))
                  t))
  :hints(("Goal" :in-theory (enable tactic.generalize-all-tac
                                    tactic.generalize-all-okp))))

(defthm forcing-tactic.generalize-all-env-okp-of-tactic.generalize-all-tac
  (implies (and (tactic.generalize-all-tac x expr var)
                (force (logic.termp expr))
                (force (logic.term-atblp expr atbl))
                (force (logic.variablep var))
                (force (tactic.skeletonp x)))
           (equal (tactic.generalize-all-env-okp (tactic.generalize-all-tac x expr var) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.generalize-all-tac
                                    tactic.generalize-all-env-okp))))





(defund tactic.generalize-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.generalize-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras        (tactic.skeleton->extras x))
         (expr          (car extras))
         (var           (cdr extras)))
    (build.instantiation-list proofs (list (cons var expr)))))

(defobligations tactic.generalize-all-compile
  (build.instantiation-list))


(encapsulate
 ()
 (local (in-theory (enable tactic.generalize-all-okp
                           tactic.generalize-all-env-okp
                           tactic.generalize-all-compile)))

 (defthm forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable-free
   (implies (and (equal y (logic.replace-subterm-list-list x old new))
                 (not (memberp new (logic.term-list-list-vars x)))
                 (logic.variablep new)
                 (force (logic.term-list-listp x)))
            (equal (logic.substitute-list-list y (list (cons new old)))
                   (list-list-fix x))))

 (verify-guards tactic.generalize-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.generalize-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.generalize-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.generalize-all-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.generalize-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.generalize-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.generalize-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.generalize-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.generalize-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.generalize-all-env-okp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.generalize-all-compile)))
            (equal (logic.proof-listp (tactic.generalize-all-compile x proofs) axioms thms atbl)
                   t))))
