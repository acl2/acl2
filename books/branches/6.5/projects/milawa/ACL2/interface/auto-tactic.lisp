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
(include-book "simple-tactics")
(include-book "rewrite-tactics")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (defund tactic.discover-elim-vars-for-goal (goal acc)
;;   ;; We search the goal for a term of the form (not (consp x)), where x is a
;;   ;; variable.  We return a list of all such x.  We also tolerate variants
;;   ;; of not.
;;   (declare (xargs :guard (logic.term-listp goal)))
;;   (if (consp goal)
;;       (if (not (clause.negative-termp (car goal)))
;;           (tactic.discover-elim-vars-for-goal (cdr goal) acc)
;;         (let ((guts (clause.negative-term-guts (car goal))))
;;           (if (and (logic.functionp guts)
;;                    (equal (logic.function-name guts) 'consp)
;;                    (equal (len (logic.function-args guts)) 1)
;;                    (logic.variablep (first (logic.function-args guts))))
;;               ;; This term has the form (not (consp x)).  We want
;;               ;; to add x to the list of vars.
;;               (tactic.discover-elim-vars-for-goal (cdr goal) (cons (first (logic.function-args guts)) acc))
;;             (tactic.discover-elim-vars-for-goal (cdr goal) acc))))
;;     acc))

;; (defthm logic.variable-listp-of-tactic.discover-elim-vars-for-goal
;;   (implies (logic.variable-listp acc)
;;            (equal (logic.variable-listp (tactic.discover-elim-vars-for-goal goal acc))
;;                   t))
;;   :hints(("Goal" :in-theory (enable tactic.discover-elim-vars-for-goal))))

;; (defund tactic.discover-elim-vars-for-all-goals (vars goals)
;;   ;; Vars are a list of vars we are considering eliminating.  We remove any
;;   ;; vars which are not discovered in all of the goals.  That is, the only vars
;;   ;; we keep are elim'able in every single goal.
;;   (declare (xargs :guard (and (logic.term-list-listp goals)
;;                               (cons-listp goals))))
;;   (if (consp goals)
;;       (tactic.discover-elim-vars-for-all-goals
;;        (intersect vars (tactic.discover-elim-vars-for-goal (car goals) nil))
;;        (cdr goals))
;;     vars))

;; (defthm logic.variable-listp-of-tactic.discover-elim-vars-for-all-goals
;;   (implies (logic.variable-listp vars)
;;            (equal (logic.variable-listp (tactic.discover-elim-vars-for-all-goals vars goals))
;;                   t))
;;   :hints(("Goal" :in-theory (enable tactic.discover-elim-vars-for-all-goals))))

;; (defund tactic.find-var-to-elim (goals)
;;   ;; We first discover the elim'able vars in the first goal.  We then remove
;;   ;; all the vars which aren't elim'able in later goals.  Finally we pick the
;;   ;; first remaining var if there is one.
;;   (declare (xargs :guard (and (logic.term-list-listp goals)
;;                               (cons-listp goals))))
;;   (and (consp goals)
;;        (car (tactic.discover-elim-vars-for-all-goals
;;              (tactic.discover-elim-vars-for-goal (car goals) nil)
;;              (cdr goals)))))

;; (defthm logic.variablep-of-tactic.find-var-to-elim
;;   (implies (tactic.find-var-to-elim goals)
;;            (equal (logic.variablep (tactic.find-var-to-elim goals))
;;                   t))
;;   :hints(("Goal" :in-theory (enable tactic.find-var-to-elim))))

;; (defund tactic.auto-elim-tac (x warnp)
;;   ;; We try to detect an elim'able variable and eliminate it.
;;   (declare (xargs :guard (and (tactic.skeletonp x)
;;                               (booleanp warnp))))
;;   (let ((goals (tactic.skeleton->goals x)))
;;     (if (not (consp goals))
;;         (and warnp
;;              (ACL2::cw "~s0auto-elim failure~s1: all goals are already proven.~%" *red* *black*))
;;       (let ((chosen-var (tactic.find-var-to-elim goals)))
;;         (if (not chosen-var)
;;             (and warnp
;;                  (ACL2::cw "~s0auto-elim failure~s1: no candidate variable detected.~%" *red* *black*))
;;           (tactic.conditional-eqsubst-all-tac x
;;                                               (logic.function 'consp (list chosen-var))
;;                                               chosen-var
;;                                               (logic.function 'cons (list (logic.function 'car (list chosen-var))
;;                                                                           (logic.function 'cdr (list chosen-var))))
;;                                               warnp))))))

;; (defthm forcing-tactic.skeletonp-of-tactic.auto-elim-tac
;;   (implies (and (tactic.auto-elim-tac x warnp)
;;                 (force (tactic.skeletonp x)))
;;            (equal (tactic.skeletonp (tactic.auto-elim-tac x warnp))
;;                   t))
;;   :hints(("Goal" :in-theory (enable tactic.auto-elim-tac))))




(defund tactic.apply-strategy-step (step x theoryname cfastp ufastp world names)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (elim.namesp names))))
  (let ((result (cond ((equal step 'cleanup)
                       (ACL2::prog2$ (ACL2::cw "(%cleanup)~|")
                                     (tactic.cleanup-tac x nil)))
                      ((equal step 'urewrite)
                       (ACL2::prog2$ (ACL2::cw "(%urewrite ~s0)~|" theoryname)
                                     (tactic.urewrite-all-tac x theoryname ufastp world nil)))
                      ((equal step 'crewrite)
                       (ACL2::prog2$ (ACL2::cw "(%crewrite ~s0)~|" theoryname)
                                     (tactic.crewrite-all-tac x theoryname cfastp world nil)))
                      ((equal step 'dist)
                       (ACL2::prog2$ (ACL2::cw "(%distribute)~|")
                                     (tactic.distribute-all-tac x nil)))
                      ((equal step 'split)
                       ;; At one point in time we just tried full splitting and if-lifting.  But this
                       ;; turned out to be far too expensive.  We added the liftlimit to prevent some
                       ;; lifting.  We can do even better by trying to do lift-free splitting initially.
                       ;; This lets us intersperse a cleanup pass between our cheap split and more
                       ;; aggressive splitting.
                       (ACL2::prog2$ (ACL2::cw "(%split)~|")
                                     (or (tactic.split-all-tac nil
                                                               (tactic.world->liftlimit world)
                                                               (tactic.world->splitlimit world)
                                                               x nil)
                                         ;; BOZO try adding another call with splitlimit=5 or
                                         ;; something else that's relatively low in here?
                                         (tactic.split-all-tac t
                                                               (tactic.world->liftlimit world)
                                                               (tactic.world->splitlimit world)
                                                               x nil))))
                      ((equal step 'elim)
                       (ACL2::prog2$ (ACL2::cw "(%car-cdr-elim)~|")
                                     (tactic.elim-all-tac x names nil)))
                      (t
                       (ACL2::cw "Error in %auto: tried to apply unknown step: ~x0.~%" step)))))
    (ACL2::prog2$ (if result
                      (ACL2::cw ";; Progress; ~x0 goals remain~|"
                                (fast-len (tactic.skeleton->goals result) 0))
                    (ACL2::cw ";; No progress~|"))
                  result)))

(defthm tactic.skeletonp-of-tactic.apply-strategy-step
  (implies (and (tactic.apply-strategy-step step x theoryname cfastp ufastp world names)
                (force (tactic.skeletonp x))
                (force (tactic.worldp world))
                (force (elim.namesp names)))
           (equal (tactic.skeletonp (tactic.apply-strategy-step step x theoryname cfastp ufastp world names))
                  t))
  :hints(("Goal" :in-theory (enable tactic.apply-strategy-step))))

(defund tactic.apply-strategy (strategy x theoryname cfastp ufastp world names)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (elim.namesp names))))
  (if (consp strategy)
      (or (tactic.apply-strategy-step (car strategy) x theoryname cfastp ufastp world names)
          (tactic.apply-strategy (cdr strategy) x theoryname cfastp ufastp world names))
    nil))

(defthm tactic.skeletonp-of-tactic.apply-strategy
  (implies (and (tactic.apply-strategy strategy x theoryname cfastp ufastp world names)
                (force (elim.namesp names))
                (force (tactic.skeletonp x))
                (force (tactic.worldp world)))
           (equal (tactic.skeletonp (tactic.apply-strategy strategy x theoryname cfastp ufastp world names))
                  t))
  :hints(("Goal" :in-theory (enable tactic.apply-strategy))))



(defund tactic.auto-tac (x strategy theoryname cfastp ufastp world names auto-n)
  ;; The auto tactic might be more properly called a "tactical" than a "tactic".
  ;; We try to repeatedly apply conditional rewriting, splitting, and
  ;; car-cdr-elim to simplify a goal.
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (elim.namesp names))
                  :measure (nfix auto-n)
                  :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force))))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        ;; All the goals are proven, we can stop.
        x
      (let ((step (tactic.apply-strategy strategy x theoryname cfastp ufastp world names)))
        (if step
            ;; Able to make some progress.  Continue our loop if we can.
            (if (zp auto-n)
                (ACL2::prog2$ (ACL2::cw "~s0warning~s1: out of steps in auto-tac.~%" *red* *black*)
                              step)
              (tactic.auto-tac step strategy theoryname cfastp ufastp world names (- auto-n 1)))
          ;; No progress was made.  Stop here.
          x)))))

(defun %tactic.auto-tac-wrapper (x strategy theoryname cfastp ufastp world names auto-n)
  ;; To avoid the expensive parts of guard-checking.
  (declare (xargs :mode :program))
  (tactic.auto-tac x strategy theoryname cfastp ufastp world names auto-n))

(defmacro %auto (&key (theory   'default)
                      (strategy '(cleanup split dist urewrite crewrite elim))
                      (steps    '500))
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton   ACL2::world))
                               (cfastp     (tactic.harness->cfastp     ACL2::world))
                               (ufastp     (tactic.harness->ufastp     ACL2::world))
                               (strategy   ',strategy)
                               (theoryname ',theory)
                               (world      (tactic.harness->world      ACL2::world))
                               (names      (%tactic.harness->create-elim-names-wrapper (tactic.skeleton->goals skelly)))
                               (auto-n     ',steps)
                               (new-skelly (%tactic.auto-tac-wrapper skelly strategy theoryname
                                                                     cfastp ufastp world names auto-n)))
                          new-skelly)))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))
    (local (%print))))

