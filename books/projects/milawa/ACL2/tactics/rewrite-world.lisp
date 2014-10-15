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
(include-book "worldp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO this belongs in fast-urewrite.

(defund rw.fast-urewrite-list-list (x iffp control n)
  ;; Note: enabled! (via definition rule below)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (booleanp iffp)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards t))
  (if (consp x)
      (cons (rw.ftraces->rhses (rw.fast-urewrite-list (car x) iffp control n))
            (rw.fast-urewrite-list-list (cdr x) iffp control n))
      nil))

(defthm rw.fast-urewrite-list-list-removal
  (implies (force (and (logic.term-list-listp x)
                       (booleanp iffp)
                       (rw.controlp control)))
           (equal (rw.fast-urewrite-list-list x iffp control n)
                  (rw.trace-list-list-rhses (rw.urewrite-list-list x iffp control n))))
  :hints(("Goal" :in-theory (enable rw.fast-urewrite-list-list))))




;; Rewriting using Worlds.
;;
;; Tactic.world->control produces the control structure implied by a world.  We
;; show it is well-formed when the world is well-formed in the various ways.

(defund tactic.world->control (theoryname world)
  (declare (xargs :guard (tactic.worldp world)))
  ;; Creates the control structure implied by a world.
  (rw.control (tactic.world->noexec world)
              (tactic.world->forcingp world)
              (tactic.world->betamode world)
              (cdr (lookup theoryname (tactic.world->theories world)))
              (tactic.world->defs world)
              (tactic.world->depth world)
              (rw.assmctrl (tactic.world->assm-primaryp world)
                           (tactic.world->assm-secondaryp world)
                           (tactic.world->assm-directp world)
                           (tactic.world->assm-negativep world))))

(defthm rw.controlp-of-tactic.world->control
  (implies (force (tactic.worldp world))
           (equal (rw.controlp (tactic.world->control theoryname world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.world->control))))

(defthm rw.control-atblp-of-tactic.world->control
  (implies (force (tactic.world-atblp world atbl))
           (equal (rw.control-atblp (tactic.world->control theoryname world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world->control))))

(defthm rw.control-env-okp-of-tactic.world->control
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (rw.control-env-okp (tactic.world->control theoryname world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world->control))))




;; World-based wrappers for urewrite.
;;
;; These might look trivial, but we may use them as redefinition targets for
;; our bootstrapping process.  They shouldn't be inlined.

(defun rw.world-urewrite (x theoryname world)
  ;; Note: enabled!
  (declare (xargs :guard (and (logic.termp x)
                              (tactic.worldp world))))
  (rw.urewrite x t
               (tactic.world->control theoryname world)
               (tactic.world->urwn world)))

(defund rw.world-urewrite-list (x theoryname world)
  ;; Note: enabled!  (via definition rule below)
  (declare (xargs :guard (and (logic.term-listp x)
                              (tactic.worldp world))))
  (if (consp x)
      (cons (rw.world-urewrite (car x) theoryname world)
            (rw.world-urewrite-list (cdr x) theoryname world))
    nil))

(defund rw.world-urewrite-list-list (x theoryname world)
  ;; Note: enabled!  (via definition rule below)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (tactic.worldp world))))
  ;; Note: don't change this to be non-recursive.  We want to make sure it calls
  ;; rw.world-urewrite-list repeatedly, for bootstrapping redefinition purposes.
  (if (consp x)
      (cons (rw.world-urewrite-list (car x) theoryname world)
            (rw.world-urewrite-list-list (cdr x) theoryname world))
    nil))

(defthm rw.world-urewrite-list-redefinition
  (equal (rw.world-urewrite-list x theoryname world)
         (rw.urewrite-list x t
                           (tactic.world->control theoryname world)
                           (tactic.world->urwn world)))
  :hints(("Goal" :in-theory (enable rw.world-urewrite-list))))


(defthm rw.world-urewrite-list-list-redefinition
  (equal (rw.world-urewrite-list-list x theoryname world)
         (rw.urewrite-list-list x t
                                (tactic.world->control theoryname world)
                                (tactic.world->urwn world)))
  :hints(("Goal" :in-theory (enable rw.world-urewrite-list-list))))



;; World-based wrappers for fast-urewrite.
;;
;; Again these shouldn't be inlined since we may want them as redefinition
;; targets for our bootstrapping process.

(defun rw.fast-world-urewrite (x theoryname world)
  ;; Note: enabled!
  (declare (xargs :guard (and (logic.termp x)
                              (tactic.worldp world))))
  ;; BOZO why do we return the whole ftrace instead of just a term?
  (rw.fast-urewrite x t
                    (tactic.world->control theoryname world)
                    (tactic.world->urwn world)))

(defund rw.fast-world-urewrite-list (x theoryname world)
  ;; Note: enabled!  (via definition rule below)
  (declare (xargs :guard (and (logic.term-listp x)
                              (tactic.worldp world))))
  (if (consp x)
      (let ((car-rw (rw.fast-world-urewrite (car x) theoryname world))
            (cdr-rw (rw.fast-world-urewrite-list (cdr x) theoryname world)))
        (cons (rw.ftrace->rhs car-rw) cdr-rw))
    nil))

(defthm definition-of-rw.fast-world-urewrite-list
  (equal (rw.fast-world-urewrite-list x theoryname world)
         (rw.ftraces->rhses
          (rw.fast-urewrite-list x t
                                 (tactic.world->control theoryname world)
                                 (tactic.world->urwn world))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (e/d (rw.fast-world-urewrite-list
                           definition-of-rw.fast-urewrite-list)
                          ((:executable-counterpart acl2::force)
                           tactic.world->control))
          :restrict ((definition-of-rw.fast-urewrite-list ((x x)))))))

(defund rw.fast-world-urewrite-list-list (x theoryname world)
  ;; Note: enabled!  (via definition rule below)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (tactic.worldp world))))
  ;; Note: don't change this to be non-recursive.  We want to make sure it calls
  ;; rw.fast-world-urewrite-list repeatedly, for bootstrapping redefinition purposes.
  (if (consp x)
      (cons (rw.fast-world-urewrite-list (car x) theoryname world)
            (rw.fast-world-urewrite-list-list (cdr x) theoryname world))
    nil))

(defthm definition-of-rw.fast-world-urewrite-list-list
  (equal (rw.fast-world-urewrite-list-list x theoryname world)
         (rw.fast-urewrite-list-list x t
                                     (tactic.world->control theoryname world)
                                     (tactic.world->urwn world)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (e/d (rw.fast-world-urewrite-list-list
                           rw.fast-urewrite-list-list)
                          (rw.fast-urewrite-list-list-removal
                           (:executable-counterpart acl2::force)
                           tactic.world->control)))))


;; Proof-building wrappers
;;
;; These are used by the urewrite tactics and our waterfall tactic.  These
;; functions are not just trivial wrappers.  They provide an important target
;; for redefinition in the bootstrapping process; see Level 9.

(defund rw.world-urewrite-list-bldr (x result fastp theoryname world traces proof)
  (declare (xargs :guard (and (consp x)
                              (logic.term-listp x)
                              (logic.term-listp result)
                              (booleanp fastp)
                              (tactic.worldp world)
                              (equal result (rw.fast-world-urewrite-list x theoryname world))
                              (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (clause.clause-formula result))))
           (ignore result))
  ;; This is our main builder that gets redefined in level 9.
  (ACL2::prog2$
   (or (not fastp)
       (ACL2::cw "Warning: rw.world-urewrite-list-bldr having to do a slow urewrite to ~
                  build proofs in fast mode.~%"))
   (let ((traces (if fastp
                     (rw.world-urewrite-list x theoryname world)
                   traces))
         (control (tactic.world->control theoryname world))
         (urwn    (tactic.world->urwn world)))
     (rw.urewrite-clause-bldr x control urwn traces proof))))

(defobligations rw.world-urewrite-list-bldr
  (rw.urewrite-clause-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.world-urewrite-list-bldr)))

 (defthm logic.appealp-of-rw.world-urewrite-list-bldr
   (implies (force (and (consp x)
                        (logic.term-listp x)
                        (logic.term-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula result))))
            (equal (logic.appealp (rw.world-urewrite-list-bldr x result fastp theoryname world traces proof))
                   t)))

 (defthm logic.conclusion-of-rw.world-urewrite-list-bldr
   (implies (force (and (consp x)
                        (logic.term-listp x)
                        (logic.term-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula result))))
            (equal (logic.conclusion (rw.world-urewrite-list-bldr x result fastp theoryname world traces proof))
                   (clause.clause-formula x))))

 (defthm@ logic.proofp-of-rw.world-urewrite-list-bldr
   (implies (force (and (consp x)
                        (logic.term-listp x)
                        (logic.term-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula result))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (tactic.world-atblp world atbl)
                        (tactic.world-env-okp world axioms thms)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.world-urewrite-list-bldr)))
            (equal (logic.proofp (rw.world-urewrite-list-bldr x result fastp theoryname world traces proof)
                                 axioms thms atbl)
                   t))))



;; BOZO note if any problems consider tactic.fast-world-list-env-okp-correct in level9.lisp

(defthm logic.term-listp-of-rw.trace-list-rhses-free
  ;; BOZO find me a home
  (implies (and (equal free (rw.trace-list-rhses x))
                (force (rw.trace-listp x)))
           (equal (logic.term-listp free)
                  t)))

(defund rw.world-urewrite-list-bldr-high (x result fastp theoryname world traces proof)
  (declare (xargs :guard (and (consp x)
                              (logic.term-listp x)
                              (logic.term-listp result)
                              (booleanp fastp)
                              (tactic.worldp world)
                              (equal result (rw.fast-world-urewrite-list x theoryname world))
                              (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (clause.clause-formula result))))
           (ignore fastp traces))
  (logic.appeal 'rw.world-urewrite-list-bldr
                (clause.clause-formula x)
                (list proof)
                (list x result theoryname (tactic.world->index world))))

(defund rw.world-urewrite-list-bldr-okp (x worlds atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.world-urewrite-list-bldr)
         (tuplep 1 subproofs)
         (tuplep 4 extras)
         (let* ((orig-clause   (first extras))
                (result-clause (second extras))
                (theoryname    (third extras))
                (windex        (fourth extras))
                (world         (tactic.find-world windex worlds))
                (subconc       (logic.conclusion (first subproofs))))
           (and world
                (consp orig-clause)
                (consp result-clause)
                (logic.term-listp orig-clause)
                (logic.term-list-atblp orig-clause atbl)
                (equal (rw.fast-world-urewrite-list orig-clause theoryname world)
                       result-clause)
                (equal subconc (clause.clause-formula result-clause))
                (equal conclusion (clause.clause-formula orig-clause)))))))

(defthm rw.world-urewrite-list-bldr-okp-of-rw.world-urewrite-list-bldr-high
  ;; This isn't strictly necessary, but helps make sure we haven't screwed
  ;; anything up.
  (implies (and (consp x)
                (logic.term-listp x)
                (logic.term-listp result)
                (booleanp fastp)
                (tactic.worldp world)
                (equal result (rw.fast-world-urewrite-list x theoryname world))
                (or fastp (equal traces (rw.world-urewrite-list x theoryname world)))
                (logic.appealp proof)
                (equal (logic.conclusion proof) (clause.clause-formula result))
                ;; --- hrmn, some non-guard things that ought to be true ---
                (logic.term-list-atblp x atbl)
                (equal (tactic.find-world (tactic.world->index world) worlds) world))
           (equal (rw.world-urewrite-list-bldr-okp
                   (rw.world-urewrite-list-bldr-high x result fastp theoryname world traces proof)
                   worlds atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.world-urewrite-list-bldr-high
                                  rw.world-urewrite-list-bldr-okp)))))

(encapsulate
 ()
 (local (in-theory (enable rw.world-urewrite-list-bldr-okp)))

 (defthm booleanp-of-rw.world-urewrite-list-bldr-okp
   (equal (booleanp (rw.world-urewrite-list-bldr-okp x worlds atbl))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.world-urewrite-list-bldr-okp-of-logic.appeal-identity
   (equal (rw.world-urewrite-list-bldr-okp (logic.appeal-identity x) worlds atbl)
          (rw.world-urewrite-list-bldr-okp x worlds atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-rw.world-urewrite-list-bldr-okp
   (implies (and (rw.world-urewrite-list-bldr-okp x worlds atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (tactic.world-listp worlds)
                 (tactic.world-list-atblp worlds atbl)
                 (tactic.world-list-env-okp worlds axioms thms))
            (equal (logic.conclusion
                    (let ((orig-clause   (first (logic.extras x)))
                          (result-clause (second (logic.extras x)))
                          (theoryname    (third (logic.extras x)))
                          (fastp         t) ;; so no traces are needed
                          (world         (tactic.find-world (fourth (logic.extras x)) worlds))
                          (traces        nil) ;; since fastp is set
                          (proof         (logic.provable-witness (logic.conclusion
                                                                  (first (logic.subproofs x)))
                                                                 axioms thms atbl)))
                      (rw.world-urewrite-list-bldr orig-clause result-clause fastp theoryname
                                                   world traces proof)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-rw.world-urewrite-list-bldr-okp
  (implies (and (rw.world-urewrite-list-bldr-okp x worlds atbl)
                (logic.appealp x)
                (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                (tactic.world-listp worlds)
                (tactic.world-list-atblp worlds atbl)
                (tactic.world-list-env-okp worlds axioms thms)
                (equal (cdr (lookup 'if atbl)) 3)
                (equal (cdr (lookup 'not atbl)) 1)
                (equal (cdr (lookup 'equal atbl)) 2)
                (equal (cdr (lookup 'iff atbl)) 2)
                (@obligations rw.world-urewrite-list-bldr))
           (equal (logic.proofp
                   (let ((orig-clause   (first (logic.extras x)))
                         (result-clause (second (logic.extras x)))
                         (theoryname    (third (logic.extras x)))
                         (fastp         t) ;; so no traces are needed
                         (world         (tactic.find-world (fourth (logic.extras x)) worlds))
                         (traces        nil) ;; since fastp is set
                         (proof         (logic.provable-witness (logic.conclusion
                                                                 (first (logic.subproofs x)))
                                                                axioms thms atbl)))
                     (rw.world-urewrite-list-bldr orig-clause result-clause fastp theoryname
                                                  world traces proof))
                   axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.world-urewrite-list-bldr-okp
   (implies (and (rw.world-urewrite-list-bldr-okp x worlds atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (@obligations rw.world-urewrite-list-bldr))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :use ((:instance lemma-1-for-soundness-of-rw.world-urewrite-list-bldr-okp)
                  (:instance lemma-2-for-soundness-of-rw.world-urewrite-list-bldr-okp)
                  (:instance forcing-logic.provablep-when-logic.proofp
                             (x
                              (let ((orig-clause   (first (logic.extras x)))
                                    (result-clause (second (logic.extras x)))
                                    (theoryname    (third (logic.extras x)))
                                    (fastp         t) ;; so no traces are needed
                                    (world         (tactic.find-world (fourth (logic.extras x)) worlds))
                                    (traces        nil) ;; since fastp is set
                                    (proof         (logic.provable-witness (logic.conclusion
                                                                            (first (logic.subproofs x)))
                                                                           axioms thms atbl)))
                                (rw.world-urewrite-list-bldr orig-clause result-clause fastp theoryname
                                                             world traces proof)))))))))





(defund rw.world-urewrite-list-list-bldr (x result fastp theoryname world traces proofs)
  (declare (xargs :guard (and (cons-listp x)
                              (logic.term-list-listp x)
                              (logic.term-list-listp result)
                              (booleanp fastp)
                              (tactic.worldp world)
                              (equal result (rw.fast-world-urewrite-list-list x theoryname world))
                              (or fastp (equal traces (rw.world-urewrite-list-list x theoryname world)))
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (clause.clause-list-formulas result)))))
  ;; BOZO don't change this to be non-recursive.  We want to be sure to call
  ;; rw.world-urewrite-list-bldr repeatedly, for bootstrapping purposes.  Each
  ;; rw.world-urewrite-list will become a single proof step at the high levels.
  ;; But we can't do multiple clauses at once in a regular appeal.

  ;;   ;; Non-recursive version, doesn't work for redef.
  ;;   (ACL2::prog2$
  ;;    (or (not fastp)
  ;;        (ACL2::cw "Warning: rw.world-urewrite-list-list-bldr having to do a slow urewrite to ~
  ;;                   build proofs in fast mode.~%"))
  ;;    (let ((traces (if fastp
  ;;                      (rw.world-urewrite-list-list x t theoryname world)
  ;;                    traces))
  ;;          (control (tactic.world->control theoryname world))
  ;;          (rwn     (tactic.world->rwn world)))
  ;;      (rw.urewrite-clause-list-bldr x control rwn traces proofs))))

  (if (consp x)
      (cons (rw.world-urewrite-list-bldr (car x) (car result) fastp theoryname world (car traces) (car proofs))
            (rw.world-urewrite-list-list-bldr (cdr x) (cdr result) fastp theoryname world (cdr traces) (cdr proofs)))
    nil))

(defobligations rw.world-urewrite-list-list-bldr
  (rw.urewrite-clause-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.world-urewrite-list-list-bldr)))

 (defthm logic.appeal-listp-of-rw.world-urewrite-list-bldr
   (implies (force (and (cons-listp x)
                        (logic.term-list-listp x)
                        (logic.term-list-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list-list x theoryname world)))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (clause.clause-list-formulas result))))
            (equal (logic.appeal-listp (rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs))
                   t)))

 (defthm logic.conclusion-of-rw.world-urewrite-list-list-bldr
   (implies (force (and (cons-listp x)
                        (logic.term-list-listp x)
                        (logic.term-list-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list-list x theoryname world)))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (clause.clause-list-formulas result))))
            (equal (logic.strip-conclusions
                    (rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs))
                   (clause.clause-list-formulas x))))

 (defthm@ logic.proofp-of-rw.world-urewrite-list-list-bldr
   (implies (force (and (cons-listp x)
                        (logic.term-list-listp x)
                        (logic.term-list-listp result)
                        (booleanp fastp)
                        (tactic.worldp world)
                        (equal result (rw.fast-world-urewrite-list-list x theoryname world))
                        (or fastp (equal traces (rw.world-urewrite-list-list x theoryname world)))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (clause.clause-list-formulas result))
                        ;; ---
                        (logic.term-list-list-atblp x atbl)
                        (tactic.world-atblp world atbl)
                        (tactic.world-env-okp world axioms thms)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.world-urewrite-list-list-bldr)))
            (equal (logic.proof-listp
                    (rw.world-urewrite-list-list-bldr x result fastp theoryname world traces proofs)
                    axioms thms atbl)
                   t))))

