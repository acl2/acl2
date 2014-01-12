;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")

;; Main Tactics
(include-book "cleanup")
(include-book "conditional-eqsubst")
(include-book "conditional-eqsubst-all")
(include-book "crewrite-all")
(include-book "crewrite-first")
(include-book "elim")
(include-book "distribute-all")
(include-book "fertilize")
(include-book "generalize-all")
(include-book "generalize-first")
(include-book "induct")
(include-book "skip-all")
(include-book "skip-first")
(include-book "split-all")
(include-book "split-first")
(include-book "urewrite-all")
(include-book "urewrite-first")
(include-book "use")
(include-book "waterfall")

;; World-changing tactics
(include-book "simple-world-change")
(include-book "theory-change")

;; Other stuff
(include-book "world-check")

(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




;; BOZO move to arith?

(defthm |(< b d) when (= (+ a (+ b c)) d)|
  (implies (equal (+ a (+ b c)) d)
           (equal (< b d)
                  (not (and (zp a)
                            (zp c))))))

(defthm |(< a c) when (= (+ a b) c)|
  (implies (equal (+ a b) c)
           (equal (< a c)
                  (not (zp b)))))

(defthm |(< b c) when (= (+ a b) c)|
  (implies (equal (+ a b) c)
           (equal (< b c)
                  (not (zp a)))))



; COMPILING SKELETONS
;
; Our tactic interface creates an initial skeleton (which has the original
; goals to prove) and also records the initial world that was being used at the
; time these goals were proposed.  Then, as we apply tactics, the skeleton is
; extended so that the new steps/goals are at the front.  Ultimately we are
; left with a skeleton whose first step has no outstanding goals.
;
; To compile a skeleton, we want to walk from the "front" (the step with no
; outstanding goals) to the "back" (the step with the original goals).  At each
; step we are to be given a list of proofs that prove our outstanding goals,
; and our job is to prove the outstanding goals of the next step.  All of our
; step compilers are built to fit this framework, so this is mainly a job of
; gluing them all together.
;
; Until the addition of worlds, this was the entire story.  But now things are
; a little bit more complicated, because we need keep track of the world that
; was being used at the time the tactic was run.
;
; So compiling skeletons is now a two-pass process.
;
; In the first pass, we are going to generate a list of worlds that will be
; used in the second pass.  To do this, we walk the skeleton "backwards" (by
; doing the computation as the recursion unwinds).  So, we start with the very
; first skeleton step and assign it the initial world (which the proof building
; interface will record for us).  As we unwind, we apply the changes that were
; made to the world (such as enabling or disabling rules, etc.), so that we
; have the later worlds that were in use on later steps.  The result is a list
; of worlds that were used during the proof.  To keep this list small, we do
; not repeat the world for skeleton steps that don't change it, e.g., the
; application of most tactics.
;
; Finally, once we have generated the list of worlds that were to be used at
; each step, we then do the regular front-to-back walk of the skeleton, at each
; step compiling the proofs that are the goals for the next step.  The use of
; world indexes, which are incremented by each world changing step, allows us
; to find the proper world to use during each tactic.

(defund tactic.world-stepp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((tacname (tactic.skeleton->tacname x)))
    (or (equal tacname 'simple-change-world)
        (equal tacname 'e/d)
        (equal tacname 'create-theory)
        (equal tacname 'restrict)
        (equal tacname 'update-noexec)
        (equal tacname 'cheapen)
        )))

(defthm booleanp-of-tactic.world-stepp
  (equal (booleanp (tactic.world-stepp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-stepp))))



(defund tactic.world-step-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((tacname (tactic.skeleton->tacname x)))
    (cond ((equal tacname 'simple-change-world)  (tactic.simple-change-world-okp x))
          ((equal tacname 'e/d)                  (tactic.e/d-okp x))
          ((equal tacname 'create-theory)        (tactic.create-theory-okp x))
          ((equal tacname 'restrict)             (tactic.restrict-okp x))
          ((equal tacname 'update-noexec)        (tactic.update-noexec-okp x))
          ((equal tacname 'cheapen)              (tactic.cheapen-okp x))
          (t                                     t))))

(defthm booleanp-of-tactic.world-step-okp
  (equal (booleanp (tactic.world-step-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-step-okp))))

(defund tactic.worlds-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (and (tactic.world-step-okp x)
       (or (not (tactic.skeleton->tacname x))
           (tactic.worlds-okp (tactic.skeleton->history x)))))




;; Our skeleton compiler takes a list of worlds.  This is where we generate
;; that list.

(defund tactic.compile-worlds-step (x world)
  ;; World is the initial world before we take this step.  We produce the new
  ;; world which should be used after the step.
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp world)
                              (tactic.world-step-okp x))
                  :guard-hints (("Goal" :in-theory (enable tactic.world-step-okp)))))
  (let ((tacname (tactic.skeleton->tacname x)))
    (cond ((equal tacname 'simple-change-world) (tactic.simple-change-world-compile-world x world))
          ((equal tacname 'e/d)                 (tactic.e/d-compile-world x world))
          ((equal tacname 'create-theory)       (tactic.create-theory-compile-world x world))
          ((equal tacname 'restrict)            (tactic.restrict-compile-world x world))
          ((equal tacname 'update-noexec)       (tactic.update-noexec-compile-world x world))
          ((equal tacname 'cheapen)             (tactic.cheapen-compile-world x world))
          (t
           ;; Many tactics don't change the world.  This makes it so that we
           ;; don't have to bother listing them.
           world))))

(defthm tactic.worldp-of-tactic.compile-worlds-step
  (implies (force (and (tactic.skeletonp x)
                       (tactic.worldp world)
                       (tactic.world-step-okp x)))
           (equal (tactic.worldp (tactic.compile-worlds-step x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds-step
                                    tactic.world-step-okp))))

(defthm tactic.world-atblp-of-tactic.compile-worlds-step
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.skeletonp x)
                       (tactic.worldp world)
                       (tactic.world-step-okp x)))
           (equal (tactic.world-atblp (tactic.compile-worlds-step x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds-step
                                    tactic.world-step-okp))))

(defthm tactic.world-env-okp-of-tactic.compile-worlds-step
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.skeletonp x)
                       (tactic.world-step-okp x)))
           (equal (tactic.world-env-okp (tactic.compile-worlds-step x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds-step
                                    tactic.world-step-okp))))

(defthm tactic.world->index-of-tactic.compile-worlds-step
  (implies (and (tactic.world-stepp x)
                (tactic.worldp world))
           (equal (tactic.world->index (tactic.compile-worlds-step x world))
                  (+ 1 (tactic.world->index world))))
  :hints(("Goal" :in-theory (enable tactic.world-stepp
                                    tactic.compile-worlds-step
                                    tactic.simple-change-world-compile-world
                                    tactic.update-noexec-compile-world
                                    tactic.create-theory-compile-world
                                    tactic.e/d-compile-world
                                    tactic.restrict-compile-world
                                    tactic.cheapen-compile-world
                                    ))))



(defund tactic.compile-worlds (x initial-world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp initial-world)
                              (tactic.worlds-okp x))
                  :verify-guards nil))
  (if (not (tactic.skeleton->tacname x))
      (list initial-world)
    (if (tactic.world-stepp x)
        (let* ((prev-worlds (tactic.compile-worlds (tactic.skeleton->history x)
                                                   initial-world))
               (prev-world  (car prev-worlds)))
          (cons (tactic.compile-worlds-step x prev-world)
                prev-worlds))
      (tactic.compile-worlds (tactic.skeleton->history x) initial-world))))

(defthm consp-of-tactic.compile-worlds
  (equal (consp (tactic.compile-worlds x world))
         t)
  :hints(("Goal" :in-theory (enable tactic.compile-worlds))))

(defthm tactic.world-listp-of-tactic.compile-worlds
  (implies (force (and (tactic.worldp world)
                       (tactic.skeletonp x)
                       (tactic.worlds-okp x)))
           (equal (tactic.world-listp (tactic.compile-worlds x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds
                                    tactic.worlds-okp))))

(defthm tactic.world-list-atblp-of-tactic.compile-worlds
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.skeletonp x)
                       (tactic.worlds-okp x)))
           (equal (tactic.world-list-atblp (tactic.compile-worlds x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds
                                    tactic.worlds-okp))))

(defthm tactic.world-list-env-okp-of-tactic.compile-worlds
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.skeletonp x)
                       (tactic.worlds-okp x)))
           (equal (tactic.world-list-env-okp (tactic.compile-worlds x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-worlds
                                    tactic.worlds-okp))))



(defund tactic.skeleton-step-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))
                  :export
                  (let ((tacname (tactic.skeleton->tacname x)))
                    (cond ((not tacname)                            t)
                          ((equal tacname 'cleanup)                 (tactic.cleanup-okp x))
                          ((equal tacname 'conditional-eqsubst)     (tactic.conditional-eqsubst-okp x))
                          ((equal tacname 'conditional-eqsubst-all) (tactic.conditional-eqsubst-all-okp x))
                          ((equal tacname 'crewrite-all)            (tactic.crewrite-all-okp x worlds))
                          ((equal tacname 'crewrite-first)          (tactic.crewrite-first-okp x worlds))
                          ((equal tacname 'elim-first)              (tactic.elim-first-okp x))
                          ((equal tacname 'elim-all)                (tactic.elim-all-okp x))
                          ((equal tacname 'distribute-all)          (tactic.distribute-all-okp x))
                          ((equal tacname 'fertilize)               (tactic.fertilize-okp x))
                          ((equal tacname 'generalize-all)          (tactic.generalize-all-okp x))
                          ((equal tacname 'generalize-first)        (tactic.generalize-first-okp x))
                          ((equal tacname 'induct)                  (tactic.induct-okp x))
                          ;((equal tacname 'skip-all)                (tactic.skip-all-okp x))
                          ;((equal tacname 'skip-first)              (tactic.skip-first-okp x))
                          ((equal tacname 'split-all)               (tactic.split-all-okp x))
                          ((equal tacname 'split-first)             (tactic.split-first-okp x))
                          ((equal tacname 'urewrite-all)            (tactic.urewrite-all-okp x worlds))
                          ((equal tacname 'urewrite-first)          (tactic.urewrite-first-okp x worlds))
                          ((equal tacname 'use)                     (tactic.use-okp x))
                          ((equal tacname 'waterfall)               (tactic.waterfall-okp x worlds))
                          ((tactic.world-stepp x)                   (tactic.world-step-okp x))
                          (t nil)))))
  (let ((tacname (tactic.skeleton->tacname x)))
    (cond ((not tacname)                            t)
          ((equal tacname 'cleanup)                 (tactic.cleanup-okp x))
          ((equal tacname 'conditional-eqsubst)     (tactic.conditional-eqsubst-okp x))
          ((equal tacname 'conditional-eqsubst-all) (tactic.conditional-eqsubst-all-okp x))
          ((equal tacname 'crewrite-all)            (tactic.crewrite-all-okp x worlds))
          ((equal tacname 'crewrite-first)          (tactic.crewrite-first-okp x worlds))
          ((equal tacname 'elim-first)              (tactic.elim-first-okp x))
          ((equal tacname 'elim-all)                (tactic.elim-all-okp x))
          ((equal tacname 'distribute-all)          (tactic.distribute-all-okp x))
          ((equal tacname 'fertilize)               (tactic.fertilize-okp x))
          ((equal tacname 'generalize-all)          (tactic.generalize-all-okp x))
          ((equal tacname 'generalize-first)        (tactic.generalize-first-okp x))
          ((equal tacname 'induct)                  (tactic.induct-okp x))
          ((equal tacname 'skip-all)                (tactic.skip-all-okp x))
          ((equal tacname 'skip-first)              (tactic.skip-first-okp x))
          ((equal tacname 'split-all)               (tactic.split-all-okp x))
          ((equal tacname 'split-first)             (tactic.split-first-okp x))
          ((equal tacname 'urewrite-all)            (tactic.urewrite-all-okp x worlds))
          ((equal tacname 'urewrite-first)          (tactic.urewrite-first-okp x worlds))
          ((equal tacname 'use)                     (tactic.use-okp x))
          ((equal tacname 'waterfall)               (tactic.waterfall-okp x worlds))
          ((tactic.world-stepp x)                   (tactic.world-step-okp x))
          (t nil))))

(defund tactic.skeleton-step-env-okp (x worlds axioms thms atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.skeleton-step-okp x worlds)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.skeleton-step-okp))))
           (ignore worlds))
  (let ((tacname (tactic.skeleton->tacname x)))
    (cond ((equal tacname 'conditional-eqsubst)     (tactic.conditional-eqsubst-env-okp x atbl))
          ((equal tacname 'conditional-eqsubst-all) (tactic.conditional-eqsubst-all-env-okp x atbl))
          ((equal tacname 'fertilize)               (tactic.fertilize-env-okp x atbl))
          ((equal tacname 'generalize-all)          (tactic.generalize-all-env-okp x atbl))
          ((equal tacname 'generalize-first)        (tactic.generalize-first-env-okp x atbl))
          ((equal tacname 'induct)                  (tactic.induct-env-okp x atbl))
          ((equal tacname 'use)                     (tactic.use-env-okp x axioms thms atbl))
          (t t))))

(defthm booleanp-of-tactic.skeleton-step-okp
  (equal (booleanp (tactic.skeleton-step-okp x worlds))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-step-okp))))

(defthm booleanp-of-tactic.skeleton-step-env-okp
  (equal (booleanp (tactic.skeleton-step-env-okp x worlds axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-step-env-okp))))




(defund tactic.skeleton-length (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (if (tactic.skeleton->tacname x)
      (+ 1 (tactic.skeleton-length (tactic.skeleton->history x)))
    1))

(defthm natp-of-tactic.skeleton-length
  (equal (natp (tactic.skeleton-length x))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-length))))

(defthm tactic.skeleton-length-zero
  (equal (equal 0 (tactic.skeleton-length x))
         nil)
  :hints(("Goal" :in-theory (enable tactic.skeleton-length))))

(defthm tactic.skeleton-length-one
  (equal (equal 1 (tactic.skeleton-length x))
         (not (tactic.skeleton->tacname x)))
  :hints(("Goal" :in-theory (enable tactic.skeleton-length))))

(defthm tactic.skeleton-length-of-tactic.skeleton->history
  (implies (tactic.skeleton->tacname x)
           (equal (tactic.skeleton-length (tactic.skeleton->history x))
                  (- (tactic.skeleton-length x) 1)))
  :hints(("Goal" :in-theory (enable tactic.skeleton-length))))

(defund tactic.compile-skeleton-step (x worlds proofs)
  (declare
   (xargs
    :guard (and (tactic.skeletonp x)
                (tactic.world-listp worlds)
                (tactic.skeleton-step-okp x worlds)
                (logic.appeal-listp proofs)
                (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                       (logic.strip-conclusions proofs)))
    :guard-hints (("Goal" :in-theory (enable tactic.skeleton-step-okp)))
    :export
    (let* ((tacname    (tactic.skeleton->tacname x))
           (new-proofs (cond ((not tacname)                             proofs)

                             ;; Main tactics
                             ((equal tacname 'cleanup)                  (tactic.cleanup-compile x proofs))
                             ((equal tacname 'conditional-eqsubst)      (tactic.conditional-eqsubst-compile x proofs))
                             ((equal tacname 'conditional-eqsubst-all)  (tactic.conditional-eqsubst-all-compile x proofs))
                             ((equal tacname 'crewrite-all)             (tactic.crewrite-all-compile x worlds proofs))
                             ((equal tacname 'crewrite-first)           (tactic.crewrite-first-compile x worlds proofs))
                             ((equal tacname 'distribute-all)           (tactic.distribute-all-compile x proofs))
                             ((equal tacname 'elim-first)               (tactic.elim-first-compile x proofs))
                             ((equal tacname 'elim-all)                 (tactic.elim-all-compile x proofs))
                             ((equal tacname 'fertilize)                (tactic.fertilize-compile x proofs))
                             ((equal tacname 'generalize-all)           (tactic.generalize-all-compile x proofs))
                             ((equal tacname 'generalize-first)         (tactic.generalize-first-compile x proofs))
                             ((equal tacname 'induct)                   (tactic.induct-compile x proofs))
                             ;;((equal tacname 'skip-all)                 (tactic.skip-all-compile x proofs))
                             ;;((equal tacname 'skip-first)               (tactic.skip-first-compile x proofs))
                             ((equal tacname 'split-all)                (tactic.split-all-compile x proofs))
                             ((equal tacname 'split-first)              (tactic.split-first-compile x proofs))
                             ((equal tacname 'urewrite-all)             (tactic.urewrite-all-compile x worlds proofs))
                             ((equal tacname 'urewrite-first)           (tactic.urewrite-first-compile x worlds proofs))
                             ((equal tacname 'use)                      (tactic.use-compile x proofs))
                             ((equal tacname 'waterfall)                (tactic.waterfall-compile x worlds proofs))

                             ((tactic.world-stepp x)                    proofs)
                             (t nil))))
      new-proofs)))
  (let* ((tacname    (tactic.skeleton->tacname x))
         (new-proofs
          (ACL2::prog2$
           (ACL2::cw! "; Compiling skeleton step #~x0: ~x1.~|" (tactic.skeleton-length x) tacname)
           (cond ((not tacname)                             proofs)

                 ;; Main tactics
                 ((equal tacname 'cleanup)                  (tactic.cleanup-compile x proofs))
                 ((equal tacname 'conditional-eqsubst)      (tactic.conditional-eqsubst-compile x proofs))
                 ((equal tacname 'conditional-eqsubst-all)  (tactic.conditional-eqsubst-all-compile x proofs))
                 ((equal tacname 'crewrite-all)             (tactic.crewrite-all-compile x worlds proofs))
                 ((equal tacname 'crewrite-first)           (tactic.crewrite-first-compile x worlds proofs))
                 ((equal tacname 'distribute-all)           (tactic.distribute-all-compile x proofs))
                 ((equal tacname 'elim-first)               (tactic.elim-first-compile x proofs))
                 ((equal tacname 'elim-all)                 (tactic.elim-all-compile x proofs))
                 ((equal tacname 'fertilize)                (tactic.fertilize-compile x proofs))
                 ((equal tacname 'generalize-all)           (tactic.generalize-all-compile x proofs))
                 ((equal tacname 'generalize-first)         (tactic.generalize-first-compile x proofs))
                 ((equal tacname 'induct)                   (tactic.induct-compile x proofs))
                 ((equal tacname 'skip-all)                 (tactic.skip-all-compile x proofs))
                 ((equal tacname 'skip-first)               (tactic.skip-first-compile x proofs))
                 ((equal tacname 'split-all)                (tactic.split-all-compile x proofs))
                 ((equal tacname 'split-first)              (tactic.split-first-compile x proofs))
                 ((equal tacname 'urewrite-all)             (tactic.urewrite-all-compile x worlds proofs))
                 ((equal tacname 'urewrite-first)           (tactic.urewrite-first-compile x worlds proofs))
                 ((equal tacname 'use)                      (tactic.use-compile x proofs))
                 ((equal tacname 'waterfall)                (tactic.waterfall-compile x worlds proofs))

                 ((tactic.world-stepp x)                    proofs)
                 (t nil)))))
    (ACL2::prog2$
     (ACL2::cw! "; Finishing ~x0.  Incremental Cost: ~s1.  Total cost: ~s2~|"
                tacname
                (STR::pretty-number (- (unbounded-rank new-proofs)
                                       (unbounded-rank proofs)))
                (STR::pretty-number (unbounded-rank new-proofs)))
     new-proofs)))

(defobligations tactic.compile-skeleton-step
  (tactic.cleanup-compile
   tactic.conditional-eqsubst-compile
   tactic.conditional-eqsubst-compile-all
   tactic.crewrite-all-compile
   tactic.crewrite-first-compile
   tactic.distribute-all-compile
   tactic.elim-first-compile
   tactic.elim-all-compile
   tactic.fertilize-compile
   tactic.generalize-all-compile
   tactic.generalize-first-compile
   tactic.induct-compile
   tactic.skip-all-compile
   tactic.skip-first-compile
   tactic.split-all-compile
   tactic.split-first-compile
   tactic.urewrite-all-compile
   tactic.urewrite-first-compile
   tactic.use-compile
   tactic.waterfall-compile
   ))

(encapsulate
 ()
 (local (in-theory (enable tactic.skeleton-step-okp
                           tactic.skeleton-step-env-okp
                           tactic.compile-skeleton-step
                           tactic.world-stepp
                           tactic.world-step-okp
                           )))

 (defthm forcing-logic.appeal-listp-of-tactic.compile-skeleton-step
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-step-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.compile-skeleton-step x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.compile-skeleton-step
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-step-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.compile-skeleton-step x worlds proofs))
                   (if (tactic.skeleton->tacname x)
                       (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x)))
                     (clause.clause-list-formulas (tactic.skeleton->goals x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.compile-skeleton-step
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-step-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-step-env-okp x worlds axioms thms atbl)
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (tactic.world-list-atblp worlds atbl)
                        (tactic.world-list-env-okp worlds axioms thms)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'ord< atbl)) 2)
                        (equal (cdr (lookup 'ordp atbl)) 1)
                        (equal (cdr (lookup 'car atbl)) 1)
                        (equal (cdr (lookup 'cdr atbl)) 1)
                        (equal (cdr (lookup 'consp atbl)) 1)
                        (equal (cdr (lookup 'cons atbl)) 2)
                        (@obligations tactic.compile-skeleton-step)))
            (equal (logic.proof-listp (tactic.compile-skeleton-step x worlds proofs) axioms thms atbl)
                   t))))



(defund tactic.skeleton-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))))
  (if (tactic.skeleton->tacname x)
      (and (tactic.skeleton-step-okp x worlds)
           (tactic.skeleton-okp (tactic.skeleton->history x) worlds))
    t))

(defthm booleanp-of-tactic.skeleton-okp
  (equal (booleanp (tactic.skeleton-okp x worlds))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-okp))))



(defund tactic.skeleton-env-okp (x worlds axioms thms atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.skeleton-okp x worlds)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.skeleton-okp)))))
  (if (tactic.skeleton->tacname x)
      (and (tactic.skeleton-step-env-okp x worlds axioms thms atbl)
           (tactic.skeleton-env-okp (tactic.skeleton->history x) worlds axioms thms atbl))
    t))

(defthm booleanp-of-tactic.skeleton-env-okp
  (equal (booleanp (tactic.skeleton-env-okp x worlds axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-env-okp))))




(defund tactic.compile-skeleton (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.skeleton-okp x worlds)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (if (not (tactic.skeleton->tacname x))
      proofs
    (tactic.compile-skeleton (tactic.skeleton->history x) worlds
                             (tactic.compile-skeleton-step x worlds proofs))))

(defobligations tactic.compile-skeleton
  (tactic.compile-skeleton-step))

(encapsulate
 ()
 (local (in-theory (enable tactic.skeleton-okp
                           tactic.skeleton-env-okp
                           tactic.compile-skeleton)))

 (verify-guards tactic.compile-skeleton
                :hints(("Goal" :do-not-induct t)))

 (defthm forcing-logic.appeal-listp-of-tactic.compile-skeleton
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.compile-skeleton x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.compile-skeleton
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.compile-skeleton x worlds proofs))
                   (clause.clause-list-formulas (tactic.original-conclusions x))))
   :hints(("Goal" :in-theory (enable tactic.original-conclusions))))

 (defthm@ forcing-logic.proof-listp-of-tactic.compile-skeleton
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.skeleton-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.skeleton-env-okp x worlds axioms thms atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (tactic.world-list-atblp worlds atbl)
                        (tactic.world-list-env-okp worlds axioms thms)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'ordp atbl)) 1)
                        (equal (cdr (lookup 'ord< atbl)) 2)
                        (equal (cdr (lookup 'car atbl)) 1)
                        (equal (cdr (lookup 'cdr atbl)) 1)
                        (equal (cdr (lookup 'consp atbl)) 1)
                        (equal (cdr (lookup 'cons atbl)) 2)
                        (@obligations tactic.compile-skeleton)))
            (equal (logic.proof-listp (tactic.compile-skeleton x worlds proofs) axioms thms atbl)
                   t))))




;; The high-level version of our skeleton compiler is kind of strange.  Note
;; that the low-level one produces a list of proofs, and we have never
;; redefined a function that produces a list of proofs before.
;;
;; In practice, the obligations of the skeleton are always a singleton list for
;; %autoprove and %prove events.  But in %admit, we sometimes have termination
;; obligations which are put into multiple goals.
;;
;; One solution to this, which would be fairly nice, would be to change the
;; way admission obligations are done, and basically "and" together all of the
;; obligations into a single formula.  Then, there would always be only one
;; formula for each skeleton.
;;
;; We use perhaps a worse alternative, which is to create a separate "skeleton
;; step" for each obligation in the skeleton.  The bad part of this if a skeleton
;; proves F1, F2, ..., FN, then we have to check the whole skeleton N times.
;;
;; As mentioned, N != 1 only when we are admitting functions, and usually those
;; are not bad proofs.  So, for now we just accept that.  If it ever becomes
;; a problem, we should switch the way termination obligations are handled.

(defund tactic.compile-skeleton-okp (x worlds axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'tactic.compile-skeleton)
         (acl2::time$ (tactic.skeletonp extras))
         (acl2::time$ (tactic.skeleton-okp extras worlds))
         (acl2::time$ (tactic.fast-skeleton-atblp extras atbl))
         (acl2::time$ (tactic.skeleton-env-okp extras worlds axioms thms atbl))
         (memberp conclusion
                  (clause.clause-list-formulas (tactic.original-conclusions extras)))
         (equal (logic.strip-conclusions subproofs)
                (clause.clause-list-formulas (tactic.skeleton->goals extras))))))

(defthm booleanp-of-tactic.compile-skeleton-okp
  (equal (booleanp (tactic.compile-skeleton-okp x worlds axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.compile-skeleton-okp)
                                 ((:executable-counterpart acl2::force))))))


;; Funny to make a list of same-typed, same-subproofs, same-extras appeals, but
;; I guess that's what we want.
(defprojection :list (logic.appeal-list method x subproofs extras)
               :element (logic.appeal method x subproofs extras)
               :guard (and (symbolp method)
                           (logic.formula-listp x)
                           (logic.appeal-listp subproofs)
                           (true-listp subproofs)))

(defund tactic.compile-skeleton-high (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.skeleton-okp x worlds)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs))))
           (ignore worlds))
  (logic.appeal-list 'tactic.compile-skeleton
                     (clause.clause-list-formulas (tactic.original-conclusions x))
                     (list-fix proofs)
                     x))


;; Just to show that tactic.compile-skeleton-high works as expected, we introduce
;; this notion.

(deflist tactic.compile-skeleton-list-okp (x worlds axioms thms atbl)
  (tactic.compile-skeleton-okp x worlds axioms thms atbl)
  :guard (and (logic.appeal-listp x)
              (tactic.world-listp worlds)
              (logic.formula-listp axioms)
              (logic.formula-listp thms)
              (logic.arity-tablep atbl)))

(defthm tactic.compile-skeleton-list-okp-of-logic.appeal-list
  (implies (force (and (symbolp method)
                       (logic.formula-listp conclusions)
                       (logic.appeal-listp subproofs)
                       (true-listp subproofs)
                       (mapp atbl)
                       ))
           (equal (tactic.compile-skeleton-list-okp
                   (logic.appeal-list method conclusions subproofs extras)
                   worlds axioms thms atbl)
                  (or
                   (not (consp conclusions))
                   (and
                    (equal method 'tactic.compile-skeleton)
                    (tactic.skeletonp extras)
                    (tactic.skeleton-okp extras worlds)
                    (tactic.skeleton-atblp extras atbl)
                    (tactic.skeleton-env-okp extras worlds axioms thms atbl)
                    (subsetp conclusions (clause.clause-list-formulas (tactic.original-conclusions extras)))
                    (equal (logic.strip-conclusions subproofs)
                           (clause.clause-list-formulas (tactic.skeleton->goals extras)))))))
  :hints(("Goal"
          :in-theory (enable tactic.compile-skeleton-okp)
          :induct (cdr-induction conclusions))))

(defthm tactic.compile-skeleton-list-okp-of-tactic.compile-skeleton-high
  (implies (and (tactic.skeletonp x)
                (tactic.world-listp worlds)
                (tactic.skeleton-okp x worlds)
                (logic.appeal-listp proofs)
                (mapp atbl)
                (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                       (logic.strip-conclusions proofs))
                ;; -----
                ;; hrmn, non-guard things that need to hold.
                (tactic.skeleton-atblp x atbl)
                (tactic.skeleton-env-okp x worlds axioms thms atbl)
                )
           (equal (tactic.compile-skeleton-list-okp
                   (tactic.compile-skeleton-high x worlds proofs)
                   worlds axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.compile-skeleton-high))))





(encapsulate
 ()
 (local (in-theory (enable tactic.compile-skeleton-okp)))

 (defthm tactic.compile-skeleton-okp-of-logic.appeal-identity
   (equal (tactic.compile-skeleton-okp (logic.appeal-identity x) worlds axioms thms atbl)
          (tactic.compile-skeleton-okp x worlds axioms thms atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-tactic.compile-skeleton-okp
   (implies (and (tactic.compile-skeleton-okp x worlds axioms thms atbl)
                 (logic.appealp x)
                 (mapp atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (tactic.world-listp worlds)
                 (tactic.world-list-atblp worlds atbl)
                 (tactic.world-list-env-okp worlds axioms thms))
            (equal (logic.conclusion
                    (let* ((skelly     (logic.extras x))
                           (in-proofs  (logic.provable-list-witness
                                        (logic.strip-conclusions (logic.subproofs x))
                                        axioms thms atbl))
                           (out-proofs (tactic.compile-skeleton skelly worlds in-proofs)))
                      (logic.find-proof (logic.conclusion x) out-proofs)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-tactic.compile-skeleton-okp
   (implies (and (tactic.compile-skeleton-okp x worlds axioms thms atbl)
                 (logic.appealp x)
                 (mapp atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (tactic.world-listp worlds)
                 (tactic.world-list-atblp worlds atbl)
                 (tactic.world-list-env-okp worlds axioms thms)
                 (equal (cdr (lookup 'if atbl)) 3)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'ordp atbl)) 1)
                 (equal (cdr (lookup 'ord< atbl)) 2)
                 (equal (cdr (lookup 'car atbl)) 1)
                 (equal (cdr (lookup 'cdr atbl)) 1)
                 (equal (cdr (lookup 'consp atbl)) 1)
                 (equal (cdr (lookup 'cons atbl)) 2)
                 (@obligations tactic.compile-skeleton))
            (equal (logic.proofp
                    (let* ((skelly     (logic.extras x))
                           (in-proofs  (logic.provable-list-witness
                                        (logic.strip-conclusions (logic.subproofs x))
                                        axioms thms atbl))
                           (out-proofs (tactic.compile-skeleton skelly worlds in-proofs)))
                      (logic.find-proof (logic.conclusion x) out-proofs))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-tactic.compile-skeleton-okp
   (implies (and (tactic.compile-skeleton-okp x worlds axioms thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'ordp atbl)) 1)
                             (equal (cdr (lookup 'ord< atbl)) 2)
                             (equal (cdr (lookup 'car atbl)) 1)
                             (equal (cdr (lookup 'cdr atbl)) 1)
                             (equal (cdr (lookup 'consp atbl)) 1)
                             (equal (cdr (lookup 'cons atbl)) 2)
                             (@obligations tactic.compile-skeleton))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :use ((:instance lemma-1-for-soundness-of-tactic.compile-skeleton-okp)
                  (:instance lemma-2-for-soundness-of-tactic.compile-skeleton-okp)
                  (:instance forcing-logic.provablep-when-logic.proofp
                             (x (let* ((skelly     (logic.extras x))
                                       (in-proofs  (logic.provable-list-witness
                                                    (logic.strip-conclusions (logic.subproofs x))
                                                    axioms thms atbl))
                                       (out-proofs (tactic.compile-skeleton skelly worlds in-proofs)))
                                  (logic.find-proof (logic.conclusion x) out-proofs)))))))))


