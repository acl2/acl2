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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm rw.theory-env-okp-of-lookup-when-rw.theory-list-env-okp-of-range
  ;; BOZO find me a home
  (implies (rw.theory-list-env-okp (range theories) thms)
           (rw.theory-env-okp (cdr (lookup name theories)) thms))
  :hints(("Goal" :induct (cdr-induction theories))))

(defaggregate tactic.world
  (index
   forcingp
   betamode
   liftlimit
   splitlimit
   blimit
   rlimit
   rwn
   urwn
   noexec
   theories
   defs
   depth
   allrules
   assm-primaryp
   assm-secondaryp
   assm-directp
   assm-negativep
   )
  :require
  ((natp-of-tactic.world->index                         (natp index))
   (booleanp-of-tactic.world->forcingp                  (booleanp forcingp))
   (symbolp-of-tactic.world->betamode                   (symbolp betamode))
   (natp-of-tactic.world->liftlimit                     (natp liftlimit))
   (natp-of-tactic.world->splitlimit                    (natp splitlimit))
   (natp-of-tactic.world->blimit                        (natp blimit))
   (natp-of-tactic.world->rlimit                        (natp rlimit))
   (natp-of-tactic.world->rwn                           (natp rwn))
   (natp-of-tactic.world->urwn                          (natp urwn))
   (definition-listp-of-tactic.world->defs              (definition-listp defs))
   (natp-of-tactic.world->depth                         (natp depth))
   (rw.theory-mapp-of-tactic.world->theories            (rw.theory-mapp theories))
   (logic.function-symbol-listp-of-tactic.world->noexec (logic.function-symbol-listp noexec))
   (rw.rule-listp-of-tactic.world->allrules             (rw.rule-listp allrules))
   (booleanp-of-tactic.world->assm-primaryp             (booleanp assm-primaryp))
   (booleanp-of-tactic.world->assm-secondaryp           (booleanp assm-secondaryp))
   (booleanp-of-tactic.world->assm-directp              (booleanp assm-directp))
   (booleanp-of-tactic.world->assm-negativep            (booleanp assm-negativep))
   ))

(deflist tactic.world-listp (x)
  (tactic.worldp x)
  :elementp-of-nil nil)



(defund tactic.world-atblp (x atbl)
  (declare (xargs :guard (and (tactic.worldp x)
                              (logic.arity-tablep atbl))))
  (and (rw.theory-list-atblp-of-range (tactic.world->theories x) atbl)
       (rw.rule-list-atblp (tactic.world->allrules x) atbl)
       (logic.formula-list-atblp (tactic.world->defs x) atbl)))

(defthm booleanp-of-tactic.world-atblp
  (equal (booleanp (tactic.world-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))

(defthm tactic.world-atblp-of-nil
  (equal (tactic.world-atblp nil atbl)
         t)
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))

(defthmd lemma-for-rw.theory-atblp-of-looked-up-theory
  (implies (rw.theory-list-atblp (range theories) atbl)
           (equal (rw.theory-atblp (cdr (lookup theory theories)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction theories))))

(defthm rw.theory-atblp-of-looked-up-theory
  (implies (force (tactic.world-atblp x atbl))
           (equal (rw.theory-atblp (cdr (lookup theory (tactic.world->theories x))) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-atblp
                                    lemma-for-rw.theory-atblp-of-looked-up-theory))))

(defthm tactic.world-atblp-of-tactic.world
  (implies (and (force (rw.theory-list-atblp (range theories) atbl))
                (force (logic.formula-list-atblp defs atbl))
                (force (rw.rule-list-atblp allrules atbl)))
           (equal (tactic.world-atblp (tactic.world index forcingp betamode liftlimit splitlimit blimit
                                                    rlimit rwn urwn noexec theories defs depth allrules
                                                    assm-primaryp assm-secondaryp assm-directp
                                                    assm-negativep)
                                      atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))

(defthm rw.theory-list-atblp-of-range-of-tactic.world->theories
  (implies (force (tactic.world-atblp world atbl))
           (equal (rw.theory-list-atblp (range (tactic.world->theories world)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))

(defthm logic.formula-list-atblp-of-tactic.world->defs
  (implies (force (tactic.world-atblp x atbl))
           (equal (logic.formula-list-atblp (tactic.world->defs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))

(defthm rw.rule-list-atblp-of-tactic.world->allrules
  (implies (force (tactic.world-atblp x atbl))
           (equal (rw.rule-list-atblp (tactic.world->allrules x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-atblp))))




(deflist tactic.world-list-atblp (x atbl)
  (tactic.world-atblp x atbl)
  :guard (and (tactic.world-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)



(defund tactic.world-env-okp (x axioms thms)
  (declare (xargs :guard (and (tactic.worldp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms))))
  (and (rw.theory-list-env-okp-of-range (tactic.world->theories x) thms)
       (rw.rule-list-env-okp (tactic.world->allrules x) thms)
       (subsetp (tactic.world->defs x) axioms)))

(defthm booleanp-of-tactic.world-env-okp
  (equal (booleanp (tactic.world-env-okp x axioms thms))
         t)
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(defthm tactic.world-env-okp-of-nil
  (equal (tactic.world-env-okp nil axioms thms)
         t)
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(defthmd lemma-for-rw.theory-env-okp-of-looked-up-theory
  (implies (rw.theory-list-env-okp (range theories) thms)
           (equal (rw.theory-env-okp (cdr (lookup theory theories)) thms)
                  t))
  :hints(("Goal" :induct (cdr-induction theories))))

(defthm rw.theory-env-okp-of-looked-up-theory
  (implies (force (tactic.world-env-okp x axioms thms))
           (equal (rw.theory-env-okp (cdr (lookup theory (tactic.world->theories x))) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp
                                    lemma-for-rw.theory-env-okp-of-looked-up-theory))))

(defthm tactic.world-env-okp-of-tactic.world
  (implies (and (force (rw.theory-list-env-okp (range theories) thms))
                (force (rw.rule-list-env-okp allrules thms))
                (force (subsetp defs axioms)))
           (equal (tactic.world-env-okp (tactic.world index forcingp betamode liftlimit splitlimit blimit
                                                      rlimit rwn urwn noexec theories defs depth allrules
                                                      assm-primaryp assm-secondaryp assm-directp
                                                      assm-negativep)
                                        axioms
                                        thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(defthm rw.theory-list-env-okp-of-range-of-tactic.world->theories
; Matt K. mod for v7-2: Don't force assumption below with free variable.
  (implies (tactic.world-env-okp world axioms thms)
           (equal (rw.theory-list-env-okp (range (tactic.world->theories world)) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(defthm subsetp-of-tactic.world->defs-and-axioms
; Matt K. mod for v7-2: Don't force assumption below with free variable.
  (implies (tactic.world-env-okp world axioms thms)
           (equal (subsetp (tactic.world->defs world) axioms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(defthm rw.rule-list-env-okp-of-tactic.world->allrules
; Matt K. mod for v7-2: Don't force assumption below with free variable.
  (implies (tactic.world-env-okp world axioms thms)
           (equal (rw.rule-list-env-okp (tactic.world->allrules world) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.world-env-okp))))

(deflist tactic.world-list-env-okp (x axioms thms)
  (tactic.world-env-okp x axioms thms)
  :guard (and (tactic.world-listp x)
              (logic.formula-listp axioms)
              (logic.formula-listp thms))
  :elementp-of-nil t)



(defthm subsetp-of-tactic.world->defs-when-memberp
  (implies (and (memberp world worlds)
                (tactic.world-list-env-okp worlds axioms thms))
           (equal (subsetp (tactic.world->defs world) axioms)
                  t))
  :hints(("Goal" :induct (cdr-induction worlds))))

(defthm subsetp-of-tactic.world->defs-when-memberp-alt
  (implies (and (tactic.world-list-env-okp worlds axioms thms)
                (memberp world worlds))
           (equal (subsetp (tactic.world->defs world) axioms)
                  t)))

(defthm rw.theory-env-okp-when-memberp
  (implies (and (memberp world worlds)
                (tactic.world-list-env-okp worlds axioms thms))
           (equal (rw.theory-list-env-okp (range (tactic.world->theories world)) thms)
                  t))
  :hints(("Goal" :induct (cdr-induction worlds))))

(defthm rw.theory-env-okp-when-memberp-alt
  (implies (and (tactic.world-list-env-okp worlds axioms thms)
                (memberp world worlds))
           (equal (rw.theory-list-env-okp (range (tactic.world->theories world)) thms)
                  t))
  :hints(("Goal" :induct (cdr-induction worlds))))



(defund tactic.find-world (index worlds)
  (declare (xargs :guard (tactic.world-listp worlds)))
  (if (consp worlds)
      (if (equal (tactic.world->index (car worlds)) index)
          (car worlds)
        (tactic.find-world index (cdr worlds)))
    nil))

(defthm tactic.worldp-of-tactic.find-world-under-iff
  (implies (force (tactic.world-listp worlds))
           (iff (tactic.worldp (tactic.find-world index worlds))
                (tactic.find-world index worlds)))
  :hints(("Goal" :in-theory (enable tactic.find-world))))

(defthm tactic.world-atblp-of-tactic.find-world-under-iff
  (implies (force (tactic.world-list-atblp worlds atbl))
           (equal (tactic.world-atblp (tactic.find-world index worlds) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-world))))

(defthm tactic.world-env-okp-of-tactic.find-world-under-iff
  (implies (force (tactic.world-list-env-okp worlds axioms thms))
           (equal (tactic.world-env-okp (tactic.find-world index worlds) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-world))))

(defthm tactic.world->index-of-tactic.find-world
  (equal (tactic.world->index (tactic.find-world index worlds))
         (if (tactic.find-world index worlds)
             index
           nil))
  :hints(("Goal" :in-theory (enable tactic.find-world))))

(defthm subsetp-of-tactic.world->defs-of-tactic.find-world-and-axioms
  (implies (force (tactic.world-list-env-okp worlds axioms thms))
           (equal (subsetp (tactic.world->defs (tactic.find-world index worlds)) axioms)
                  t))
  :hints(("Goal"
          :in-theory (disable subsetp-of-tactic.world->defs-and-axioms)
          :use ((:instance subsetp-of-tactic.world->defs-and-axioms
                           (world (tactic.find-world index worlds)))))))

(defthm rw.theory-list-env-okp-of-range-of-tactic.world->theories-of-find-world
  (implies (force (tactic.world-list-env-okp worlds axioms thms))
           (equal (rw.theory-list-env-okp (range (tactic.world->theories (tactic.find-world world worlds)))
                                          thms)
                  t))
  :hints(("Goal"
          :in-theory (disable rw.theory-list-env-okp-of-range-of-tactic.world->theories)
          :use ((:instance rw.theory-list-env-okp-of-range-of-tactic.world->theories
                           (world (tactic.find-world world worlds)))))))


(defund tactic.increment-world-index (world)
  (declare (xargs :guard (tactic.worldp world)))
  (change-tactic.world world
                       :index (+ 1 (tactic.world->index world))))

(defthm tactic.worldp-of-tactic.increment-world-index
  (implies (force (tactic.worldp world))
           (equal (tactic.worldp (tactic.increment-world-index world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.increment-world-index))))

(defthm tactic.world-atblp-of-tactic.increment-world-index
  (implies (force (tactic.world-atblp world atbl))
           (equal (tactic.world-atblp (tactic.increment-world-index world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.increment-world-index))))

(defthm tactic.world-env-okp-of-tactic.increment-world-index
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (tactic.world-env-okp (tactic.increment-world-index world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.increment-world-index))))

(defthm tactic.world->index-of-tactic.increment-world-index
  (equal (tactic.world->index (tactic.increment-world-index world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.increment-world-index))))
