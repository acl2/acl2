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
(include-book "skeletonp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund tactic.simple-world-change-aux (changes world)
  (declare (xargs :guard (tactic.worldp world)))
  (if (consp changes)
      (let ((field (car (car changes)))
            (value (cdr (car changes))))
        (tactic.simple-world-change-aux
         (cdr changes)
         (cond ((equal field 'forcingp)   (change-tactic.world world :forcingp (if value t nil)))
               ((equal field 'betamode)   (change-tactic.world world :betamode (if (symbolp value) value nil)))

               ((equal field 'assm-primaryp)     (change-tactic.world world :assm-primaryp (if value t nil)))
               ((equal field 'assm-secondaryp)   (change-tactic.world world :assm-secondaryp (if value t nil)))
               ((equal field 'assm-directp)      (change-tactic.world world :assm-directp (if value t nil)))
               ((equal field 'assm-negativep)    (change-tactic.world world :assm-negativep (if value t nil)))

               ((equal field 'liftlimit)  (change-tactic.world world :liftlimit (nfix value)))
               ((equal field 'splitlimit) (change-tactic.world world :splitlimit (nfix value)))
               ((equal field 'blimit)     (change-tactic.world world :blimit (nfix value)))
               ((equal field 'rlimit)     (change-tactic.world world :rlimit (nfix value)))
               ((equal field 'rwn)        (change-tactic.world world :rwn (nfix value)))
               ((equal field 'urwn)       (change-tactic.world world :urwn (nfix value)))
               ((equal field 'depth)      (change-tactic.world world :depth (nfix value)))

               (t
                (ACL2::prog2$
                 (ACL2::cw "Warning: unknown field for tactic.simple-world-change-aux: ~x0.~%" field)
                 world)))))
    world))

(defthm tactic.worldp-of-tactic.simple-world-change-aux
  (implies (force (tactic.worldp world))
           (equal (tactic.worldp (tactic.simple-world-change-aux changes world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change-aux))))

(defthm tactic.world-atblp-of-tactic.simple-world-change-aux
  (implies (force (tactic.world-atblp world atbl))
           (equal (tactic.world-atblp (tactic.simple-world-change-aux changes world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change-aux))))

(defthm tactic.world-env-okp-of-tactic.simple-world-change-aux
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (tactic.world-env-okp (tactic.simple-world-change-aux changes world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change-aux))))

(defthm tactic.world->index-of-tactic.simple-world-change-aux
  (equal (tactic.world->index (tactic.simple-world-change-aux changes world))
         (tactic.world->index world))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change-aux))))



(defund tactic.simple-world-change (changes world)
  (declare (xargs :guard (tactic.worldp world)))
  (tactic.increment-world-index
   (tactic.simple-world-change-aux changes world)))

(defthm tactic.worldp-of-tactic.simple-world-change
  (implies (force (tactic.worldp world))
           (equal (tactic.worldp (tactic.simple-world-change changes world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change))))

(defthm tactic.world-atblp-of-tactic.simple-world-change
  (implies (force (tactic.world-atblp world atbl))
           (equal (tactic.world-atblp (tactic.simple-world-change changes world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change))))

(defthm tactic.world-env-okp-of-tactic.simple-world-change
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (tactic.world-env-okp (tactic.simple-world-change changes world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change))))

(defthm tactic.world->index-of-tactic.simple-world-change
  (equal (tactic.world->index (tactic.simple-world-change changes world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.simple-world-change))))



(defund tactic.simple-change-world-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        ;(extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'simple-change-world)
         (equal goals (tactic.skeleton->goals history))
         ;; Extras hold the changes.  But we don't need to know anything about
         ;; them.
         )))

(defthm booleanp-of-tactic.simple-change-world-okp
  (equal (booleanp (tactic.simple-change-world-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-okp))))

(defthm tactic.skeleton->goals-when-tactic.simple-change-world-okp
  (implies (tactic.simple-change-world-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-okp))))



(defund tactic.simple-change-world-tac (x changes)
  (declare (xargs :guard (tactic.skeletonp x)))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'simple-change-world
                          changes
                          x))

(defthm tactic.skeletonp-of-tactic.simple-change-world-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.simple-change-world-tac x changes))
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-tac))))

(defthm tactic.simple-change-world-okp-of-tactic.simple-change-world-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.simple-change-world-okp (tactic.simple-change-world-tac x changes))
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-tac
                                    tactic.simple-change-world-okp))))



(defund tactic.simple-change-world-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.simple-change-world-okp x)
                              (tactic.worldp world))))
  (tactic.simple-world-change (tactic.skeleton->extras x) world))


(defthm tactic.worldp-of-tactic.simple-change-world-compile-world
  (implies (force (tactic.worldp world))
           (equal (tactic.worldp (tactic.simple-change-world-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-compile-world))))

(defthm tactic.world-atblp-of-tactic.simple-change-world-compile-world
  (implies (force (tactic.world-atblp world atbl))
           (equal (tactic.world-atblp (tactic.simple-change-world-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-compile-world))))

(defthm tactic.world-env-okp-of-tactic.simple-change-world-compile-world
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (tactic.world-env-okp (tactic.simple-change-world-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.simple-change-world-compile-world))))

