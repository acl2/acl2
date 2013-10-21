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

