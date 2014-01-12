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
(include-book "basic")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund build.skip (a)
  (declare (xargs :guard (logic.formulap a)))
  (logic.appeal 'skip a nil nil))

(encapsulate
 ()
 (local (in-theory (enable build.skip)))

 (defthm build.skip-under-iff
   (iff (build.skip a)
        t))

 (defthm logic.method-of-build.skip
   (equal (logic.method (build.skip a))
          'skip))

 (defthm logic.conclusion-of-build.skip
   (equal (logic.conclusion (build.skip a))
          a))

 (defthm logic.subproofs-of-build.skip
   (equal (logic.subproofs (build.skip a))
          nil))

 (defthm logic.extras-of-build.skip
   (equal (logic.extras (build.skip a))
          nil))

 (defthm forcing-logic.appealp-of-build.skip
   (implies (force (logic.formulap a))
            (equal (logic.appealp (build.skip a))
                   t)))

 (defthm forcing-logic.proofp-of-build.skip
   (implies (force (logic.formula-atblp a atbl))
            (equal (logic.proofp (build.skip a) skips thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.skip-okp)))))


(defprojection :list (build.skip-list x)
               :element (build.skip x)
               :guard (logic.formula-listp x))

(defthm forcing-logic.appeal-listp-of-build.skip-list
  (implies (force (logic.formula-listp x))
           (equal (logic.appeal-listp (build.skip-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-conclusions-of-build.skip-list
  (implies (force (logic.formula-listp x))
           (equal (logic.strip-conclusions (build.skip-list x))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.proof-listp-of-build.skip-list
  (implies (force (logic.formula-list-atblp x atbl))
           (equal (logic.proof-listp (build.skip-list x) axioms thms atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
