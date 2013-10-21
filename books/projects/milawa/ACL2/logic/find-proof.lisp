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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO implement a deffinder sort of macro?

(defund logic.find-proof (a x)
  ;; We return the first proof in x which concludes a, or nil if no such proof
  ;; is present.
  (declare (xargs :guard (and (logic.formulap a)
                              (logic.appeal-listp x))))
  (if (consp x)
      (if (equal (logic.conclusion (car x)) a)
          (car x)
        (logic.find-proof a (cdr x)))
    nil))


(defthm logic.find-proof-when-not-consp
  (implies (not (consp x))
           (equal (logic.find-proof a x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.find-proof))))

(defthm logic.find-proof-of-cons
  (equal (logic.find-proof a (cons b x))
         (if (equal (logic.conclusion b) a)
             b
           (logic.find-proof a x)))
  :hints(("Goal" :in-theory (enable logic.find-proof))))

(defthm logic.find-proof-of-list-fix
  (equal (logic.find-proof a (list-fix x))
         (logic.find-proof a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.find-proof-of-app
  (implies (and (force (logic.appeal-listp x))
                (force (logic.appeal-listp y)))
           (equal (logic.find-proof a (app x y))
                  (or (logic.find-proof a x)
                      (logic.find-proof a y))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm conclusion-of-logic.find-proof
  (implies (logic.find-proof a x)
           (equal (logic.conclusion (logic.find-proof a x))
                  a))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.find-proof-under-iff-when-memberp-of-logic.strip-conclusions
  (implies (and (memberp a (logic.strip-conclusions x))
                (force (logic.appeal-listp x)))
           (iff (logic.find-proof a x)
                t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-memberp-of-logic.strip-conclusions-when-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.appeal-listp x)))
           (equal (memberp a (logic.strip-conclusions x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.appealp-of-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.appeal-listp x)))
           (equal (logic.appealp (logic.find-proof a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.proofp-of-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.proof-listp x axioms thms atbl)))
           (logic.proofp (logic.find-proof a x) axioms thms atbl))
  :hints(("Goal" :induct (cdr-induction x))))



(defprojection :list (logic.find-proofs x proofs)
               :element (logic.find-proof x proofs)
               :guard (and (logic.formula-listp x)
                           (logic.appeal-listp proofs)))

