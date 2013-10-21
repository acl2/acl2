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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO Dammit I hate this stupid file.  I wish it would die.


;; We interpret F ^ G as an abbreviation for ~(~F v ~G).  We write the function
;; logic.and-structurep to recognize formulas of this form.

(defund logic.and-structurep (x)
  ;; BOZO this should be guarded with formulap instead of checking it
  (declare (xargs :guard t))
  (and (logic.formulap x)
       (equal (logic.fmtype x) 'pnot*)
       (let ((or-not-f-not-g (logic.~arg x)))
         (and (equal (logic.fmtype or-not-f-not-g) 'por*)
              (let ((not-f (logic.vlhs or-not-f-not-g))
                    (not-g (logic.vrhs or-not-f-not-g)))
                (and (equal (logic.fmtype not-f) 'pnot*)
                     (equal (logic.fmtype not-g) 'pnot*)))))))

(defthm booleanp-of-logic.and-structurep
  (equal (booleanp (logic.and-structurep x))
         t)
  :hints(("Goal" :in-theory (enable logic.and-structurep))))

(defund logic.andlhs (x)
  (declare (xargs :guard (logic.and-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.and-structurep)))))
  (logic.~arg          ;; F
   (logic.vlhs         ;; ~F
    (logic.~arg        ;; ~F v ~G
     x))))       ;; ~(~F v ~G)

(defund logic.andrhs (x)
  (declare (xargs :guard (logic.and-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.and-structurep)))))
  (logic.~arg          ;; G
   (logic.vrhs         ;; ~G
    (logic.~arg        ;; ~F v ~G
     x))))       ;; ~(~F v ~G)

(defund logic.pand (x y)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formulap y))))
  (logic.pnot (logic.por (logic.pnot x)
                         (logic.pnot y))))

(in-theory (disable (:executable-counterpart logic.pand)))

(defthm logic.pand-under-iff
  (iff (logic.pand x y)
       t)
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.and-structurep-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.and-structurep (logic.pand x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.pand logic.and-structurep))))

(defthm forcing-logic.formulap-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.formulap (logic.pand x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.formula-atblp-of-logic.pand
  (implies (and (force (logic.formula-atblp x atbl))
                (force (logic.formula-atblp y atbl)))
           (equal (logic.formula-atblp (logic.pand x y) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.formulap-of-logic.andlhs
  (implies (force (logic.and-structurep x))
           (equal (logic.formulap (logic.andlhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.and-structurep))))

(defthm forcing-logic.formulap-of-logic.andrhs
  (implies (force (logic.and-structurep x))
           (equal (logic.formulap (logic.andrhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.and-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.andlhs
  (implies (and (force (logic.and-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.andlhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.and-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.andrhs
  (implies (and (force (logic.and-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.andrhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.and-structurep))))

(defthm forcing-logic.andlhs-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.andlhs (logic.pand x y))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.pand))))

(defthm forcing-logic.andrhs-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.andrhs (logic.pand x y))
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.pand))))


