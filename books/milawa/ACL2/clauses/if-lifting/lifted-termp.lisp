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
(include-book "simple-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (clause.lifted-termp x)
;;
;; We say x is a "lifted" term if it has no subterms of the form (f ... (if
;; ...)  ...) unless f is if.  We call such subterms the "unlifted" parts of a
;; term.

(defund clause.lifted-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (cond ((logic.constantp x) t)
        ((logic.variablep x) t)
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (if (and (equal name 'if)
                    (equal (len args) 3))
               (and (clause.lifted-termp (first args))
                    (clause.lifted-termp (second args))
                    (clause.lifted-termp (third args)))
             (clause.simple-term-listp (logic.function-args x)))))
        ((logic.lambdap x)
         (clause.simple-term-listp (logic.lambda-actuals x)))
        (t t)))

(defthm clause.lifted-termp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-not-if
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (and (clause.lifted-termp (first (logic.function-args x)))
                       (clause.lifted-termp (second (logic.function-args x)))
                       (clause.lifted-termp (third (logic.function-args x))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-if-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.lifted-termp x)
                  (clause.simple-term-listp (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.lifted-termp-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.lifted-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))


(defun clause.lifted-termp-induction (x)
  (declare (xargs :verify-guards nil))
  (cond ((logic.constantp x) nil)
        ((logic.variablep x) nil)
        ((and (logic.functionp x)
              (equal (logic.function-name x) 'if)
              (equal (len (logic.function-args x)) 3))
         (list (clause.lifted-termp-induction (first (logic.function-args x)))
               (clause.lifted-termp-induction (second (logic.function-args x)))
               (clause.lifted-termp-induction (third (logic.function-args x)))))
        ((logic.functionp x)
         nil)
        ((logic.lambdap x)
         nil)
        (t nil)))

(defthm clause.lifted-termp-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.lifted-termp x)
                  t))
  :hints(("Goal" :induct (clause.lifted-termp-induction x))))

(defthm booleanp-of-clause.lifted-termp
  (equal (booleanp (clause.lifted-termp x))
         t)
  :hints(("Goal" :induct (clause.lifted-termp-induction x))))

(deflist clause.lifted-term-listp (x)
  (clause.lifted-termp x)
  :elementp-of-nil t
  :guard (logic.term-listp x))
