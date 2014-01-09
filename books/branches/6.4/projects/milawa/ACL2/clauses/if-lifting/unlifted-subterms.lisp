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
(include-book "lifted-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund clause.unlifted-subterms (x)
  (declare (xargs :guard (logic.termp x)))
  (cond ((logic.constantp x) nil)
        ((logic.variablep x) nil)
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (if (and (equal name 'if)
                    (equal (len args) 3))
               (app (clause.unlifted-subterms (first args))
                    (app (clause.unlifted-subterms (second args))
                         (clause.unlifted-subterms (third args))))
             (if (clause.simple-term-listp args)
                 nil
               (list x)))))
        ((logic.lambdap x)
         (if (clause.simple-term-listp (logic.lambda-actuals x))
             nil
           (list x)))
        (t nil)))

(defthm consp-of-clause.unlifted-subterms
  (equal (consp (clause.unlifted-subterms x))
         (if (clause.unlifted-subterms x)
             t
           nil))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.unlifted-subterms x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.unlifted-subterms x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.unlifted-subterms x)
                  (if (clause.simple-termp x)
                      nil
                    (list x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.unlifted-subterms x)
                  (if (clause.simple-termp x)
                      nil
                    (list x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.unlifted-subterms x)
                  (app (clause.unlifted-subterms (first (logic.function-args x)))
                       (app (clause.unlifted-subterms (second (logic.function-args x)))
                            (clause.unlifted-subterms (third (logic.function-args x)))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.unlifted-subterms x)
                  (if (clause.simple-termp x)
                      nil
                    (list x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.unlifted-subterms x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm true-listp-of-clause.unlifted-subterms
  (equal (true-listp (clause.unlifted-subterms x))
         t)
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm forcing-logic.term-listp-of-clause.unlifted-subterms
  (implies (force (logic.termp x))
           (logic.term-listp (clause.unlifted-subterms x)))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.unlifted-subterms x)
                  nil))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.simple-termp-when-memberp-of-clause.unlifted-subterms
  (implies (memberp a (clause.unlifted-subterms x))
           (equal (clause.simple-termp a)
                  nil))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))

(defthm clause.unlifted-subterms-under-iff
  (iff (clause.unlifted-subterms x)
       (not (clause.lifted-termp x)))
  :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthm clause.simple-term-listp-of-clause.unlifted-subterms
  (equal (clause.simple-term-listp (clause.unlifted-subterms x))
         (clause.lifted-termp x))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms))))





(defund clause.unlifted-subterms-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (app (clause.unlifted-subterms (car x))
           (clause.unlifted-subterms-list (cdr x)))
    nil))

(defthm clause.unlifted-subterms-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.unlifted-subterms-list x)
                  nil))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms-list))))

(defthm clause.unlifted-subterms-list-of-cons
  (equal (clause.unlifted-subterms-list (cons a x))
         (app (clause.unlifted-subterms a)
              (clause.unlifted-subterms-list x)))
  :hints(("Goal" :in-theory (enable clause.unlifted-subterms-list))))

(defthm true-listp-of-clause.unlifted-subterms-list
  (equal (true-listp (clause.unlifted-subterms-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-clause.unlifted-subterms-list
  (equal (consp (clause.unlifted-subterms-list x))
         (not (clause.lifted-term-listp x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-listp-of-clause.unlifted-subterms-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (clause.unlifted-subterms-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.unlifted-subterms-list-of-list-fix
  (equal (clause.unlifted-subterms-list (list-fix x))
         (clause.unlifted-subterms-list x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.unlifted-subterms-list-of-app
  (equal (clause.unlifted-subterms-list (app x y))
         (app (clause.unlifted-subterms-list x)
              (clause.unlifted-subterms-list y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.simple-termp-when-memberp-of-clause.unlifted-subterms-list
  (implies (memberp a (clause.unlifted-subterms-list x))
           (equal (clause.simple-termp a)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.unlifted-subterms-list-under-iff
  (iff (clause.unlifted-subterms-list x)
       (not (clause.lifted-term-listp x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.simple-term-listp-of-clause.unlifted-subterms-list
  (equal (clause.simple-term-listp (clause.unlifted-subterms-list x))
         (clause.lifted-term-listp x))
  :hints(("Goal" :induct (cdr-induction x))))
