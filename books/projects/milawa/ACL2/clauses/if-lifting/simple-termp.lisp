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
(include-book "../../logic/terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (clause.simple-termp x)
;;
;; A term is "simple" if it contains no if-expressions.  As a slight hack, we
;; consider degenerate terms to be simple, so this definition lines up
;; perfectly with clause.depth.

(defund clause.flag-simple-termp (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (and (equal flag 'list)
                                (logic.term-listp x)))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) t)
            ((logic.variablep x) t)
            ((logic.functionp x)
             (if (and (equal (logic.function-name x) 'if)
                      (equal (len (logic.function-args x)) 3))
                 nil
               (clause.flag-simple-termp 'list (logic.function-args x))))
            ((logic.lambdap x)
             (clause.flag-simple-termp 'list (logic.lambda-actuals x)))
         (t t))
    (if (consp x)
        (and (clause.flag-simple-termp 'term (car x))
             (clause.flag-simple-termp 'list (cdr x)))
      t)))

(definlined clause.simple-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (clause.flag-simple-termp 'term x))

(definlined clause.simple-term-listp (x)
  (declare (xargs :guard (logic.term-listp x)))
  (clause.flag-simple-termp 'list x))

(defthmd definition-of-clause.simple-termp
  (equal (clause.simple-termp x)
         (cond ((logic.constantp x) t)
               ((logic.variablep x) t)
               ((logic.functionp x)
                (if (and (equal (logic.function-name x) 'if)
                         (equal (len (logic.function-args x)) 3))
                    nil
                  (clause.simple-term-listp (logic.function-args x))))
               ((logic.lambdap x)
                (clause.simple-term-listp (logic.lambda-actuals x)))
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.simple-termp
                                    clause.simple-term-listp
                                    clause.flag-simple-termp))))

(defthmd definition-of-clause.simple-term-listp
  (equal (clause.simple-term-listp x)
         (if (consp x)
             (and (clause.simple-termp (car x))
                  (clause.simple-term-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.simple-termp
                                    clause.simple-term-listp
                                    clause.flag-simple-termp))))

(defthm clause.flag-simple-termp-of-term-removal
  (equal (clause.flag-simple-termp 'term x)
         (clause.simple-termp x))
  :hints(("Goal" :in-theory (enable clause.simple-termp))))

(defthm clause.flag-simple-termp-of-list-removal
  (equal (clause.flag-simple-termp 'list x)
         (clause.simple-term-listp x))
  :hints(("Goal" :in-theory (enable clause.simple-term-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-termp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-term-listp))))

(defthm clause.simple-termp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.simple-termp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.simple-termp x)
                  (clause.simple-term-listp (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))

(defthm clause.simple-termp-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.simple-termp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-termp))))




(defun clause.simple-term-induction (flag x)
  (declare (xargs :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) nil)
            ((logic.functionp x)
             (if (and (equal (logic.function-name x) 'if)
                      (equal (len (logic.function-args x)) 3))
                 (list (clause.simple-term-induction 'term (first (logic.function-args x)))
                       (clause.simple-term-induction 'term (second (logic.function-args x)))
                       (clause.simple-term-induction 'term (third (logic.function-args x))))
               (clause.simple-term-induction 'list (logic.function-args x))))
            ((logic.lambdap x)
             (clause.simple-term-induction 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (list (clause.simple-term-induction 'term (car x))
              (clause.simple-term-induction 'list (cdr x)))
      nil)))

(defthm clause.simple-term-listp-when-not-consp
  (implies (not (consp x))
           (equal (clause.simple-term-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-term-listp))))

(defthm clause.simple-term-listp-of-cons
  (equal (clause.simple-term-listp (cons a x))
         (and (clause.simple-termp a)
              (clause.simple-term-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-term-listp))))

(defthms-flag
  :thms ((term booleanp-of-clause.simple-termp
               (equal (booleanp (clause.simple-termp x))
                      t))
         (t booleanp-of-clause.simple-term-listp
            (equal (booleanp (clause.simple-term-listp x))
                   t)))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(deflist clause.simple-term-listp (x)
  (clause.simple-termp x)
  :elementp-of-nil t
  :already-definedp t)

(defthm clause.simple-term-listp-when-length-three
  (implies (equal (len x) 3)
           (equal (clause.simple-term-listp x)
                  (and (clause.simple-termp (first x))
                       (clause.simple-termp (second x))
                       (clause.simple-termp (third x))))))

(deflist clause.simple-term-list-listp (x)
  (clause.simple-term-listp x)
  :elementp-of-nil t
  :guard (logic.term-list-listp x))
