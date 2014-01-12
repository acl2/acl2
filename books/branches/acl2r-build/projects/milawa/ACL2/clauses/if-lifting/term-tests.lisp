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



;; (clause.term-tests x)
;;
;; Construct the set of tests for x -- { a : (if a b c) is a subterm of x }

(defund clause.flag-term-tests (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (true-listp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) acc)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3))
                   (cons (first args)
                         (clause.flag-term-tests 'term (first args)
                          (clause.flag-term-tests 'term (second args)
                           (clause.flag-term-tests 'term (third args) acc))))
                 (clause.flag-term-tests 'list args acc))))
            ((logic.lambdap x)
             (clause.flag-term-tests 'list (logic.lambda-actuals x) acc))
            (t acc))
    (if (consp x)
        (clause.flag-term-tests 'term (car x)
         (clause.flag-term-tests 'list (cdr x) acc))
      acc)))

(definlined clause.term-tests (x)
  (declare (xargs :guard (logic.termp x)
                  :verify-guards nil))
  (clause.flag-term-tests 'term x nil))

(definlined clause.term-tests-list (x)
  (declare (xargs :guard (logic.term-listp x)
                  :verify-guards nil))
  (clause.flag-term-tests 'list x nil))

(defund clause.slow-term-tests (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (and (equal flag 'list)
                                (logic.term-listp x)))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) nil)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3))
                   (cons (first args)
                         (app (clause.slow-term-tests 'term (first args))
                              (app (clause.slow-term-tests 'term (second args))
                                   (clause.slow-term-tests 'term (third args)))))
                 (clause.slow-term-tests 'list args))))
            ((logic.lambdap x)
             (clause.slow-term-tests 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (app (clause.slow-term-tests 'term (car x))
             (clause.slow-term-tests 'list (cdr x)))
      nil)))

(encapsulate
 ()
 (defthmd lemma-1-for-definition-of-clause.term-tests
   (equal (true-listp (clause.slow-term-tests flag x))
          t)
   :hints(("Goal"
           :in-theory (enable clause.slow-term-tests)
           :induct (clause.slow-term-tests flag x))))

 (defthmd lemma-2-for-definition-of-clause.term-tests
   (equal (true-listp (clause.flag-term-tests flag x acc))
          (true-listp acc))
   :hints(("Goal"
           :in-theory (enable clause.flag-term-tests)
           :induct (clause.flag-term-tests flag x acc))))

 (local (in-theory (enable lemma-1-for-definition-of-clause.term-tests
                           lemma-2-for-definition-of-clause.term-tests)))

 (defthmd lemma-3-for-definition-of-clause.term-tests
   (implies (true-listp acc)
            (equal (clause.flag-term-tests flag x acc)
                   (app (clause.slow-term-tests flag x) acc)))
   :hints(("Goal"
           :in-theory (enable clause.flag-term-tests clause.slow-term-tests)
           :induct (clause.flag-term-tests flag x acc))))

 (local (in-theory (enable lemma-3-for-definition-of-clause.term-tests)))

 (verify-guards clause.flag-term-tests)
 (verify-guards clause.term-tests)
 (verify-guards clause.term-tests-list)

 (defthmd definition-of-clause.term-tests
   (equal (clause.term-tests x)
          (cond ((logic.constantp x) nil)
                ((logic.variablep x) nil)
                ((logic.functionp x)
                 (let ((name (logic.function-name x))
                       (args (logic.function-args x)))
                   (if (and (equal name 'if)
                            (equal (len args) 3))
                       (cons (first args)
                             (app (clause.term-tests (first args))
                                  (app (clause.term-tests (second args))
                                       (clause.term-tests (third args)))))
                     (clause.term-tests-list args))))
                ((logic.lambdap x)
                 (clause.term-tests-list (logic.lambda-actuals x)))
                (t nil)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable clause.term-tests
                                     clause.term-tests-list
                                     clause.slow-term-tests))))

 (defthmd definition-of-clause.term-tests-list
   (equal (clause.term-tests-list x)
          (if (consp x)
              (app (clause.term-tests (car x))
                   (clause.term-tests-list (cdr x)))
            nil))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable clause.term-tests
                                     clause.term-tests-list
                                     clause.slow-term-tests))))

 (defthm clause.flag-term-tests-removal
   (implies (force (true-listp acc))
            (equal (clause.flag-term-tests 'term x acc)
                   (app (clause.term-tests x) acc)))
   :hints(("Goal" :in-theory (enable clause.term-tests
                                     clause.slow-term-tests))))

 (defthm clause.flag-term-tests-list-removal
   (implies (force (true-listp acc))
            (equal (clause.flag-term-tests 'list x acc)
                   (app (clause.term-tests-list x) acc)))
   :hints(("Goal" :in-theory (enable clause.term-tests-list
                                     clause.slow-term-tests)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.term-tests))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.term-tests-list))))

(defthm clause.term-tests-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.term-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.term-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.term-tests x)
                  (clause.term-tests-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.term-tests x)
                  (clause.term-tests-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-if-logic.functionp
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.term-tests x)
                  (cons (first (logic.function-args x))
                        (app (clause.term-tests (first (logic.function-args x)))
                             (app (clause.term-tests (second (logic.function-args x)))
                                  (clause.term-tests (third (logic.function-args x))))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.term-tests x)
                  (clause.term-tests-list (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))

(defthm clause.term-tests-when-degenerate
  (implies (and (not (logic.variablep x))
                (not (logic.constantp x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.term-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests))))



(defthm clause.term-tests-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.term-tests-list x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests-list))))

(defthm clause.term-tests-list-of-cons
  (equal (clause.term-tests-list (cons a x))
         (app (clause.term-tests a)
              (clause.term-tests-list x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.term-tests-list))))

(defthm clause.term-tests-list-when-len-three
  (implies (equal (len x) 3)
           (equal (clause.term-tests-list x)
                  (app (clause.term-tests (first x))
                       (app (clause.term-tests (second x))
                            (clause.term-tests (third x)))))))



(defthms-flag
  :thms ((term clause.term-tests-when-clause.simple-termp
               (implies (clause.simple-termp x)
                        (equal (clause.term-tests x)
                               nil)))
         (t clause.term-tests-list-when-clause.simple-term-listp
            (implies (clause.simple-term-listp x)
                     (equal (clause.term-tests-list x)
                            nil))))
  :hints(("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-listp-of-clause.term-tests
               (implies (force (logic.termp x))
                        (equal (logic.term-listp (clause.term-tests x))
                               t)))
         (t forcing-logic.term-listp-of-clause.term-tests-list
            (implies (force (logic.term-listp x))
                     (equal (logic.term-listp (clause.term-tests-list x))
                            t))))
  :hints(("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-list-atblp-of-clause.term-tests
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)))
                        (equal (logic.term-list-atblp (clause.term-tests x) atbl)
                               t)))
         (t forcing-logic.term-list-atblp-of-clause.term-tests-list
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)))
                     (equal (logic.term-list-atblp (clause.term-tests-list x) atbl)
                            t))))
  :hints(("Goal" :induct (clause.simple-term-induction flag x))))




;; (clause.simple-tests x)
;;
;; Construct the set of simple tests for x:
;;
;;   { a : a is simple, (if a b c) is a subterm of x }

(defund clause.flag-simple-tests (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (true-listp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) acc)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3)
                        (clause.simple-termp (first args)))
                   (cons (first args)
                         (clause.flag-simple-tests 'term (second args)
                          (clause.flag-simple-tests 'term (third args) acc)))
                 (clause.flag-simple-tests 'list args acc))))
            ((logic.lambdap x)
             (clause.flag-simple-tests 'list (logic.lambda-actuals x) acc))
            (t acc))
    (if (consp x)
        (clause.flag-simple-tests 'term (car x)
         (clause.flag-simple-tests 'list (cdr x) acc))
      acc)))

(definlined clause.simple-tests (x)
  (declare (xargs :guard (logic.termp x)
                  :verify-guards nil))
  (clause.flag-simple-tests 'term x nil))

(definlined clause.simple-tests-list (x)
  (declare (xargs :guard (logic.term-listp x)
                  :verify-guards nil))
  (clause.flag-simple-tests 'list x nil))

(defun clause.slow-simple-tests (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (and (equal flag 'list)
                                (logic.term-listp x)))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) nil)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3)
                        (clause.simple-termp (first args)))
                   (cons (first args)
                         (app (clause.slow-simple-tests 'term (second args))
                              (clause.slow-simple-tests 'term (third args))))
                 (clause.slow-simple-tests 'list args))))
            ((logic.lambdap x)
             (clause.slow-simple-tests 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (app (clause.slow-simple-tests 'term (car x))
             (clause.slow-simple-tests 'list (cdr x)))
      nil)))

(encapsulate
 ()
 (defthmd lemma-1-for-definition-of-clause.simple-tests
   (equal (true-listp (clause.slow-simple-tests flag x))
          t)
   :hints(("Goal"
           :in-theory (enable clause.slow-simple-tests)
           :induct (clause.slow-simple-tests flag x))))

 (defthmd lemma-2-for-definition-of-clause.simple-tests
   (equal (true-listp (clause.flag-simple-tests flag x acc))
          (true-listp acc))
   :hints(("Goal"
           :in-theory (enable clause.flag-simple-tests)
           :induct (clause.flag-simple-tests flag x acc))))

 (local (in-theory (enable lemma-1-for-definition-of-clause.simple-tests
                           lemma-2-for-definition-of-clause.simple-tests)))

 (defthmd lemma-3-for-definition-of-clause.simple-tests
   (implies (true-listp acc)
            (equal (clause.flag-simple-tests flag x acc)
                   (app (clause.slow-simple-tests flag x) acc)))
   :hints(("Goal"
           :in-theory (enable clause.flag-simple-tests clause.slow-simple-tests)
           :induct (clause.flag-simple-tests flag x acc))))

 (local (in-theory (enable lemma-3-for-definition-of-clause.simple-tests)))

 (verify-guards clause.flag-simple-tests)
 (verify-guards clause.simple-tests)
 (verify-guards clause.simple-tests-list)

 (defthmd definition-of-clause.simple-tests
   (equal (clause.simple-tests x)
          (cond ((logic.constantp x) nil)
                ((logic.variablep x) nil)
                ((logic.functionp x)
                 (let ((name (logic.function-name x))
                       (args (logic.function-args x)))
                   (if (and (equal name 'if)
                            (equal (len args) 3)
                            (clause.simple-termp (first args)))
                       (cons (first args)
                             (app (clause.simple-tests (second args))
                                  (clause.simple-tests (third args))))
                     (clause.simple-tests-list args))))
                ((logic.lambdap x)
                 (clause.simple-tests-list (logic.lambda-actuals x)))
                (t nil)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable clause.simple-tests
                                     clause.simple-tests-list
                                     clause.slow-simple-tests))))

 (defthmd definition-of-clause.simple-tests-list
   (equal (clause.simple-tests-list x)
          (if (consp x)
              (app (clause.simple-tests (car x))
                   (clause.simple-tests-list (cdr x)))
            nil))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable clause.simple-tests
                                     clause.simple-tests-list
                                     clause.slow-simple-tests))))

 (defthm clause.flag-simple-tests-removal
   (implies (force (true-listp acc))
            (equal (clause.flag-simple-tests 'term x acc)
                   (app (clause.simple-tests x) acc)))
   :hints(("Goal" :in-theory (enable clause.simple-tests
                                     clause.slow-simple-tests))))

 (defthm clause.flag-simple-tests-list-removal
   (implies (force (true-listp acc))
            (equal (clause.flag-simple-tests 'list x acc)
                   (app (clause.simple-tests-list x) acc)))
   :hints(("Goal" :in-theory (enable clause.simple-tests-list
                                     clause.slow-simple-tests))))

 (local (in-theory (disable clause.flag-simple-tests-removal
                            clause.flag-simple-tests-list-removal)))

 (defthm clause.slow-simple-tests-removal
   (equal (clause.slow-simple-tests 'term x)
          (clause.simple-tests x))
   :hints(("Goal" :in-theory (enable clause.simple-tests))))

 (defthm clause.slow-simple-tests-removal
   (equal (clause.slow-simple-tests 'term x)
          (clause.simple-tests x))
   :hints(("Goal" :in-theory (enable clause.simple-tests-list)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-tests))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.simple-tests-list))))

(defthm clause.simple-tests-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.simple-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.simple-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-non-if-logic.functionp
  (implies (and (logic.functionp x)
                ;; Was using case-split
                (not (equal (logic.function-name x) 'if)))
           (equal (clause.simple-tests x)
                  (clause.simple-tests-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-bad-args-logic.functionp
  (implies (and (logic.functionp x)
                ;; Was using case-split
                (not (equal (len (logic.function-args x)) 3)))
           (equal (clause.simple-tests x)
                  (clause.simple-tests-list (logic.function-args x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))



;; (defthm clause.simple-tests-when-not-simple-first
;;   (implies (and (logic.functionp x)
;;                 ;; Was using case-split
;;                 (not (clause.simple-termp (first (logic.function-args x)))))
;;            (equal (clause.simple-tests x)
;;                   (clause.simple-tests-list (logic.function-args x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

;; (defthm clause.simple-tests-when-not-if-logic.functionp-of-simple
;;   (implies (and (logic.functionp x)
;;                 (equal (logic.function-name x) 'if)
;;                 (equal (len (logic.function-args x)) 3)
;;                 (clause.simple-termp (first (logic.function-args x))))
;;            (equal (clause.simple-tests x)
;;                   (cons (first (logic.function-args x))
;;                         (app (clause.simple-tests (second (logic.function-args x)))
;;                              (clause.simple-tests (third (logic.function-args x)))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-if
  (implies (and (logic.functionp x)
                (equal (logic.function-name x) 'if)
                (equal (len (logic.function-args x)) 3))
           (equal (clause.simple-tests x)
                  (if (clause.simple-termp (car (logic.function-args x)))
                      (cons (first (logic.function-args x))
                            (app (clause.simple-tests (second (logic.function-args x)))
                                 (clause.simple-tests (third (logic.function-args x)))))
                    (clause.simple-tests-list (logic.function-args x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.simple-tests x)
                  (clause.simple-tests-list (logic.lambda-actuals x))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.simple-tests x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests))))

(defthm clause.simple-tests-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.simple-tests-list x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests-list))))

(defthm clause.simple-tests-list-of-cons
  (equal (clause.simple-tests-list (cons a x))
         (app (clause.simple-tests a)
              (clause.simple-tests-list x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.simple-tests-list))))

(defthm clause.simple-tests-list-when-len-three
  (implies (equal (len x) 3)
           (equal (clause.simple-tests-list x)
                  (app (clause.simple-tests (first x))
                       (app (clause.simple-tests (second x))
                            (clause.simple-tests (third x)))))))

(defthm true-listp-of-clause.simple-tests-list
  (equal (true-listp (clause.simple-tests-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.simple-tests-list-of-list-fix
  (equal (clause.simple-tests-list (list-fix x))
         (clause.simple-tests-list x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.simple-tests-list-of-app
  (equal (clause.simple-tests-list (app x y))
         (app (clause.simple-tests-list x)
              (clause.simple-tests-list y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :thms ((term subsetp-of-clause.simple-tests-and-clause.term-tests
               (equal (subsetp (clause.simple-tests x) (clause.term-tests x))
                      t))
         (t subsetp-of-clause.simple-tests-list-and-clause.term-tests-list
            (equal (subsetp (clause.simple-tests-list x) (clause.term-tests-list x))
                   t)))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term clause.simple-term-listp-of-clause.simple-tests
               (equal (clause.simple-term-listp (clause.simple-tests x))
                      t))
         (t clause.simple-term-listp-of-clause.simple-tests-list
            (equal (clause.simple-term-listp (clause.simple-tests-list x))
                   t)))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term clause.simple-tests-when-clause.simple-termp
               (implies (clause.simple-termp x)
                        (equal (clause.simple-tests x)
                               nil)))
         (t clause.simple-tests-list-when-clause.simple-term-listp
            (implies (clause.simple-term-listp x)
                     (equal (clause.simple-tests-list x)
                            nil))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-listp-of-clause.simple-tests
               (implies (force (logic.termp x))
                        (equal (logic.term-listp (clause.simple-tests x))
                               t)))
         (t forcing-logic.term-listp-of-clause.simple-tests-list
            (implies (force (logic.term-listp x))
                     (equal (logic.term-listp (clause.simple-tests-list x))
                            t))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term forcing-logic.term-list-atblp-of-clause.simple-tests
               (implies (force (logic.term-atblp x atbl))
                        (equal (logic.term-list-atblp (clause.simple-tests x) atbl)
                               t)))
         (t forcing-logic.term-list-atblp-of-clause.simple-tests-list
            (implies (force (logic.term-list-atblp x atbl))
                     (equal (logic.term-list-atblp (clause.simple-tests-list x) atbl)
                            t))))
  :hints (("Goal"
           :induct (clause.simple-term-induction flag x)
           :in-theory (disable forcing-true-listp-of-logic.function-args))))

