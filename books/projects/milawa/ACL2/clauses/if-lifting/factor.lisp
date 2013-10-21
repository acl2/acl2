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


(defund clause.flag-factor (flag x assignment)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (mapp assignment))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond
       ((logic.constantp x) x)
       ((logic.variablep x) x)
       ((logic.functionp x)
        (let ((name (logic.function-name x))
              (args (logic.function-args x)))
          (if (and (equal name 'if)
                   (equal (len args) 3))
              (let* ((new-test (clause.flag-factor 'term (first args) assignment))
                     (new-test-binding (lookup new-test assignment)))
                (if new-test-binding
                    (if (cdr new-test-binding)
                        (clause.flag-factor 'term (second args) assignment)
                      (clause.flag-factor 'term (third args) assignment))
                  (let ((new-arg2 (clause.flag-factor 'term (second args) assignment))
                        (new-arg3 (clause.flag-factor 'term (third args) assignment)))
                    (logic.function 'if (list new-test new-arg2 new-arg3)))))
            (logic.function name (clause.flag-factor 'list args assignment)))))
       ((logic.lambdap x)
        (logic.lambda (logic.lambda-formals x)
                      (logic.lambda-body x)
                      (clause.flag-factor 'list (logic.lambda-actuals x) assignment)))
       (t x))
    (if (consp x)
        (cons (clause.flag-factor 'term (car x) assignment)
              (clause.flag-factor 'list (cdr x) assignment))
      nil)))

(definlined clause.factor (x assignment)
  (declare (xargs :guard (and (logic.termp x)
                              (mapp assignment))
                  :verify-guards nil))
  (clause.flag-factor 'term x assignment))

(definlined clause.factor-list (x assignment)
  (declare (xargs :guard (and (logic.term-listp x)
                              (mapp assignment))
                  :verify-guards nil))
  (clause.flag-factor 'list x assignment))

(defthmd definition-of-clause.factor
  (equal (clause.factor x assignment)
         (cond
          ((logic.constantp x) x)
          ((logic.variablep x) x)
          ((logic.functionp x)
           (let ((name (logic.function-name x))
                 (args (logic.function-args x)))
             (if (and (equal name 'if)
                      (equal (len args) 3))
                 (let* ((new-test (clause.factor (first args) assignment))
                        (new-test-binding (lookup new-test assignment)))
                   (if new-test-binding
                       (if (cdr new-test-binding)
                           (clause.factor (second args) assignment)
                         (clause.factor (third args) assignment))
                     (let ((new-arg2 (clause.factor (second args) assignment))
                           (new-arg3 (clause.factor (third args) assignment)))
                       (logic.function 'if (list new-test new-arg2 new-arg3)))))
               (logic.function name (clause.factor-list args assignment)))))
          ((logic.lambdap x)
           (logic.lambda (logic.lambda-formals x)
                         (logic.lambda-body x)
                         (clause.factor-list (logic.lambda-actuals x) assignment)))
          (t x)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.factor
                                    clause.factor-list
                                    clause.flag-factor))))

(defthmd definition-of-clause.factor-list
  (equal (clause.factor-list x assignment)
         (if (consp x)
             (cons (clause.factor (car x) assignment)
                   (clause.factor-list (cdr x) assignment))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.factor
                                    clause.factor-list
                                    clause.flag-factor))))

(defthm clause.flag-factor-of-term-removal
  (equal (clause.flag-factor 'term x assignment)
         (clause.factor x assignment))
  :hints(("Goal" :in-theory (enable clause.factor))))

(defthm clause.flag-factor-of-list-removal
  (equal (clause.flag-factor 'list x assignment)
         (clause.factor-list x assignment))
  :hints(("Goal" :in-theory (enable clause.factor-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.factor))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.factor-list))))



(defthm clause.factor-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.factor-list x assignment)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-list))))

(defthm clause.factor-list-of-cons
  (equal (clause.factor-list (cons a x) assignment)
         (cons (clause.factor a assignment)
               (clause.factor-list x assignment)))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-list))))

(defprojection :list (clause.factor-list x assignment)
               :element (clause.factor x assignment)
               :guard (and (logic.term-listp x)
                           (mapp assignment))
               :verify-guards nil
               :already-definedp t)

(defthm clause.factor-list-when-len-three
  (implies (equal (len x) 3)
           (equal (clause.factor-list x assignment)
                  (list (clause.factor (first x) assignment)
                        (clause.factor (second x) assignment)
                        (clause.factor (third x) assignment)))))



;; Usually I don't really care for these kinds of opening rules.  But here they
;; seem to do a good job.  For example, they prevent the large case splits that
;; would be caused by just enabling factor when we get into situations like
;; proving the factor builder, and allow us to prove the theorem more quickly.

(defthm clause.factor-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.factor x assignment)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.factor x assignment)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-non-if-logic.functionp
  (implies (and (not (equal 'if (logic.function-name x)))
                (logic.functionp x))
           (equal (clause.factor x assignment)
                  (logic.function (logic.function-name x)
                         (clause.factor-list (logic.function-args x) assignment))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-bad-args-logic.functionp
  (implies (and (not (equal 3 (len (logic.function-args x))))
                (logic.functionp x))
           (equal (clause.factor x assignment)
                  (logic.function (logic.function-name x)
                         (clause.factor-list (logic.function-args x) assignment))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

;; (defthm clause.factor-when-test-not-bound
;;   (implies (and (logic.functionp x)
;;                 (not (lookup (clause.factor (first (logic.function-args x)) assignment) assignment)))
;;            (equal (clause.factor x assignment)
;;                   (logic.function (logic.function-name x)
;;                                   (clause.factor-list (logic.function-args x) assignment))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal"
;;           :in-theory (enable definition-of-clause.factor)
;;           :expand (clause.factor x assignment))))

;; (defthm clause.factor-when-if-logic.functionp
;;   (implies (and (logic.functionp x)
;;                 (equal (logic.function-name x) 'if)
;;                 (equal (len (logic.function-args x)) 3)
;;                 (lookup (clause.factor (first (logic.function-args x)) assignment) assignment))
;;            (equal (clause.factor x assignment)
;;                   (if (cdr (lookup (clause.factor (first (logic.function-args x)) assignment) assignment))
;;                       (clause.factor (second (logic.function-args x)) assignment)
;;                     (clause.factor (third (logic.function-args x)) assignment))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-if-expression
  (implies (and (equal 'if (logic.function-name x))
                (equal 3 (len (logic.function-args x)))
                (logic.functionp x))
           (equal (clause.factor x assignment)
                  (if (lookup (clause.factor (first (logic.function-args x)) assignment) assignment)
                      (if (cdr (lookup (clause.factor (first (logic.function-args x)) assignment) assignment))
                          (clause.factor (second (logic.function-args x)) assignment)
                        (clause.factor (third (logic.function-args x)) assignment))
                    (logic.function (logic.function-name x)
                                    (clause.factor-list (logic.function-args x) assignment)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.factor x assignment)
                  (logic.lambda (logic.lambda-formals x)
                                (logic.lambda-body x)
                                (clause.factor-list (logic.lambda-actuals x) assignment))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))

(defthm clause.factor-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.factor x assignment)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor))))



(defthms-flag
  :thms ((term forcing-logic.termp-of-clause.factor
               (implies (force (logic.termp x))
                        (equal (logic.termp (clause.factor x assignment))
                               t)))
         (t forcing-logic.term-listp-of-clause.factor-list
            (implies (force (logic.term-listp x))
                     (equal (logic.term-listp (clause.factor-list x assignment))
                            t))))
  :hints(("Goal" :induct (clause.simple-term-induction flag x))))

(verify-guards clause.flag-factor)
(verify-guards clause.factor)
(verify-guards clause.factor-list)

(defthms-flag
  :thms ((term forcing-logic.term-atblp-of-clause.factor
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)))
                        (equal (logic.term-atblp (clause.factor x assignment) atbl)
                               t)))
         (t forcing-logic.term-list-atblp-of-clause.factor-list
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)))
                     (equal (logic.term-list-atblp (clause.factor-list x assignment) atbl)
                            t))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :shared-hyp (not (consp assignment))
  :thms ((term clause.factor-when-not-consp-of-assignment
               (implies (force (logic.termp x))
                        (equal (clause.factor x assignment)
                               x)))
         (t clause.factor-list-when-not-consp-of-assignment
            (implies (force (logic.term-listp x))
                     (equal (clause.factor-list x assignment)
                            (list-fix x)))))
  :hints (("Goal" :induct (clause.simple-term-induction flag x))))

(defprojection :list (clause.multifactor term x)
               :element (clause.factor term x)
               :guard (and (logic.termp term)
                           (map-listp x)))

(defthm forcing-logic.term-listp-of-clause.multifactor
  (implies (force (logic.termp x))
           (equal (logic.term-listp (clause.multifactor x assignments))
                  t))
  :hints(("Goal" :induct (cdr-induction assignments))))

