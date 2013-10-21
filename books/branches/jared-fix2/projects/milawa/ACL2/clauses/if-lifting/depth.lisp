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
(include-book "casesplit")
(include-book "term-paths")
(include-book "unlifted-subterms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.flag-depth (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) 0)
            ((logic.variablep x) 0)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3))
                   (+ 1 (max3 (clause.flag-depth 'term (first args))
                              (clause.flag-depth 'term (second args))
                              (clause.flag-depth 'term (third args))))
                 (clause.flag-depth 'list args))))
            ((logic.lambdap x)
             (clause.flag-depth 'list (logic.lambda-actuals x)))
            (t 0))
    (if (consp x)
        (max (clause.flag-depth 'term (car x))
             (clause.flag-depth 'list (cdr x)))
      0)))

(defund clause.depth (x)
  (declare (xargs :guard (logic.termp x)))
  (clause.flag-depth 'term x))

(defund clause.depth-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (clause.flag-depth 'list x))

(defthmd definition-of-clause.depth
  (equal (clause.depth x)
         (cond ((logic.constantp x) 0)
               ((logic.variablep x) 0)
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (if (and (equal name 'if)
                           (equal (len args) 3))
                      (+ 1 (max3 (clause.depth (first args))
                                 (clause.depth (second args))
                                 (clause.depth (third args))))
                    (clause.depth-list args))))
               ((logic.lambdap x)
                (clause.depth-list (logic.lambda-actuals x)))
               (t 0)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.flag-depth
                                    clause.depth
                                    clause.depth-list))))

(defthmd definition-of-clause.depth-list
  (equal (clause.depth-list x)
         (if (consp x)
             (max (clause.depth (car x))
                  (clause.depth-list (cdr x)))
           0))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.flag-depth
                                    clause.depth
                                    clause.depth-list))))

(defthm clause.flag-depth-of-term
  (equal (clause.flag-depth 'term x)
         (clause.depth x))
  :hints(("Goal" :in-theory (enable clause.depth))))

(defthm clause.flag-depth-of-list
  (equal (clause.flag-depth 'list x)
         (clause.depth-list x))
  :hints(("Goal" :in-theory (enable clause.depth-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.depth))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.flag-depth))))




;; (mutual-recursion
;;  (defund clause.depth (x)
;;    (declare (xargs :guard (logic.termp x)))
;;    (cond ((logic.constantp x) 0)
;;          ((logic.variablep x) 0)
;;          ((logic.functionp x)
;;           (let ((name (logic.function-name x))
;;                 (args (logic.function-args x)))
;;             (if (and (equal name 'if)
;;                      (equal (len args) 3))
;;                 (+ 1 (max3 (clause.depth (first args))
;;                            (clause.depth (second args))
;;                            (clause.depth (third args))))
;;               (clause.depth-list args))))
;;          ((logic.lambdap x)
;;           (clause.depth-list (logic.lambda-actuals x)))
;;          (t 0)))
;;  (defund clause.depth-list (x)
;;    (declare (xargs :guard (logic.term-listp x)))
;;    (if (consp x)
;;        (max (clause.depth (car x))
;;             (clause.depth-list (cdr x)))
;;      0)))

;; (defthm clause.depth-when-logic.constantp
;;   (implies (logic.constantp x)
;;            (equal (clause.depth x)
;;                   0))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-logic.variablep
;;   (implies (logic.variablep x)
;;            (equal (clause.depth x)
;;                   0))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-non-if-logic.functionp
;;   (implies (and (logic.functionp x)
;;                 ;; Was using case-split
;;                 (not (equal (logic.function-name x) 'if)))
;;            (equal (clause.depth x)
;;                   (clause.depth-list (logic.function-args x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-bad-args-logic.functionp
;;   (implies (and (logic.functionp x)
;;                 ;; Was using case-split
;;                 (not (equal (len (logic.function-args x)) 3)))
;;            (equal (clause.depth x)
;;                   (clause.depth-list (logic.function-args x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-if-logic.functionp
;;   (implies (and (logic.functionp x)
;;                 (equal (logic.function-name x) 'if)
;;                 (equal (len (logic.function-args x)) 3))
;;            (equal (clause.depth x)
;;                   (+ 1 (max3 (clause.depth (first (logic.function-args x)))
;;                              (clause.depth (second (logic.function-args x)))
;;                              (clause.depth (third (logic.function-args x)))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-logic.lambdap
;;   (implies (logic.lambdap x)
;;            (equal (clause.depth x)
;;                   (clause.depth-list (logic.lambda-actuals x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))

;; (defthm clause.depth-when-degenerate
;;   (implies (and (not (logic.constantp x))
;;                 (not (logic.variablep x))
;;                 (not (logic.functionp x))
;;                 (not (logic.lambdap x)))
;;            (equal (clause.depth x)
;;                   0))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.depth))))


(defthm forcing-clause.depth-of-logic.function
  (implies (force (logic.function-namep fn))
           (equal (clause.depth (logic.function fn args))
                  (if (and (equal fn 'if)
                           (equal (len args) 3))
                      (+ 1 (max3 (clause.depth (first args))
                                 (clause.depth (second args))
                                 (clause.depth (third args))))
                    (clause.depth-list args))))
  :hints(("Goal"
          :in-theory (disable (:executable-counterpart ACL2::force))
          :expand (clause.depth (logic.function fn args)))))

(defthm forcing-clause.depth-of-logic.lambda
  (equal (clause.depth (logic.lambda formals body actuals))
         (clause.depth-list actuals))
  :hints(("Goal"
          :in-theory (disable (:executable-counterpart ACL2::force))
          :expand (clause.depth (logic.lambda formals body actuals)))))


(defthm clause.depth-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.depth-list x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-clause.depth-list))))

(defthm clause.depth-list-of-cons
  (equal (clause.depth-list (cons a x))
         (max (clause.depth a)
              (clause.depth-list x)))
  :hints(("Goal" :in-theory (enable definition-of-clause.depth-list))))

(defthm clause.depth-list-when-length-three
  (implies (equal (len x) 3)
           (equal (clause.depth-list x)
                  (max3 (clause.depth (first x))
                        (clause.depth (second x))
                        (clause.depth (third x))))))

(defthms-flag
  :thms ((term natp-of-clause.depth
               (equal (natp (clause.depth x))
                      t))
         (t natp-of-clause.depth-list
            (equal (natp (clause.depth-list x))
                   t)))
  :hints (("Goal"
           :expand (clause.depth x)
           :induct (clause.simple-term-induction flag x))))

(defthm clause.depth-list-of-list-fix
  (equal (clause.depth-list (list-fix x))
         (clause.depth-list x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.depth-list-of-app
  (equal (clause.depth-list (app x y))
         (max (clause.depth-list x)
              (clause.depth-list y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.depth-list-of-rev
  (equal (clause.depth-list (rev x))
         (clause.depth-list x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :thms ((term clause.depth-zero
               (equal (equal 0 (clause.depth x))
                      (clause.simple-termp x)))
         (t clause.depth-list-zero
            (equal (equal 0 (clause.depth-list x))
                   (clause.simple-term-listp x))))
  :hints (("Goal"
           :expand (clause.depth x)
           :induct (clause.simple-term-induction flag x))))

(defthm clause.depth-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.depth x)
                  0)))

(defthm clause.depth-list-when-clause.simple-term-listp
  (implies (clause.simple-term-listp x)
           (equal (clause.depth-list x)
                  0)))

(defthm clause.depth-positive-when-non-clause.simple-termp
  (equal (< 0 (clause.depth x))
         (not (clause.simple-termp x))))

(defthm clause.depth-list-positive-when-non-clause.simple-term-listp
  (equal (< 0 (clause.depth-list x))
         (not (clause.simple-term-listp x))))



;; (clause.deepest x)
;;
;; X is a list of terms.  If x is empty, we return nil.  Otherwise, we return
;; the first member of x whose clause.depth is maximal for this list.

(defund clause.deepest (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (consp (cdr x))
          (let ((clause.deepest-in-cdr (clause.deepest (cdr x))))
            (if (< (clause.depth (car x))
                   (clause.depth clause.deepest-in-cdr))
                clause.deepest-in-cdr
              (car x)))
        (car x))
    nil))

(defthm clause.deepest-when-not-consp
  (implies (not (consp x))
           (equal (clause.deepest x)
                  nil))
  :hints(("Goal" :in-theory (enable clause.deepest))))

(defthm clause.deepest-of-cons
  (equal (clause.deepest (cons a x))
         (if (consp x)
             (if (< (clause.depth a)
                    (clause.depth (clause.deepest x)))
                 (clause.deepest x)
               a)
           a))
  :hints(("Goal" :in-theory (enable clause.deepest))))

(defthm clause.deepest-of-list-fix
  (equal (clause.deepest (list-fix x))
         (clause.deepest x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.deepest-of-app
  (equal (clause.deepest (app x y))
         (cond ((and (consp x) (consp y))
                (if (< (clause.depth (clause.deepest x))
                       (clause.depth (clause.deepest y)))
                    (clause.deepest y)
                  (clause.deepest x)))
               ((consp x)
                (clause.deepest x))
               ((consp y)
                (clause.deepest y))
               (t nil)))
  :hints(("Goal" :in-theory (enable clause.deepest))))

(defthm memberp-of-clause.deepest
  (equal (memberp (clause.deepest x) x)
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm positiveness-of-clause.depth-of-clause.deepest
  (equal (< 0 (clause.depth (clause.deepest x)))
         (and (consp x)
              (not (clause.simple-term-listp x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.deepest-weakly-deeper-than-any-member
  (implies (memberp a x)
           (equal (< (clause.depth (clause.deepest x))
                     (clause.depth a))
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))


;; clause.depth-list can be redefined in terms of clause.deepest, but we do not enable
;; this rule by default since it is so severe.

(defthmd clause.depth-list-redefinition
  (equal (clause.depth-list x)
         (if (consp x)
             (clause.depth (clause.deepest x))
           0))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.unlifted-subterms-weakly-decreases-clause.depth
  (equal (< (clause.depth x)
            (clause.depth-list (clause.unlifted-subterms x)))
         nil)
  :hints(("Goal"
          :expand (clause.depth x)
          :in-theory (enable clause.unlifted-subterms)
          :induct (clause.unlifted-subterms x))))

(defthm forcing-clause.simple-termp-of-clause.deepest
  (equal (clause.simple-termp (clause.deepest x))
         (clause.simple-term-listp x))
  :hints(("Goal"
          :induct (cdr-induction x))))

(defthms-flag
  :thms ((term clause.factor-when-irrelevant-tests
               (implies (and (disjointp (domain assignment) (clause.term-tests x))
                             (force (logic.termp x)))
                        (equal (clause.factor x assignment)
                               x)))
         (t clause.factor-list-when-irrelevant-tests
            (implies (and (disjointp (domain assignment) (clause.term-tests-list x))
                          (force (logic.term-listp x)))
                     (equal (clause.factor-list x assignment)
                            (list-fix x)))))
  :hints (("Goal"
           :induct (clause.simple-term-induction flag x))))

(defthms-flag
  :thms ((term clause.depth-of-clause.factor-weak
               (implies (force (logic.termp x))
                        (equal (< (clause.depth x)
                                  (clause.depth (clause.factor x assignment)))
                               nil)))
         (t clause.depth-of-clause.factor-list-weak
            (implies (force (logic.term-listp x))
                     (equal (< (clause.depth-list x)
                               (clause.depth-list (clause.factor-list x assignment)))
                            nil))))
  :hints (("Goal"
           :expand (clause.depth x)
           :induct (clause.simple-term-induction flag x))))



(defthmd lemma-2-for-clause.depth-of-clause.factor-strong
  (implies (and (< (clause.depth a) (clause.depth b))
                (force (logic.termp a)))
           (equal (< (clause.depth (clause.factor a assignment))
                     (+ 1 (clause.depth b)))
                  t))
  :hints(("Goal"
          :use ((:instance |a <= b, b <= c --> a < 1+c|
                           (a (clause.depth (clause.factor a assignment)))
                           (b (clause.depth a))
                           (c (clause.depth b)))))))

(defthms-flag
  :shared-hyp (clause.simple-term-listp (domain assignment))
  :thms ((term clause.depth-of-clause.factor-strong
               (implies (and (logic.termp x)
                             (not (clause.simple-termp x))
                             (disjoint-from-nonep (domain assignment) (clause.term-paths x)))
                        (equal (< (clause.depth (clause.factor x assignment))
                                  (clause.depth x))
                               t)))
         (t clause.depth-list-of-clause.factor-list-strong
            (implies (and (logic.term-listp x)
                          (not (clause.simple-term-listp x))
                          (disjoint-from-nonep (domain assignment) (clause.term-paths-list x)))
                     (equal (< (clause.depth-list (clause.factor-list x assignment))
                               (clause.depth-list x))
                            t))))
  :hints (("Goal"
           :expand (clause.depth x)
           :induct (clause.simple-term-induction flag x)
           :in-theory (enable lemma-2-for-clause.depth-of-clause.factor-strong))))

(defthm clause.depth-list-of-clause.unlifted-subterms-of-clause.casesplit
  (implies (and (logic.termp x)
                (logic.term-listp cases)
                (clause.simple-term-listp cases))
           (equal (clause.depth-list
                   (clause.unlifted-subterms
                    (clause.casesplit x cases assignment)))
                  (clause.depth-list
                   (clause.unlifted-subterms-list
                    (clause.multifactor x
                     (clause.cases cases assignment))))))
  :hints(("Goal"
          :in-theory (enable clause.casesplit)
          :induct (clause.casesplit x cases assignment))))


(encapsulate
 ()
 (defthmd lemma-for-clause.casesplit-strongly-reduces-clause.depth
   (implies (and (logic.termp x)
                 (not (clause.simple-termp x))
                 (clause.simple-term-listp (domain assignment))
                 (disjoint-from-nonep (domain assignment) (clause.term-paths x)))
            (equal (< (clause.depth-list (clause.unlifted-subterms (clause.factor x assignment)))
                      (clause.depth x))
                   t))
   :hints(("Goal"
           :in-theory (disable clause.unlifted-subterms-weakly-decreases-clause.depth)
           :use ((:instance clause.unlifted-subterms-weakly-decreases-clause.depth
                            (x (clause.factor x assignment)))))))

 (defthm clause.casesplit-strongly-reduces-clause.depth
   (implies (and (logic.termp x)
                 (not (clause.simple-termp x))
                 (logic.term-listp cases)
                 (clause.simple-term-listp cases)
                 (clause.simple-term-listp (domain assignment))
                 (disjoint-from-nonep (domain assignment) (clause.term-paths x)))
            (equal (< (clause.depth-list
                       (clause.unlifted-subterms
                        (clause.casesplit x cases assignment)))
                      (clause.depth x))
                   t))
   :hints(("Goal"
           :in-theory (enable clause.casesplit
                              lemma-for-clause.casesplit-strongly-reduces-clause.depth)
           :induct (clause.casesplit x cases assignment)))))




;; among a list of assignments, the special assignment is the one that will
;; have the clause.deepest unlifted subterm.

(defund clause.special-assignment (x assignments)
  (declare (xargs :guard (and (logic.termp x)
                              (map-listp assignments))))
  (if (consp assignments)
      (if (consp (cdr assignments))
          (let ((special-from-cdr (clause.special-assignment x (cdr assignments))))
            (if (< (clause.depth-list (clause.unlifted-subterms (clause.factor x (car assignments))))
                   (clause.depth-list (clause.unlifted-subterms (clause.factor x special-from-cdr))))
                special-from-cdr
              (car assignments)))
        (car assignments))
    nil))

(defthm clause.special-assignment-when-not-consp
  (implies (not (consp assignments))
           (equal (clause.special-assignment x assignments)
                  nil))
  :hints(("Goal" :in-theory (enable clause.special-assignment))))

(defthm clause.special-assignment-of-cons
  (equal (clause.special-assignment x (cons a assignments))
         (if (consp assignments)
             (if (< (clause.depth-list
                     (clause.unlifted-subterms
                      (clause.factor x a)))
                    (clause.depth-list
                     (clause.unlifted-subterms
                      (clause.factor x
                       (clause.special-assignment x assignments)))))
                 (clause.special-assignment x assignments)
               a)
           a))
  :hints(("Goal" :in-theory (enable clause.special-assignment))))

(defthm memberp-of-clause.special-assignment
  (equal (memberp (clause.special-assignment x assignments) assignments)
         (consp assignments))
  :hints(("Goal" :induct (cdr-induction assignments))))


(defthm forcing-logic.termp-of-clause.deepest
  (implies (force (logic.term-listp x))
           (equal (logic.termp (clause.deepest x))
                  (consp x)))
  :hints(("Goal" :in-theory (enable clause.deepest))))

(defthm clause.special-assignment-of-clause.multifactor
  (implies (and (consp assignments)
                (force (logic.termp x)))
           (equal (clause.deepest
                   (clause.unlifted-subterms-list
                    (clause.multifactor x assignments)))
                  (clause.deepest
                   (clause.unlifted-subterms
                    (clause.factor x (clause.special-assignment x assignments))))))
  :hints(("Goal"
          :in-theory (e/d (clause.depth-list-redefinition)
                          (positiveness-of-clause.depth-of-clause.deepest) ;; Yuck!
                          )
          :induct (cdr-induction assignments))))





;; among a list of terms to be factored with some assignment, the most deeply
;; factorable is the one which will be clause.deepest after factoring.

(defund clause.deepest-after-factoring (x assignment)
  (declare (xargs :guard (and (logic.term-listp x)
                              (mapp assignment))))
  (if (consp x)
      (if (consp (cdr x))
          (let ((clause.deepest-from-cdr (clause.deepest-after-factoring (cdr x) assignment)))
            (if (< (clause.depth (clause.factor (car x) assignment))
                   (clause.depth (clause.factor clause.deepest-from-cdr assignment)))
                clause.deepest-from-cdr
              (car x)))
        (car x))
    nil))

(defthm clause.deepest-after-factoring-when-not-consp
  (implies (not (consp x))
           (equal (clause.deepest-after-factoring x assignment)
                  nil))
  :hints(("Goal" :in-theory (enable clause.deepest-after-factoring))))

(defthm clause.deepest-after-factoring-of-cons
  (equal (clause.deepest-after-factoring (cons a x) assignment)
         (if (consp x)
             (let ((clause.deepest-from-cdr (clause.deepest-after-factoring x assignment)))
               (if (< (clause.depth (clause.factor a assignment))
                      (clause.depth (clause.factor clause.deepest-from-cdr assignment)))
                   clause.deepest-from-cdr
                 a))
           a))
  :hints(("Goal" :in-theory (enable clause.deepest-after-factoring))))

(defthm forcing-logic.termp-of-clause.deepest-after-factoring
  (implies (force (logic.term-listp x))
           (equal (logic.termp (clause.deepest-after-factoring x assignment))
                  (consp x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-clause.deepest-after-factoring
  (equal (memberp (clause.deepest-after-factoring x assignment) x)
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.deepest-of-clause.factor-list
  (implies (consp x)
           (equal (clause.deepest (clause.factor-list x assignment))
                  (clause.factor (clause.deepest-after-factoring x assignment)
                             assignment)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-clause.term-paths-of-clause.deepest-after-factoring
  (implies (disjoint-from-nonep domain (clause.term-paths-list x))
           (equal (disjoint-from-nonep domain (clause.term-paths (clause.deepest-after-factoring x assignment)))
                  t))
  :hints(("Goal"
          :in-theory (disable disjoint-from-nonep-of-clause.term-paths-when-memberp)
          :use ((:instance disjoint-from-nonep-of-clause.term-paths-when-memberp
                           (a (clause.deepest-after-factoring x assignment))
                           (x x))))))

