; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "truth-monotone")
(include-book "unit-propagation-monotone")
(include-book "unit-propagation-implies-unsat")

(defthm not-conflicting-literalsp-implies-negate-is-not-member
  (implies (and (member lit a)
                (not (conflicting-literalsp a))
                (literal-listp a))
           (not (member (negate lit) a))))

(defthm not-conflicting-literalsp-implies-negate-is-not-member-subset
  (implies (and (subsetp a1 a2)
                (member lit a2)
                (not (conflicting-literalsp a2))
                (literal-listp a2))
           (not (member (negate lit) a1))))

(defthm subsetp-union-equal-2
  (implies (subsetp x z)
           (subsetp x (union$ y z))))

(defthm not-conflicting-literalsp-subsetp
  (implies (and (subsetp a1 a2)
                (literal-listp a2)
                (not (conflicting-literalsp a2)))
           (not (conflicting-literalsp a1))))

(defthm union-preserves-subsetp-2
  (implies (subsetp y z)
           (subsetp (union$ x y)
                    (union$ x z))))

(defthm conflicting-literalsp-preserved-by-union-equal-cons-2
  (implies (and (not (conflicting-literalsp (union$ a1 a2)))
                (literalp lit)
                (not (member (negate lit) a1))
                (not (member (negate lit) a2)))
           (not (conflicting-literalsp (union$ a1 (cons lit a2))))))

(defthm conflicting-literalsp-union-when-member
  (implies (and (literal-listp a1)
                (not (conflicting-literalsp a1))
                (literal-listp a2)
                (not (conflicting-literalsp a2))
                (member lit a1))
           (iff (conflicting-literalsp
                 (union-equal a1 (cons lit a2)))
                (conflicting-literalsp
                 (union-equal a1 a2))))
  :hints (("Goal"
           :induct (union-equal a1 a2)
           :restrict
           ((not-conflicting-literalsp-implies-negate-is-not-member-subset
             ((a2 (union-equal (cdr a1) (cons (car a1) a2)))))
            (not-conflicting-literalsp-subsetp
             ((a2 (union-equal (cdr a1) (cons (car a1) a2)))))))))

(defthm negate-negate
  (implies (literalp lit)
           (equal (negate (negate lit))
                  lit)))

(defthm not-conflicting-literalsp-union
  (implies (and (literal-listp clause)
                (not (conflicting-literalsp clause))
                (not (conflicting-literalsp assignment))
                (not (equal (evaluate-clause clause assignment)
                            t)))
           (not (conflicting-literalsp
                 (union-equal assignment
                              (negate-clause-or-assignment clause))))))

(defthm clause-or-assignment-p-union
  (implies (and (clause-or-assignment-p clause)
                (clause-or-assignment-p assignment)
                (not (equal (evaluate-clause clause assignment)
                            t)))
           (clause-or-assignment-p
            (union$ assignment
                    (negate-clause-or-assignment clause))))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm subsetp-union-1
  (subsetp x (union$ x y)))

(defthm unit-propagation-correct-1
  (implies (formula-truep formula assignment)
           (formula-truep
            formula
            (union$ assignment
                    (negate-clause-or-assignment clause))))
  :hints (("Goal" :restrict ((truth-monotone ((a1 assignment))))))
  :rule-classes nil)

(defthm unit-propagation-correct-2
  (implies (and (formula-p formula)
                (clause-or-assignment-p clause)
                (clause-or-assignment-p assignment)
                (equal (unit-propagation formula
                                         indices
                                         (negate-clause-or-assignment clause))
                       t)
                (not (equal (evaluate-clause clause assignment)
                            t)))
           (equal (unit-propagation formula
                                    indices
                                    (union$ assignment
                                            (negate-clause-or-assignment clause)))
                  t))
  :rule-classes nil)

(defthm unit-propagation-correct
  (implies (and (formula-p formula)
                (clause-or-assignment-p clause)
                (clause-or-assignment-p assignment)
                (formula-truep formula assignment)
                (equal (unit-propagation formula
                                         indices
                                         (negate-clause-or-assignment clause))
                       t))
           (equal (evaluate-clause clause assignment)
                  t))
  :hints (("Goal"
           :do-not-induct t
           :use (unit-propagation-correct-1 unit-propagation-correct-2)
           :in-theory (disable formula-p subsetp-union-equal-2))))
