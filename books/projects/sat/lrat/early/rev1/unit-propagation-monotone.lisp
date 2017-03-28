; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "lrat-checker")

(defthm member-equal-monotone
  (implies (and (subsetp-equal s1 s2)
                (member-equal a s1))
           (member-equal a s2)))

(defthm clause-or-assignment-p-forward
  (implies (and clause
                (clause-or-assignment-p clause))
           (literalp (car clause)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm contradiction-implies-conflicting-literalsp
  (implies (and (member-equal lit x)
                (member-equal (- lit) x)
		(literal-listp x))
           (conflicting-literalsp x))
	   :hints (("Goal" :in-theory (enable literalp) :do-not '(generalize))))

(defthm clause-or-assignment-p-is-not-contradictory
  (implies (and (member-equal lit x)
                (member-equal (- lit) x))
           (not (clause-or-assignment-p x)))
  :hints (("Goal"
           :in-theory (enable clause-or-assignment-p))))

(defthm is-unit-clause-t-monotone
  (implies (and (equal (is-unit-clause clause a1)
                       t)
                (clause-or-assignment-p a2)
                (not (equal (is-unit-clause clause a2)
                            t)))
           (not (subsetp-equal a1 a2))))

(defthm subsetp-transitive
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

(defthm not-member-is-unit-clause
  (implies (and (is-unit-clause clause assignment)
                (not (equal (is-unit-clause clause assignment)
                            t)))
           (not (member-equal (is-unit-clause clause assignment)
                              assignment))))

(defthm clause-or-assignment-p-cons-is-unit-clause
  (implies (and (clause-or-assignment-p a1)
                (clause-or-assignment-p clause)
                (is-unit-clause clause a1)
                (not (equal (is-unit-clause clause a1)
                            t)))
           (clause-or-assignment-p
            (cons (is-unit-clause clause a1)
                  a1)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm is-unit-clause-t-monotone-alt
  (implies (and (subsetp-equal a1 a2)
                (clause-or-assignment-p a2)
                (not (equal (is-unit-clause clause a2)
                            t)))
           (not (equal (is-unit-clause clause a1)
                       t))))

(defthm cons-preserves-subsetp
  (implies (subsetp x y)
           (subsetp x (cons a y))))

; !! Needed?
(defthm is-unit-clause-implies-not-member-car
  (implies (and (is-unit-clause clause a1)
                (clause-or-assignment-p a1))
           (not (member (car clause) a1)))
  :rule-classes :forward-chaining)

(defthm evaluate-clause-nil-implies-is-unit-clause-t
  (implies (null (evaluate-clause clause assignment))
           (equal (is-unit-clause clause assignment)
                  t)))

(defthm subsetp-preserves-evaluate-clause-nil
  (implies (and (clause-or-assignment-p a2)
                (null (evaluate-clause clause a1))
                (subsetp a1 a2))
           (equal (evaluate-clause clause a2)
                  nil)))

(defthm is-unit-clause-unchanged
  (implies (and (subsetp-equal a1 a2)
                (clause-or-assignment-p a2)
                (not (equal (is-unit-clause clause a2)
                            t))
                (is-unit-clause clause a1)
                (is-unit-clause clause a2))
           (equal (equal (is-unit-clause clause a1)
                         (is-unit-clause clause a2))
                  t)))

; After modifying unit-propagation so that in the error cases, we use
; unit-propagation-error instead of simply returning assignment, ACL2 failed to
; merge the induction schemes for (unit-propagation formula indices a1) and
; (unit-propagation formula indices a2).  So we need an induction hint.

(defun unit-propagation-2 (formula indices a1 a2)
  (cond
   ((endp indices) (list a1 a2))
   ((> (car indices) (formula-max formula))
    (unit-propagation-2 formula (cdr indices) a1 a2))
   (t (let* ((pair (hons-get (car indices) (formula-fal formula)))
             (clause (and pair
                          (not (deleted-clause-p (cdr pair)))
                          (cdr pair)))
             (unit-literal (and clause
                                (is-unit-clause clause a1))))
        (cond ((not unit-literal)
               (unit-propagation-2 formula (cdr indices) a1
                                   (let ((u2 (and clause
                                                  (is-unit-clause clause a2))))
                                     (if u2
                                         (cons u2 a2)
                                       a2))))
              ((eq unit-literal t) ; found contradiction
               t)
              (t (unit-propagation-2 formula
                                     (cdr indices)
                                     (add-to-set unit-literal
                                                 a1)
                                     (add-to-set unit-literal
                                                 a2))))))))

(defthm is-unit-clause-superset
  (implies (and (subsetp a1 a2)
                (syntaxp (term-order a1 a2))
                (clause-or-assignment-p a2)
                (is-unit-clause clause a1))
           (equal (is-unit-clause clause a2)
                  (cond ((member-equal (is-unit-clause clause a1) a2)
                         nil)
                        ((member-equal (negate (is-unit-clause clause a1))
                                       a2)
                         t)
                        (t (is-unit-clause clause a1))))))

(defthm clause-or-assignment-p-cons
  (implies (and (clause-or-assignment-p assignment)
                (literalp lit)
                (not (member lit assignment))
                (not (member (negate lit) assignment)))
           (clause-or-assignment-p (cons lit assignment)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm clause-or-assignment-p-has-literals
  (implies (and (clause-or-assignment-p clause)
                (not (literalp lit)))
           (not (member lit clause))))

(defthm unit-propagation-t-monotone
  (implies (and (equal (unit-propagation formula indices a1)
                       t)
                (clause-or-assignment-p a1)
                (clause-or-assignment-p a2)
                (subsetp-equal a1 a2)
                (formula-p formula))
           (equal (unit-propagation formula indices a2)
                  t))
  :hints (("Goal" :induct (unit-propagation-2 formula indices a1 a2))))

(defthm unit-propagation-monotonicity
  (implies (and (subsetp-equal a1 a2)
                (not (equal (unit-propagation formula indices a2)
                            t))
                (clause-or-assignment-p a1)
                (clause-or-assignment-p a2)
                (formula-p formula))
           (and (clause-or-assignment-p a1)
                (subsetp (unit-propagation formula indices a1)
                         (unit-propagation formula indices a2))))
  :hints (("Goal" :induct (unit-propagation-2 formula indices a1 a2))))
