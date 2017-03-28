; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

; Start proof of sat-drat-claim-1.

(defun non-subsetp-witness (x y)
  (cond ((endp x) 1) ; irrelevant, but return a literal
        ((member-equal (car x) y)
         (non-subsetp-witness (cdr x) y))
        (t (car x))))

(defthm literalp-non-subsetp-witness
  (implies (force (clause-or-assignment-p x))
           (literalp (non-subsetp-witness x y)))
  :rule-classes :type-prescription)

(defthmd non-subsetp-witness-property
  (equal (subsetp x y)
         (not (let ((wit (non-subsetp-witness x y)))
                (and (member wit x)
                     (not (member wit y)))))))

(defthm member-negate-clause-or-assignment
  (implies (clause-or-assignment-p clause)
           (iff (member lit (negate-clause-or-assignment clause))
                (member (negate lit) clause))))

(defthm evaluate-clause-when-member
  (implies (and (clause-or-assignment-p clause)
                (member lit assignment)
                (member lit clause))
           (equal (evaluate-clause clause assignment)
                  t)))

; The following book includes the lemma formula-truep-cons, which is useful for
; formula-truep-add-proof-clause.
(local (include-book "satisfiable-add-proof-clause-rup"))

(defthm formula-truep-add-proof-clause
  (implies (and (clause-or-assignment-p clause)
                (member lit assignment)
                (member lit clause)
                (formula-truep formula assignment))
           (formula-truep (add-proof-clause index clause formula)
                          assignment)))

; Keep the following in-theory event non-local, since we are including this
; book at the top level of satisfiable-add-proof-clause-drat.lisp.
(in-theory (disable add-proof-clause))

(defthm clause-or-assignment-p-cons-better
  (implies (and (clause-or-assignment-p assignment)
                (force (literalp lit))
                (not (member lit assignment)))
           (equal (clause-or-assignment-p (cons lit assignment))
                  (not (member (negate lit) assignment))))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm sat-drat-claim-1
  (implies (and (not (satisfiable (add-proof-clause index clause formula)))
                (solution-p assignment formula)
                (clause-or-assignment-p clause))
           (subsetp (negate-clause-or-assignment clause)
                    assignment))
  :hints (("Goal"
           :in-theory (e/d (non-subsetp-witness-property) (satisfiable-suff))
           :use ((:instance satisfiable-suff
                            (formula (add-proof-clause index clause formula))
                            (assignment (add-to-set
                                         (negate
                                          (non-subsetp-witness
                                           (negate-clause-or-assignment
                                            clause)
                                           assignment))
                                         assignment))))
           :restrict ((formula-truep-add-proof-clause
                       ((lit (- (non-subsetp-witness
                                 (negate-clause-or-assignment clause)
                                 assignment))))))
           :do-not-induct t)))
