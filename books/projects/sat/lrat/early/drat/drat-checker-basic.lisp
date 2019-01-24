; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This work is based on Nathan Wetzler's RAT checker work in ACL2 community
; books directory books/projects/sat/proof-checker-itp13/.  Here we accommodate
; a more recent input proof format to speed up unit propagation and add
; deletion (to obtain a DRAT checker).

; See ../../README.

(in-package "PROOF-CHECKER-ITP13")

(include-book "supplemental/ternary" :dir :itp13)
(include-book "supplemental/literal" :dir :itp13)
(include-book "supplemental/sets" :dir :itp13)
(include-book "supplemental/assignment" :dir :itp13)
(include-book "supplemental/clause" :dir :itp13)
(include-book "supplemental/evaluator" :dir :itp13)
(include-book "supplemental/unit-propagation" :dir :itp13)
(include-book "std/util/bstar" :dir :system)



;; ========================== CLAUSE-LISTP and D-CLAUSE-LISTP ===========================

(defun d-clause-listp (d-clause-list) ; primitive

; A d-clause-list is a list of pairs (boolean . clause), where the boolean is
; intended to indicate whether the clause is to be added (boolean = nil) or to
; be deleted (boolean = t).

  (declare (xargs :guard t))
  (if (atom d-clause-list)
      (null d-clause-list)
    (and (consp (car d-clause-list))
         (booleanp (caar d-clause-list))
         (clausep (cdar d-clause-list))
         (d-clause-listp (cdr d-clause-list)))))


;; ========================== NEGATE-CLAUSE ==========================
;; ======================== NEGATE-ASSIGNMENT ========================

(defun negate-clause (clause) ; primitive
  (declare (xargs :guard (clausep clause)))
  (if (atom clause)
      nil
    (cons (negate (car clause))
          (negate-clause (cdr clause)))))

(defun negate-assignment (assignment)
  (declare (xargs :guard (assignmentp assignment)))
  (if (atom assignment)
      nil
    (cons (negate (car assignment))
          (negate-assignment (cdr assignment)))))

(defthm negate-clause-negate-assignment
  (implies (literal-listp x)
           (equal (negate-clause (negate-assignment x))
                  x)))

(defthm negate-assignment-negate-clause
  (implies (literal-listp x)
           (equal (negate-assignment (negate-clause x))
                  x)))

(defthm member-negate-negate-clause
  (implies (and (literalp e)
                (literal-listp x))
           (iff (member e (negate-clause x))
                (member (negate e) x))))

(defthm member-negate-negate-assignment
  (implies (and (literalp e)
                (literal-listp x))
           (iff (member e (negate-assignment x))
                (member (negate e) x))))

(defthm assignmentp-negate-clause
  (implies (clausep clause)
           (assignmentp (negate-clause clause))))

(defthm assignmentp-negate-assignment
  (implies (assignmentp clause)
           (clausep (negate-assignment clause)))
  :hints (("Goal" :in-theory (enable assignmentp))))


;; ============================ NUM-UNDEF ============================

(defun num-undef (formula assignment)
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))))
  (if (atom formula)
      0
    (if (undefp (evaluate-clause (car formula) assignment))
        (1+ (num-undef (cdr formula) assignment))
      (num-undef (cdr formula) assignment))))


(defthm natp-num-undef
  (natp (num-undef formula assignment))
  :rule-classes :type-prescription)

(defthm num-undef-cons
  (<= (num-undef formula (cons literal assignment))
      (num-undef formula assignment))
  :rule-classes :linear)

(defthm num-undef-cons-2
  (implies (mv-nth 0 (find-unit-clause formula assignment))
           (< (num-undef formula
                         (cons (mv-nth 0 (find-unit-clause formula assignment))
                               assignment))
              (num-undef formula assignment))))


;; ======================== UNIT-PROPAGATION =========================

(defun unit-propagation (formula assignment) ; primitive
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))
                  :measure (num-undef formula assignment)))
  (mv-let (unit-literal unit-clause)
          (find-unit-clause formula assignment)
          (declare (ignorable unit-clause))
          (if (not unit-literal)
              assignment
            (unit-propagation formula (cons unit-literal assignment)))))


(defthm assignmentp-unit-propagation
  (implies (formulap formula)
           (equal (assignmentp (unit-propagation formula assignment))
                  (assignmentp assignment))))


;; ========================= REMOVE-LITERAL ==========================

(defun remove-literal (literal clause)
  (declare (xargs :guard (and (literalp literal)
                              (clausep clause))))
  (if (atom clause)
      nil
    (if (equal (car clause) literal)
        (remove-literal literal (cdr clause))
      (cons (car clause)
            (remove-literal literal (cdr clause))))))


(defthm not-member-remove-literal
  (not (member lit (remove-literal lit clause))))

(defthm member-remove-literal
  (iff (member lit1 (remove-literal lit2 clause))
       (if (equal lit1 lit2)
           nil
         (member lit1 clause))))


(defthm literal-listp-remove-literal
  (implies (and (literalp literal)
                (clausep clause))
           (literal-listp (remove-literal literal clause))))

(defthm unique-literalsp-remove-literal
  (implies (and (literalp literal)
                (clausep clause))
           (unique-literalsp (remove-literal literal clause))))

(defthm no-conflicting-literalsp-remove-literal
  (implies (and (literalp literal)
                (clausep clause))
           (no-conflicting-literalsp (remove-literal literal clause))))


(defthm clausep-remove-literal
  (implies (and (literalp literal)
                (clausep clause))
           (clausep (remove-literal literal clause))))


;; =========================== RESOLUTION ============================

(defun resolution (lit A B)
  (declare (xargs :guard (and (literalp lit)
                              (clausep A)
                              (clausep B))))
  (union (remove-literal lit A)
         (remove-literal (negate lit) B)))


(defthm member-union
  (iff (member e (union A B))
       (or (member e A)
           (member e B))))


(defthm literal-listp-union
  (implies (and (clausep A)
                (clausep B))
           (literal-listp (union A B))))

(defthm unique-literalsp-union
  (implies (and (clausep A)
                (clausep B))
           (unique-literalsp (union A B))))


(defthm literal-listp-resolution
  (implies (and (literalp lit)
                (clausep A)
                (clausep B))
           (literal-listp (resolution lit A B))))

(defthm unique-literalsp-resolution
  (implies (and (literalp lit)
                (clausep A)
                (clausep B))
           (unique-literalsp (resolution lit A B))))


;; ============================== RATp ===============================

(defun tautologyp (clause)
  (declare (xargs :guard (literal-listp clause)))
  (not (no-conflicting-literalsp clause)))

(defun ATp (formula clause)
  (declare (xargs :guard (and (formulap formula)
                              (clausep clause))))
  (falsep (evaluate-formula formula
                            (unit-propagation formula
                                              (negate-clause clause)))))

(defun resolution-keeping-lit (lit a b)
  (declare (xargs :guard (and (literalp lit)
                              (clausep a)
                              (clausep b))))
  (union a ; instead of (remove-literal lit a)
         (remove-literal (negate lit) b)))

(defun RATp1 (formula-tail formula proof-clause literal)
  (declare (xargs :guard (and (formulap formula-tail)
                              (formulap formula)
                              (clausep proof-clause)
                              (literalp literal))))
  (if (atom formula-tail)
      t
    (if (not (member (negate literal) (car formula-tail)))
        (RATp1 (cdr formula-tail) formula proof-clause literal)
      (let ((resolvent (resolution literal proof-clause (car formula-tail))))
; We want to extend resolvent by literal.  So use resolution-keeping-lit
; instead of resolution just above.
; Also, we want to do more unit propagation, and ignore attempts to delete
; pseudo-unit clauses (i.e., units given an assignment A0), as follows.
; We will maintain a "permanent assignment" Forced that is monotonically
; increasing as we go through the proof.  We proceed as follows.
; (1) [new] Unit-propagate from Forced to weakly extend to new Forced.
; (2) Extend Forced with negation of next proof clause, PC, to get A2.
; (3) Unit-propagate from A2 to get A3.
; (4) For each "rat candidate" RC, i.e., where literal p in PC
;     occurs as -p in the rat candidate:
;     (4a) Extend A3 to A4a by adding negations of all literals from RC except
;         -p (called (car formula-tail) above).
;     (4b) Unit-propagate from A4a to get contradiction (else proof is invalid).
;     (4c) Pop back to A3 for the next rat candidate.
; (5) Recur, popping back the assignment to Forced.
       (if (tautologyp resolvent)
           (RATp1 (cdr formula-tail) formula proof-clause literal)
         (and (ATp formula resolvent)
              (RATp1 (cdr formula-tail) formula proof-clause literal)))))))

(defun RATp (formula proof-clause literal)
  (declare (xargs :guard (and (formulap formula)
                              (clausep proof-clause)
                              (literalp literal))))
  (RATp1 formula formula proof-clause literal))





;; ======================= VERIFY-UNSAT-PROOF ========================



(defun verify-clause (proof-clause formula)
  (declare (xargs :guard (and (clausep proof-clause)
                              (formulap formula))))
  (or (ATp formula proof-clause)
      (and (not (atom proof-clause))
           (RATp formula proof-clause (car proof-clause)))))

(defun verify-proof (d-clause-list formula)
  (declare (xargs :guard (and (formulap formula)
                              (d-clause-listp d-clause-list))))
  (if (atom d-clause-list)
      t
    (let* ((pair (car d-clause-list))
           (delete-flg (car pair))
           (proof-clause (cdr pair))
           (rest-clause-list (cdr d-clause-list)))
      (cond
       (delete-flg
        (verify-proof rest-clause-list (remove1-equal proof-clause formula)))
       ((verify-clause proof-clause formula)
        (verify-proof rest-clause-list (cons proof-clause formula)))
       (t nil)))))

(defun proofp (proof formula)
  (declare (xargs :guard (formulap formula)))
  (and (d-clause-listp proof)
       (verify-proof proof formula)))

(defconst *empty-clause* nil)

(defthm d-clause-listp-forward-to-true-listp
  (implies (d-clause-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defun refutationp (proof formula)
  (declare (xargs :guard (formulap formula)))
  (and (proofp proof formula)
       (member *empty-clause* proof)))



(defun solutionp (solution formula)
  (declare (xargs :guard (formulap formula)))
  (and (assignmentp solution)
       (truep (evaluate-formula formula solution))))

(defun-sk exists-solution (formula)
  (exists assignment (solutionp assignment formula)))
(in-theory (disable exists-solution
                    exists-solution-suff))




;; ===================================================================
;; ============================= ATP NIL =============================
;; ===================================================================

(defthm truep-evaluate-clause-subsetp
  (implies (and (subsetp sub super)
                (truep (evaluate-clause clause sub)))
           (truep (evaluate-clause clause super))))

(defthm truep-evaluate-formula-subsetp
  (implies (and (subsetp sub super)
                (truep (evaluate-formula formula sub)))
           (truep (evaluate-formula formula super))))


(defthm assignmentp-and-member-implies-not-member-negate
  (implies (and (assignmentp assignment)
                (member literal assignment))
           (not (member (negate literal) assignment)))
  :hints (("Goal"
           :in-theory (enable assignmentp))))

(defthm falsep-evaluate-clause-subsetp
  (implies (and (subsetp sub super)
                (falsep (evaluate-clause clause sub))
                (assignmentp super))
           (falsep (evaluate-clause clause super)))
  :hints (("Goal"
           :in-theory (disable
                       not-set-difference-variables-implies-subset-variablesp
                       is-unit-clause-implies-undefp-evaluate-clause
                       subsetp-and-set-equal-variablesp-implies-subsetp))))

(defthm falsep-evaluate-formula-subsetp
  (implies (and (subsetp sub super)
                (falsep (evaluate-formula formula sub))
                (assignmentp super))
           (falsep (evaluate-formula formula super))))


(defthm truep-evaluate-clause-is-unit-clause-subsetp
  (implies (and (subsetp sub super)
                (truep (evaluate-clause clause super))
                (is-unit-clause clause sub)
                (assignmentp super))
           (member (is-unit-clause clause sub)
                   super))
  :hints (("Goal"
           :in-theory (disable
                       not-set-difference-variables-implies-subset-variablesp
                       is-unit-clause-implies-undefp-evaluate-clause
                       subsetp-and-set-equal-variablesp-implies-subsetp))))

(in-theory (disable assignmentp-and-member-implies-not-member-negate))



(defthm truep-evaluate-formula-find-unit-clause-subsetp
  (implies (and (subsetp sub super)
                (truep (evaluate-formula formula super))
                (mv-nth 0 (find-unit-clause formula sub))
                (assignmentp super))
           (member (mv-nth 0 (find-unit-clause formula sub))
                   super)))

(defthm truep-evaluate-formula-unit-propagation-subsetp
  (implies (and (subsetp sub super)
                (truep (evaluate-formula formula super))
                (assignmentp super))
           (subsetp (unit-propagation formula sub) super)))


(defthm evaluate-formula-unit-propagation-nil
  (implies (and (assignmentp solution)
                (truep (evaluate-formula formula solution)))
           (not (falsep (evaluate-formula formula
                                          (unit-propagation formula nil)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable falsep-evaluate-formula-subsetp
                               truep-evaluate-formula-unit-propagation-subsetp)
           :use ((:instance truep-evaluate-formula-unit-propagation-subsetp
                            (sub nil)
                            (super solution))
                 (:instance falsep-evaluate-formula-subsetp
                            (sub (unit-propagation formula nil))
                            (super solution))))))


(defthm solutionp-implies-not-ATp-*empty-clause*
  (implies (solutionp solution formula)
           (not (ATp formula *empty-clause*))))

; redundant even with name-from-paper
(defthm *empty-clause*-lemma
  (implies (solutionp solution formula)
           (not (ATp formula *empty-clause*))))

(defthm exists-solution-implies-not-ATp-*empty-clause*
  (implies (exists-solution formula)
           (not (ATp formula *empty-clause*)))
  :hints (("Goal"
           :use ((:instance (:definition exists-solution))))))





;; ===================================================================
;; =============================== ATp ===============================
;; ===================================================================

;; ======================= EXISTS-TRUE-LITERAL =======================

(defun find-true-literal-in-clause (clause assignment)
  (if (atom clause)
      nil
    (if (member (car clause) assignment)
        (car clause)
      (find-true-literal-in-clause (cdr clause) assignment))))


(defthm truep-evaluate-clause-implies-find-true-literal-in-clause
  (implies (clausep clause)
           (iff (find-true-literal-in-clause clause assignment)
                (truep (evaluate-clause clause assignment)))))

(defthm find-true-literal-in-clause-implies-member-clause
  (implies (find-true-literal-in-clause clause assignment)
           (member (find-true-literal-in-clause clause assignment)
                   clause)))

(defthm find-true-literal-in-clause-implies-member-assignment
  (implies (find-true-literal-in-clause clause assignment)
           (member (find-true-literal-in-clause clause assignment)
                   assignment)))

(defthm find-true-literal-in-clause-implies-member-assignment
  (implies (find-true-literal-in-clause clause assignment)
           (member (find-true-literal-in-clause clause assignment)
                   assignment)))

(defthm find-true-literal-in-clause-implies-literalp
  (implies (and (clausep clause)
                (find-true-literal-in-clause clause assignment))
           (literalp (find-true-literal-in-clause clause assignment))))

(defun-sk exists-true-literal (clause assignment)
  (exists literal (and (member literal clause)
                       (member literal assignment))))
(in-theory (disable exists-true-literal
                    exists-true-literal-suff))

(defthm truep-evaluate-clause-implies-exists-true-literal
  (implies (and (clausep clause)
                (truep (evaluate-clause clause assignment)))
           (exists-true-literal clause assignment))
  :hints (("Goal"
           :use ((:instance exists-true-literal-suff
                            (literal (find-true-literal-in-clause
                                      clause
                                      assignment)))))))

(defthm member-both-implies-truep-evaluate-clause
  (implies (and (member literal clause)
                (member literal assignment))
           (truep (evaluate-clause clause assignment))))


;; ===================================================================

(defthm truep-evaluate-clause-negate-assignment
  (implies (and (literalp literal)
                (member literal solution)
                (member (negate literal) assignment))
           (truep (evaluate-clause (negate-assignment assignment)
                                   solution))))

(defthm evaluate-clause-implies-truep-evaluate-clause-negate-assignment
  (implies (and (clausep clause)
                (truep (evaluate-clause clause solution))
                (falsep (evaluate-clause clause assignment)))
           (truep (evaluate-clause (negate-assignment assignment)
                                   solution))))

(defthm evaluate-formula-implies-truep-evaluate-clause-negate-assignment
  (implies (and (formulap formula)
                (truep (evaluate-formula formula solution))
                (falsep (evaluate-formula formula assignment)))
           (truep (evaluate-clause (negate-assignment assignment)
                                   solution)))
  :hints (("Goal"
           :in-theory (disable clausep))))



(defthm not-is-unit-clause-literal-implies-member-negate
  (implies (and (is-unit-clause clause assignment)
                (member literal clause)
                (not (equal literal (is-unit-clause clause assignment))))
           (member (negate literal) assignment)))

(defthm not-equal-unit-literal-implies-member-negate
  (implies (and (mv-nth 0 (find-unit-clause formula assignment))
                (member literal (mv-nth 1 (find-unit-clause
                                           formula
                                           assignment)))
                (not (equal literal (mv-nth 0 (find-unit-clause
                                               formula
                                               assignment)))))
           (member (negate literal) assignment)))


(defthm not-equal-unit-literal-implies-truep-negate-assignment
  (implies (and (literalp literal)
                (mv-nth 0 (find-unit-clause formula assignment))
                (member literal (mv-nth 1 (find-unit-clause
                                           formula
                                           assignment)))
                (not (equal literal (mv-nth 0 (find-unit-clause
                                               formula
                                               assignment))))
                (member literal solution))
           (truep (evaluate-clause (negate-assignment assignment)
                                    solution))))

(defthm truep-evaluate-formula-implies-exists-true-literal
  (implies (and (formulap formula)
                (truep (evaluate-formula formula solution))
                (mv-nth 0 (find-unit-clause formula assignment)))
           (exists-true-literal (mv-nth 1 (find-unit-clause
                                           formula
                                           assignment))
                                solution)))


(defthm find-unit-clause-and-member-negate-implies-truep-negate-assignment
  (implies (and (formulap formula)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (mv-nth 0 (find-unit-clause formula assignment))
                (member (negate (mv-nth 0 (find-unit-clause
                                           formula
                                           assignment)))
                        solution))
           (truep (evaluate-clause (negate-assignment assignment)
                                   solution)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (assignmentp-and-member-implies-not-member-negate)
                           (truep-evaluate-formula-implies-exists-true-literal))
           :use ((:instance truep-evaluate-formula-implies-exists-true-literal)
                 (:instance (:definition exists-true-literal)
                            (clause (mv-nth 1 (find-unit-clause
                                               formula
                                               assignment)))
                            (assignment solution))
                 (:instance
                  not-equal-unit-literal-implies-truep-negate-assignment
                  (literal (exists-true-literal-witness
                            (mv-nth 1 (find-unit-clause formula assignment))
                            solution)))))))


(defthm falsep-EF-UP-implies-truep-EC-na
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            assignment)))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (assignmentp assignment)
                (assignmentp solution))
           (truep (evaluate-clause (negate-assignment assignment) solution))))

; redundant even with name-from-paper
(defthm ATp-lemma-induction
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            assignment)))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (assignmentp assignment)
                (assignmentp solution))
           (truep (evaluate-clause (negate-assignment assignment) solution))))

(defthm falsep-EF-UP-nc-implies-truep-EC
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            (negate-clause
                                                             clause))))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (clausep clause)
                (assignmentp solution))
           (truep (evaluate-clause clause solution)))
  :hints (("Goal"
           :use ((:instance falsep-EF-UP-implies-truep-EC-na
                            (assignment (negate-clause clause)))))))


(defthm solutionp-and-ATp-implies-truep-evaluate-clause
  (implies (and (ATp formula clause)
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (clausep clause)
                (assignmentp solution))
           (truep (evaluate-clause clause solution))))



(defthm solutionp-and-ATp-implies-solutionp-cons
  (implies (and (ATp formula clause)
                (solutionp solution formula)
                (formulap formula)
                (clausep clause))
           (solutionp solution (cons clause formula)))
  :hints (("Goal" :in-theory (disable ATp clausep))))


(defthm exists-solution-and-ATp-implies-exists-solution
  (implies (and (ATp formula clause)
                (exists-solution formula)
                (formulap formula)
                (clausep clause))
           (exists-solution (cons clause formula)))
  :hints (("Goal"
           :in-theory (disable solutionp)
           :use ((:instance (:definition exists-solution))
                 (:instance exists-solution-suff
                            (assignment (exists-solution-witness formula))
                            (formula (cons clause formula)))))))

; redudant even with name-from-paper
(defthm ATp-lemma
  (implies (and (ATp formula clause)
                (exists-solution formula)
                (formulap formula)
                (clausep clause))
           (exists-solution (cons clause formula))))


;; ===================================================================
;; ============================== RATp ===============================
;; ============================ FALSE-EC =============================
;; ===================================================================

;; ========================= MODIFY-SOLUTION =========================


(defun modify-solution (solution literal)
  (cons literal
        (remove-literal literal
                        (remove-literal (negate literal)
                                        solution))))

(defthm assignmentp-modify-solution
  (implies (and (assignmentp solution)
                (literalp literal))
           (assignmentp (modify-solution solution literal)))
  :hints (("Goal"
           :in-theory (enable assignmentp))))


(defthm member-implies-truep-evaluate-clause-modify-solution
  (implies (and (clausep clause)
                (assignmentp solution)
                (member literal clause))
           (truep (evaluate-clause clause
                                   (modify-solution solution literal)))))

(defthm truep-EC-and-not-member-negate-implies-truep-EC-modify-solution
  (implies (and (not (member (negate literal) clause))
                (truep (evaluate-clause clause solution)))
           (truep (evaluate-clause clause
                                   (modify-solution solution literal)))))


;; =================== EXISTS-CONFLICTING-LITERAL ====================

(defun find-conflicting-literal (pseudo-clause)
  (if (atom pseudo-clause)
      nil
    (if (member (negate (car pseudo-clause)) (cdr pseudo-clause))
        (car pseudo-clause)
      (find-conflicting-literal (cdr pseudo-clause)))))

(defthm not-no-conflicting-literalsp-implies-find-conflicting-literal
  (implies (and (literal-listp pseudo-clause)
                (not (no-conflicting-literalsp pseudo-clause)))
           (find-conflicting-literal pseudo-clause)))

(defthm find-conflicting-literal-implies-member
  (implies (find-conflicting-literal pseudo-clause)
           (member (find-conflicting-literal pseudo-clause)
                   pseudo-clause)))

(defthm find-conflicting-literal-implies-member-negate
  (implies (find-conflicting-literal pseudo-clause)
           (member (negate (find-conflicting-literal pseudo-clause))
                   pseudo-clause)))

(defun-sk exists-conflicting-literal (pseudo-clause)
  (exists literal (and (member literal pseudo-clause)
                       (member (negate literal) pseudo-clause))))
(in-theory (disable exists-conflicting-literal
                    exists-conflicting-literal-suff))


(defthm not-no-conflicting-literalsp-implies-exists-conflicting-literal
  (implies (and (literal-listp pseudo-clause)
                (not (no-conflicting-literalsp pseudo-clause)))
           (exists-conflicting-literal pseudo-clause))
  :hints (("Goal"
           :use ((:instance exists-conflicting-literal-suff
                            (literal (find-conflicting-literal
                                      pseudo-clause)))))))

(defthm member-and-member-negate-implies-not-no-conflicting-literalsp
  (implies (and (literalp literal)
                (member literal pseudo-clause)
                (member (negate literal) pseudo-clause))
           (not (no-conflicting-literalsp pseudo-clause))))



;; ========================= RATP TAUTOLOGY ==========================

(defthm conflicting-literal-and-false-EC-implies-member-negate
  (implies (and (member conflicting-literal rat-clause)
                (falsep (evaluate-clause rat-clause solution)))
           (member (negate conflicting-literal) solution)))

(defthm conflicting-literal-resolvent-implies-true-EC-modify-solution
  (implies (and (clausep clause)
                (clausep rat-clause)
                (member literal rat-clause)
                (member (negate literal) clause)
                (not (no-conflicting-literalsp (resolution literal rat-clause clause)))
                (falsep (evaluate-clause rat-clause solution))
                (truep (evaluate-clause clause solution)))
           (truep (evaluate-clause clause (modify-solution solution
                                                           literal))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable evaluate-clause
                               not-no-conflicting-literalsp
                               modify-solution)
           :use ((:instance
                  not-no-conflicting-literalsp-implies-exists-conflicting-literal
                  (pseudo-clause (resolution literal rat-clause clause)))
                 (:instance (:definition exists-conflicting-literal)
                            (pseudo-clause (resolution literal
                                                       rat-clause
                                                       clause)))))
          ("Subgoal 2"
           :do-not-induct t
           :in-theory (disable
                       conflicting-literal-and-false-EC-implies-member-negate
                       member-union)
           :use ((:instance conflicting-literal-and-false-EC-implies-member-negate
                            (conflicting-literal
                             (exists-conflicting-literal-witness
                              (resolution literal rat-clause clause))))
                 (:instance member-union
                            (e (NEGATE (EXISTS-CONFLICTING-LITERAL-WITNESS
                                  (UNION (REMOVE-LITERAL LITERAL RAT-CLAUSE)
                                         (REMOVE-LITERAL (NEGATE LITERAL)
                                                         CLAUSE)))))
                            (a (REMOVE-LITERAL LITERAL RAT-CLAUSE))
                            (b (REMOVE-LITERAL (NEGATE LITERAL)
                                            CLAUSE)))))
          ("Subgoal 1"
           :do-not-induct t
           :in-theory (disable
                       conflicting-literal-and-false-EC-implies-member-negate
                       member-union)
           :use ((:instance conflicting-literal-and-false-EC-implies-member-negate
                            (conflicting-literal
                             (negate (exists-conflicting-literal-witness
                              (resolution literal rat-clause clause)))))
                 (:instance member-union
                            (e (NEGATE (EXISTS-CONFLICTING-LITERAL-WITNESS
                                  (UNION (REMOVE-LITERAL LITERAL RAT-CLAUSE)
                                         (REMOVE-LITERAL (NEGATE LITERAL)
                                                         CLAUSE)))))
                            (a (REMOVE-LITERAL LITERAL RAT-CLAUSE))
                            (b (REMOVE-LITERAL (NEGATE LITERAL)
                                            CLAUSE)))))))



(defthm truep-evaluate-formula-and-member-implies-truep-evaluate-clause
  (implies (and (truep (evaluate-formula formula solution))
                (member clause formula))
           (truep (evaluate-clause clause solution))))



;; ========================= RATP MAIN CASE ==========================



(defthm solution-literal-and-not-equal-implies-true-evaluate-clause-modify-solution
  (implies (and (not (equal solution-literal (negate literal)))
                (member solution-literal clause)
                (member solution-literal solution))
           (truep (evaluate-clause clause
                                   (modify-solution solution literal)))))

(defthm clausep-resolution
  (implies (and (clausep rat-clause)
                (clausep clause)
                (literalp literal)
                (no-conflicting-literalsp (resolution literal rat-clause
                                                      clause)))
           (clausep (resolution literal rat-clause clause))))

(defthm falsep-evaluate-clause-and-member-implies-not-member
  (implies (and (falsep (evaluate-clause clause solution))
                (member literal solution))
           (not (member literal clause))))

(defthm not-member-and-member-resolution-implies-member
  (implies (and (not (member witness-literal rat-clause))
                (member witness-literal (resolution literal rat-clause clause)))
           (member witness-literal clause)))

(defthm member-resolution-implies-not-equal-negate
 (implies (and (clausep rat-clause)
               (member literal rat-clause)
               (member witness-literal (resolution literal rat-clause clause)))
          (not (equal witness-literal (negate literal)))))


(defthm true-EC-resolution-implies-true-EC-modify-solution
  (implies (and (clausep rat-clause)
                (clausep clause)
                (literalp literal)
                (no-conflicting-literalsp (resolution literal rat-clause
                                                      clause))
                (assignmentp solution)
                (member literal rat-clause)
                (member (negate literal) clause)
                (truep (evaluate-clause clause solution))
                (falsep (evaluate-clause rat-clause solution))
                (truep (evaluate-clause (resolution literal rat-clause clause)
                                        solution)))
           (truep (evaluate-clause clause (modify-solution solution literal))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable resolution modify-solution clausep
                               evaluate-clause member
                               TRUEP-EVALUATE-CLAUSE-IMPLIES-EXISTS-TRUE-LITERAL
                               falsep-evaluate-clause-and-member-implies-not-member
                               not-member-and-member-resolution-implies-member
                               member-resolution-implies-not-equal-negate)
           :use ((:instance truep-evaluate-clause-implies-exists-true-literal
                            (assignment solution))
                 (:instance (:definition exists-true-literal)
                            (assignment solution))))
          ("Goal'4'"
           :cases ((equal (exists-true-literal-witness clause solution)
                          (negate literal))))
          ("Subgoal 1'"
           :use ((:instance truep-evaluate-clause-implies-exists-true-literal
                            (assignment solution)
                            (clause (resolution literal rat-clause clause)))
                 (:instance (:definition exists-true-literal)
                            (assignment solution)
                            (clause (resolution literal rat-clause clause)))))
          ("Subgoal 1'4'"
           :use ((:instance
                  falsep-evaluate-clause-and-member-implies-not-member
                  (clause rat-clause)
                  (literal (exists-true-literal-witness (resolution literal
                                                                    rat-clause
                                                                    clause)
                                                        solution)))
                 (:instance
                  not-member-and-member-resolution-implies-member
                  (witness-literal (exists-true-literal-witness (resolution
                                                                 literal
                                                                 rat-clause
                                                                 clause)
                                                                solution)))
                 (:instance member-resolution-implies-not-equal-negate
                  (witness-literal (exists-true-literal-witness (resolution
                                                                 literal
                                                                 rat-clause
                                                                 clause)
                                                                solution))) ))))






(defthm ATp-and-truep-evaluate-clause-implies-truep-evaluate-clause-modify-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (clausep rat-clause)
                (literalp literal)
                (member literal rat-clause)
                (member (negate literal) clause)
                (ATp formula (resolution literal rat-clause clause))
                (truep (evaluate-formula formula solution))
                (truep (evaluate-clause clause solution))
                (falsep (evaluate-clause rat-clause solution))
                (no-conflicting-literalsp (resolution literal rat-clause clause)))
           (truep (evaluate-clause clause (modify-solution solution literal))))
  :hints (("Goal"
           :in-theory (disable ATp resolution modify-solution clausep
                               solutionp-and-ATp-implies-truep-evaluate-clause)
           :use ((:instance solutionp-and-ATp-implies-truep-evaluate-clause
                            (clause (resolution literal rat-clause clause)))))))




;; ========================= RATP INDUCTION ==========================


(defthm truep-EC-and-RATp1-implies-truep-EC-modify-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (clausep rat-clause)
                (RATp1 clause-list formula RAT-clause literal)
                (member clause clause-list)
                (member literal RAT-clause)
                (truep (evaluate-clause clause solution))
                (subsetp clause-list formula)
                (truep (evaluate-formula formula solution))
                (falsep (evaluate-clause RAT-clause solution)))
           (truep (evaluate-clause clause (modify-solution solution literal))))
  :hints (("Goal"
           :induct (RATp1 clause-list formula RAT-clause literal)
           :in-theory (disable ATp resolution modify-solution clausep
                               evaluate-clause))))

(defthm subsetp-reflexive
  (subsetp x x))

(defthm truep-EC-and-RATp-implies-truep-EC-modify-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (clausep rat-clause)
                (RATp formula RAT-clause literal)
                (member clause formula)
                (member literal RAT-clause)
                (truep (evaluate-clause clause solution))
                (truep (evaluate-formula formula solution))
                (falsep (evaluate-clause RAT-clause solution)))
           (truep (evaluate-clause clause (modify-solution solution literal))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable
                       ATp resolution modify-solution clausep evaluate-clause
                       truep-EC-and-RATp1-implies-truep-EC-modify-solution)
           :use ((:instance
                  truep-EC-and-RATp1-implies-truep-EC-modify-solution
                  (clause-list formula))))))


;; ======================= EXISTS-FALSE-CLAUSE =======================

(defun find-false-clause (formula assignment)
  (if (atom formula)
      (mv nil nil)
    (if (falsep (evaluate-clause (car formula) assignment))
        (mv t (car formula))
      (find-false-clause (cdr formula) assignment))))

(defthm falsep-evaluate-formula-implies-find-false-clause
  (implies (and (formulap formula)
                (falsep (evaluate-formula formula assignment)))
           (mv-nth 0 (find-false-clause formula assignment))))

(defthm find-false-clause-implies-clausep
  (implies (and (formulap formula)
                (mv-nth 0 (find-false-clause formula assignment)))
           (clausep (mv-nth 1 (find-false-clause formula assignment)))))

(defthm find-false-clause-implies-member
  (implies (mv-nth 0 (find-false-clause formula assignment))
           (member (mv-nth 1 (find-false-clause formula assignment))
                   formula)))

(defthm find-false-clause-implies-falsep-evaluate-clause
  (implies (mv-nth 0 (find-false-clause formula assignment))
           (falsep (evaluate-clause (mv-nth 1 (find-false-clause
                                               formula
                                               assignment))
                                    assignment))))

(defun-sk exists-false-clause (formula assignment)
  (exists clause (and (clausep clause)
                      (member clause formula)
                      (falsep (evaluate-clause clause assignment)))))
(in-theory (disable exists-false-clause
                    exists-false-clause-suff))

(defthm falsep-evaluate-formula-implies-exists-false-clause
  (implies (and (formulap formula)
                (falsep (evaluate-formula formula assignment)))
           (exists-false-clause formula assignment))
  :hints (("Goal"
           :use ((:instance exists-false-clause-suff
                            (clause (mv-nth 1 (find-false-clause
                                               formula
                                               assignment))))))))



;; ======================= EXISTS-UNDEF-CLAUSE =======================

(defun find-undef-clause (formula assignment)
  (if (atom formula)
      (mv nil nil)
    (if (undefp (evaluate-clause (car formula) assignment))
        (mv t (car formula))
      (find-undef-clause (cdr formula) assignment))))

(defthm undefp-evaluate-formula-implies-find-undef-clause
  (implies (and (formulap formula)
                (undefp (evaluate-formula formula assignment)))
           (mv-nth 0 (find-undef-clause formula assignment))))

(defthm find-undef-clause-implies-clausep
  (implies (and (formulap formula)
                (mv-nth 0 (find-undef-clause formula assignment)))
           (clausep (mv-nth 1 (find-undef-clause formula assignment)))))

(defthm find-undef-clause-implies-member
  (implies (mv-nth 0 (find-undef-clause formula assignment))
           (member (mv-nth 1 (find-undef-clause formula assignment))
                   formula)))

(defthm find-undef-clause-implies-undefp-evaluate-clause
  (implies (mv-nth 0 (find-undef-clause formula assignment))
           (undefp (evaluate-clause (mv-nth 1 (find-undef-clause
                                               formula
                                               assignment))
                                    assignment))))

(defun-sk exists-undef-clause (formula assignment)
  (exists clause (and (clausep clause)
                      (member clause formula)
                      (undefp (evaluate-clause clause assignment)))))
(in-theory (disable exists-undef-clause
                    exists-undef-clause-suff))

(defthm undefp-evaluate-formula-implies-exists-undef-clause
  (implies (and (formulap formula)
                (undefp (evaluate-formula formula assignment)))
           (exists-undef-clause formula assignment))
  :hints (("Goal"
           :use ((:instance exists-undef-clause-suff
                            (clause (mv-nth 1 (find-undef-clause
                                               formula
                                               assignment))))))))


;; ============================== RATP ===============================

(defthm member-cdr
  (implies (member e (cdr x))
           (member e x)))

(defthm truep-evaluate-formula-and-RATp-implies-truep-evaluate-formula-modify-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (RATp formula clause literal)
                (truep (evaluate-formula formula solution))
                (member literal clause)
                (falsep (evaluate-clause clause solution)))
           (truep (evaluate-formula formula
                                    (modify-solution solution literal))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable ATp resolution modify-solution clausep
                               RATp
                               member-equal
                               evaluate-clause
                               subsetp
                               ))
          ("Subgoal *1/12.2'"
           :in-theory (disable
                       ATp resolution modify-solution clausep RATp
                       member-equal evaluate-clause subsetp
                       TRUEP-EVALUATE-FORMULA-AND-MEMBER-IMPLIES-TRUEP-EVALUATE-CLAUSE
                       truep-EC-and-RATp-implies-truep-EC-modify-solution)
           :use ((:instance undefp-evaluate-formula-implies-exists-undef-clause
                            (formula (cdr formula))
                            (assignment (modify-solution solution literal)))
                 (:instance (:definition exists-undef-clause)
                            (formula (cdr formula))
                            (assignment (modify-solution solution literal)))
                 (:instance
                  TRUEP-EVALUATE-FORMULA-AND-MEMBER-IMPLIES-TRUEP-EVALUATE-CLAUSE
                  (clause (exists-undef-clause-witness (cdr formula)
                                                       (modify-solution
                                                        solution literal))))
                 (:instance
                  truep-EC-and-RATp-implies-truep-EC-modify-solution
                  (rat-clause clause)
                  (clause (exists-undef-clause-witness (cdr formula)
                                                       (modify-solution
                                                        solution literal))))))

          ("Subgoal *1/10.2'"
           :in-theory (enable ATp resolution modify-solution clausep
                              RATp evaluate-clause subsetp)
           :use ((:instance
                  truep-EC-and-RATp-implies-truep-EC-modify-solution
                  (rat-clause clause)
                  (clause (car formula)))))
          ("Subgoal *1/8.2'"
           :in-theory (enable ATp resolution modify-solution clausep
                              RATp evaluate-clause subsetp)
           :use ((:instance
                  truep-EC-and-RATp-implies-truep-EC-modify-solution
                  (rat-clause clause)
                  (clause (car formula)))))
          ("Subgoal *1/4.1'"
           :in-theory (disable
                       ATp resolution modify-solution clausep RATp
                       member-equal evaluate-clause subsetp
                       TRUEP-EVALUATE-FORMULA-AND-MEMBER-IMPLIES-TRUEP-EVALUATE-CLAUSE
                       truep-EC-and-RATp-implies-truep-EC-modify-solution)
           :use ((:instance falsep-evaluate-formula-implies-exists-false-clause
                            (formula (cdr formula))
                            (assignment (modify-solution solution literal)))
                 (:instance (:definition exists-false-clause)
                            (formula (cdr formula))
                            (assignment (modify-solution solution literal)))
                 (:instance
                  TRUEP-EVALUATE-FORMULA-AND-MEMBER-IMPLIES-TRUEP-EVALUATE-CLAUSE
                  (clause (exists-false-clause-witness (cdr formula)
                                                       (modify-solution
                                                        solution literal))))
                 (:instance
                  truep-EC-and-RATp-implies-truep-EC-modify-solution
                  (rat-clause clause)
                  (clause (exists-false-clause-witness (cdr formula)
                                                       (modify-solution
                                                        solution literal))))))
          ("Subgoal *1/2.1'"
           :in-theory (enable ATp resolution modify-solution clausep
                              RATp evaluate-clause subsetp)
           :use ((:instance
                  truep-EC-and-RATp-implies-truep-EC-modify-solution
                  (rat-clause clause)
                  (clause (car formula)))))))




(defthm equal-falsep-evaluate-formula-cons
  (implies (truep (evaluate-formula formula assignment))
           (equal (falsep (evaluate-formula (cons clause formula) assignment))
                  (falsep (evaluate-clause clause assignment)))))


(defthm exists-solution-and-RATp-and-truep-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (RATp formula clause literal)
                (member literal clause)
                (falsep (evaluate-clause clause solution)))
           (exists-solution (cons clause formula)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable clausep RATp evaluate-formula
                               evaluate-clause modify-solution)
           :use ((:instance exists-solution-suff
                            (assignment (modify-solution solution literal))
                            (formula (cons clause formula)))))))



;; ===================================================================
;; ============================ UNDEF-EC =============================
;; ===================================================================

;; ====================== EXISTS-UNDEF-LITERAL =======================

(defun find-undef-literal (clause assignment)
  (if (atom clause)
      nil
    (if (and (not (member (car clause) assignment))
             (not (member (negate (car clause)) assignment)))
        (car clause)
      (find-undef-literal (cdr clause) assignment))))


(defthm undefp-EC-implies-find-undef-literal
  (implies (and (clausep clause)
                (undefp (evaluate-clause clause assignment)))
           (find-undef-literal clause assignment)))

(defthm find-undef-literal-implies-member-clause
  (implies (find-undef-literal clause assignment)
           (member (find-undef-literal clause assignment)
                   clause)))

(defthm find-undef-literal-implies-not-member-assignment
  (implies (find-undef-literal clause assignment)
           (not (member (find-undef-literal clause assignment)
                        assignment))))

(defthm find-undef-literal-implies-not-member-negate-assignment
  (implies (find-undef-literal clause assignment)
           (not (member (negate (find-undef-literal clause assignment))
                        assignment))))


(defun-sk exists-undef-literal (clause assignment)
  (exists literal (and (member literal clause)
                       (not (member literal assignment))
                       (not (member (negate literal) assignment)))))
(in-theory (disable exists-undef-literal
                    exists-undef-literal-suff))


(defthm undefp-EC-implies-exists-undef-literal
  (implies (and (clausep clause)
                (undefp (evaluate-clause clause assignment)))
           (exists-undef-literal clause assignment))
  :hints (("Goal"
           :use ((:instance exists-undef-literal-suff
                            (literal (find-undef-literal
                                      clause
                                      assignment)))))))



;; ===================================================================


(defthm truep-EF-implies-truep-EF-cons
  (implies (truep (evaluate-formula formula solution))
           (truep (evaluate-formula formula (cons literal solution))))
  :hints (("Goal"
           :in-theory (disable evaluate-clause))))


(defthm equal-undefp-evaluate-formula-cons
  (implies (truep (evaluate-formula formula assignment))
           (equal (undefp (evaluate-formula (cons clause formula) assignment))
                  (undefp (evaluate-clause clause assignment)))))

(defthm truep-EF-and-undefp-EF-cons-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (undefp (evaluate-formula (cons clause formula) solution)))
           (exists-solution (cons clause formula)))
  :hints (("Goal"
           :in-theory (disable evaluate-clause evaluate-formula)
           :use ((:instance undefp-EC-implies-exists-undef-literal
                            (assignment solution))
                 (:instance (:definition exists-undef-literal)
                            (assignment solution))
                 (:instance exists-solution-suff
                            (assignment (cons (exists-undef-literal-witness
                                               clause
                                               solution)
                                              solution))
                            (formula (cons clause formula)))))))



;; ===================================================================
;; ============================ TRUEP-EC =============================


(defthm solutionp-and-truep-EF-cons-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (truep (evaluate-clause clause solution)))
           (exists-solution (cons clause formula)))
  :hints (("Goal"
           :use ((:instance exists-solution-suff
                            (assignment solution)
                            (formula (cons clause formula)))))))


;; ===================================================================
;; =========================== CASE-SPLIT ============================
;; ===================================================================

; case split on original solution
(defthm solutionp-and-RATp-implies-exists-solution-cons
  (implies (and (formulap formula)
                (clausep clause)
                (solutionp solution formula)
                (RATp formula clause literal)
                (member literal clause))
           (exists-solution (cons clause formula)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable RATp evaluate-formula clausep)
           :cases ((truep (evaluate-formula (cons clause formula) solution))
                   (undefp (evaluate-formula (cons clause formula) solution))
                   (falsep (evaluate-formula (cons clause formula) solution)))) ))



(defthm exists-solution-and-RATp-implies-exists-solution-cons
  (implies (and (RATp formula clause literal)
                (formulap formula)
                (clausep clause)
                (exists-solution formula)
                (member literal clause))
           (exists-solution (cons clause formula)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable RATp solutionp clausep)
           :use ((:instance (:definition exists-solution))))))

(defconst *empty-clause-proof-step* ; addition of empty clause
  (cons nil *empty-clause*))

; redundant even with name-from-paper
(defthm RATp-lemma
  (implies (and (formulap formula)
                (clausep clause)
                (member literal clause)
                (exists-solution formula)
                (RATp formula clause literal))
           (exists-solution (cons clause formula)))
  :hints (("Goal"
           :use exists-solution-and-RATp-implies-exists-solution-cons)))

(defthm formulap-remove1-equal
  (implies (formulap formula)
           (formulap (remove1-equal clause formula))))

(defthm remove1-equal-preserves-truep-evaluate-formula
  (implies (truep (evaluate-formula formula assignment))
           (truep (evaluate-formula (remove1-equal clause formula) assignment))))

(defthm remove1-equal-preserves-exists-solution
  (implies (exists-solution formula)
           (exists-solution (remove1-equal clause formula)))
  :hints (("Goal"
           :use ((:instance exists-solution (formula formula))
                 (:instance exists-solution-suff
                            (assignment (exists-solution-witness formula))
                            (formula (remove1-equal clause formula)))))))

; verify-proof induction
(defthm solution-and-member-nil-implies-not-verify-proof
  (implies (and (d-clause-listp d-clause-list)
                (formulap formula)
                (exists-solution formula)
                (member *empty-clause-proof-step* d-clause-list))
           (not (verify-proof d-clause-list formula)))
  :hints (("Goal"
           :in-theory (disable RATp ATp clausep))))


; redundant event with name from paper
(defthm verify-proof-induction
  (implies (and (d-clause-listp d-clause-list)
                (formulap formula)
                (exists-solution formula)
                (member *empty-clause-proof-step*
                        d-clause-list))
           (not (verify-proof d-clause-list formula)))
  :hints (("Goal"
           :in-theory (disable RATp ATp clausep))))



;; ===================================================================
;; =========================== MAIN PROOF ============================
;; ===================================================================

;; (defun-sk exists-solution (formula)
;;   (exists assignment (solutionp assignment formula)))
;; (in-theory (disable exists-solution
;;                     exists-solution-suff))

; Silly lemma 1:
(defthm exists-solution-implies-not-refutationp-lemma
  (implies (d-clause-listp d-clause-list)
           (alistp d-clause-list))
  :rule-classes :forward-chaining)

; Silly lemma 2:
(defthm alistp-has-pairs
  (implies (and (member-equal x a)
                (alistp a))
           (consp x))
  :rule-classes :forward-chaining)

(defthm exists-solution-implies-not-refutationp
  (implies (and (formulap formula)
                (exists-solution formula))
           (not (refutationp d-clause-list formula)))
  :hints (("Goal"
           :in-theory (disable solutionp)
           :use ((:instance exists-solution)))))

(defthm refutationp-implies-not-exists-solution
  (implies (and (formulap formula)
                (refutationp d-clause-list formula))
           (not (exists-solution formula)))
  :hints (("Goal"
           :use ((:instance exists-solution-implies-not-refutationp)))))

; redundant event with name from paper
(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp d-clause-list formula))
           (not (exists-solution formula))))


;; ===================================================================
;; ============================= EXAMPLE =============================
;; ===================================================================

;; (ld "rat-parser.lisp")

;; (in-package "PROOF-CHECKER-ITP13")


;; (defun get-formula (clause-list num-clauses)
;;   (cond
;;    ((atom clause-list) (mv nil nil))
;;    ((<= num-clauses 0) (mv nil clause-list))
;;    (t
;;     (mv-let (formula learned)
;;             (get-formula (cdr clause-list) (1- num-clauses))
;;             (mv (cons (car clause-list) formula) learned)))))


;; (defun verify-file (filename)
;;   (declare (xargs :mode :program))
;;   (b* (((mv fail ?num-vars num-clauses clause-list)
;;         (acl2::parse-unsat-proof filename))
;;        ((when fail) 'parse-fail)
;;        ((mv formula proof) (get-formula clause-list num-clauses)))
;;       (verify-proof proof formula)))


;; (defconst *input* (mv-let (fail num-vars num-clauses clause-list)
;;                           (acl2::parse-unsat-proof "rat-1")
;;                           (list fail num-vars num-clauses clause-list)))



;; (defconst *separated-input* (mv-let (formula proof)
;;                                     (get-formula (nth 3 *input*) (nth 2 *input*))
;;                                     (list formula proof)))

;; (defconst *formula* (nth 0 *separated-input*))
;; (defconst *proof* (nth 1 *separated-input*))


;; (defthm unsat-proof
;;   (not (exists-solution *formula*))
;;   :hints (("Goal"
;;            :use ((:instance refutationp-implies-not-exists-solution
;;                             (clause-list *proof*)
;;                             (formula *formula*))))))
