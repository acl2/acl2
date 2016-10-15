;; Copyright (c) 2016, Regents of the University of Texas
;;
;; License: The MIT License (MIT)
;;
;;   Permission is hereby granted, free of charge, to any person
;;   obtaining a copy of this software and associated documentation
;;   files (the "Software"), to deal in the Software without
;;   restriction, including without limitation the rights to use,
;;   copy, modify, merge, publish, distribute, sublicense, and/or sell
;;   copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following
;;   conditions:
;;
;;   The above copyright notice and this permission notice shall be
;;   included in all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
;;   OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;   OTHER DEALINGS IN THE SOFTWARE.
;;
;; Original author: Nathan Wetzler <nathan.wetzler@gmail.com>

;; Last Modified:  2016-08-29 20:49

;; ============================= PACKAGE =============================
(in-package "PROOF-CHECKER-ITP13")


;; ============================ INCLUDES =============================

(include-book "xdoc/top" :dir :system)
;; (include-book "xdoc/debug" :dir :system)

(include-book "rat-checker")


;; ===================================================================
;; ============================== XDOC ===============================
;; ===================================================================

(defxdoc PROOF-CHECKER-ITP13
  :parents (acl2::projects)
  :short "RAT Proof Checker for ITP 2013"
  )

(xdoc::order-subtopics
 PROOF-CHECKER-ITP13
 (;Background-And-Description
  ))

;; =========================== DESCRIPTION ===========================

(defsection Description
  :extension PROOF-CHECKER-ITP13
  ;; :parents (PROOF-CHECKER-ITP13)
  ;; :short ""
  :long
"<p>This proof is the supplemental material for a paper appearing in
  Interactive Theorem Proving 2013.  A README file describes the build process.
  Build, run, and clean scripts are provided for simplicity.  The paper is
  available online as a <a
  href='http://www.cs.utexas.edu/~nwetzler/publications/itp13.pdf'>preprint</a>
  or from <a
  href='http://link.springer.com/chapter/10.1007%2F978-3-642-39634-2_18'>Springer</a>.</p>
" )

;; ============================ ABSTRACT =============================

(defsection Abstract
  :extension PROOF-CHECKER-ITP13
  ;; :parents (PROOF-CHECKER-ITP13)
  ;; :short ""
  :long
"<h2>Abstract From Paper</h2>

<p> We present a mechanically-verified proof checker developed with the ACL2
theorem-proving system that is general enough to support the growing variety of
increasingly complex satisfiability (SAT) solver techniques, including those
based on extended resolution.  A common approach to assure the correctness of
SAT solvers is to emit a proof of unsatisfiability when no solution is reported
to exist.  Contemporary proof checkers only check logical equivalence using
resolution-style inference.  However, some state-of-the-art, conflict-driven
clause-learning SAT solvers use preprocessing, inprocessing, and learning
techniques, that cannot be checked solely by resolution-style inference.  We
have developed a mechanically-verified proof checker that assures refutation
clauses preserve satisfiability.  We believe our approach is sufficiently
expressive to validate all known SAT-solver techniques.</p>

<h2>Citation</h2>

<p>Mechanical verification of SAT refutations with extended resolution Nathan
Wetzler, Marijn J. H. Heule, and Warren A. Hunt, Jr.  Interactive Theorem
Proving (ITP), volume 7998 of LNCS, pages 229-244. Springer, 2013.</p>" )


;; ===================================================================

(set-enforce-redundancy t)

;; ===================================================================
;; =========================== DEFINITIONS ===========================
;; ===================================================================


;; ========================== CLAUSE-LISTP ===========================

(defun clause-listp (clause-list)
  (declare (xargs :guard t))
  (if (atom clause-list)
      (null clause-list)
    (and (clausep (car clause-list))
         (clause-listp (cdr clause-list)))))


;; ========================== NEGATE-CLAUSE ==========================
;; ======================== NEGATE-ASSIGNMENT ========================

(defun negate-clause (clause)
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


;; ======================== UNIT-PROPAGATION =========================

(defun num-undef (formula assignment)
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))))
  (if (atom formula)
      0
    (if (undefp (evaluate-clause (car formula) assignment))
        (1+ (num-undef (cdr formula) assignment))
      (num-undef (cdr formula) assignment))))


(defun unit-propagation (formula assignment)
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))
                  :measure (num-undef formula assignment)))
  (mv-let (unit-literal unit-clause)
          (find-unit-clause formula assignment)
          (declare (ignorable unit-clause))
          (if (not unit-literal)
              assignment
            (unit-propagation formula (cons unit-literal assignment)))))

           
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


;; =========================== RESOLUTION ============================

(defun resolution (lit A B)
  (declare (xargs :guard (and (literalp lit)
                              (clausep A)
                              (clausep B))))
  (union (remove-literal lit A)
         (remove-literal (negate lit) B)))


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

(defun RATp1 (clause-list formula clause literal)
  (declare (xargs :guard (and (clause-listp clause-list)
                              (formulap formula)
                              (clausep clause)
                              (literalp literal))))
  (if (atom clause-list)
      t
    (if (not (member (negate literal) (car clause-list)))
        (RATp1 (cdr clause-list) formula clause literal)
      (let ((resolvent (resolution literal clause (car clause-list))))
       (if (tautologyp resolvent)
           (RATp1 (cdr clause-list) formula clause literal)
         (and (ATp formula resolvent)
              (RATp1 (cdr clause-list) formula clause literal)))))))

(defun RATp (formula clause literal)
  (declare (xargs :guard (and (formulap formula)
                              (clausep clause)
                              (literalp literal))))
  (RATp1 formula formula clause literal))


;; ======================= VERIFY-UNSAT-PROOF ========================

(defun verify-clause (clause formula)
  (declare (xargs :guard (and (clausep clause)
                              (formulap formula))))
  (or (ATp formula clause)
      (and (not (atom clause))
           (RATp formula clause (car clause)))))

(defun verify-proof (clause-list formula)
  (declare (xargs :guard (and (formulap formula)
                              (clause-listp clause-list))))
  (if (atom clause-list)
      t
    (if (verify-clause (car clause-list) formula)
        (verify-proof (cdr clause-list) (cons (car clause-list) formula))
      nil)))


(defun proofp (proof formula)
  (declare (xargs :guard (formulap formula)))
  (and (clause-listp proof)
       (verify-proof proof formula)))

(defconst *empty-clause* nil)

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


;; ===================================================================
;; ============================= ATP NIL =============================
;; ===================================================================

(defthm evaluate-formula-unit-propagation-nil
  (implies (and (assignmentp solution)
                (truep (evaluate-formula formula solution)))
           (not (falsep (evaluate-formula formula
                                          (unit-propagation formula nil))))))

(defthm *empty-clause*-lemma
  (implies (solutionp solution formula)
           (not (ATp formula *empty-clause*))))


;; ===================================================================
;; =============================== ATp ===============================
;; ===================================================================

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
                                   solution))))


(defthm ATp-lemma-induction
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            assignment)))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (assignmentp assignment)
                (assignmentp solution))
           (truep (evaluate-clause (negate-assignment assignment) solution))))


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


;; ========================= RATP TAUTOLOGY ==========================

(defthm conflicting-literal-resolvent-implies-true-EC-modify-solution
  (implies (and (clausep clause)
                (clausep rat-clause)
                (member literal rat-clause)
                (member (negate literal) clause)
                (not (no-conflicting-literalsp (resolution literal rat-clause clause)))
                (falsep (evaluate-clause rat-clause solution))
                (truep (evaluate-clause clause solution)))
           (truep (evaluate-clause clause (modify-solution solution
                                                           literal)))))


;; ========================= RATP MAIN CASE ==========================

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
           (truep (evaluate-clause clause (modify-solution solution literal)))))

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
           (truep (evaluate-clause clause (modify-solution solution literal)))))


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
           (truep (evaluate-clause clause (modify-solution solution literal)))))

(defthm truep-evaluate-formula-and-RATp-implies-truep-evaluate-formula-modify-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (RATp formula clause literal)
                (truep (evaluate-formula formula solution))
                (member literal clause)
                (falsep (evaluate-clause clause solution)))
           (truep (evaluate-formula formula
                                    (modify-solution solution literal)))))


(defthm exists-solution-and-RATp-and-truep-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (RATp formula clause literal)
                (member literal clause)
                (falsep (evaluate-clause clause solution)))
           (exists-solution (cons clause formula))))


;; ===================================================================
;; ============================ UNDEF-EC =============================
;; ===================================================================

(defthm truep-EF-and-undefp-EF-cons-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (undefp (evaluate-formula (cons clause formula) solution)))
           (exists-solution (cons clause formula))))


;; ===================================================================
;; ============================ TRUEP-EC =============================
;; ===================================================================

(defthm solutionp-and-truep-EF-cons-implies-exists-solution
  (implies (and (formulap formula)
                (clausep clause)
                (assignmentp solution)
                (truep (evaluate-formula formula solution))
                (truep (evaluate-clause clause solution)))
           (exists-solution (cons clause formula))))

;; ===================================================================
;; =========================== CASE-SPLIT ============================               
;; ===================================================================

(defthm solutionp-and-RATp-implies-exists-solution-cons
  (implies (and (formulap formula)
                (clausep clause)
                (solutionp solution formula)
                (RATp formula clause literal)
                (member literal clause))
           (exists-solution (cons clause formula))))

(defthm RATp-lemma
  (implies (and (formulap formula)
                (clausep clause)
                (member literal clause)
                (exists-solution formula)
                (RATp formula clause literal))
           (exists-solution (cons clause formula))))

(defthm verify-proof-induction
  (implies (and (clause-listp clause-list)
                (formulap formula)
                (exists-solution formula)
                (member *empty-clause* clause-list))
           (not (verify-proof clause-list formula))))


;; ===================================================================
;; =========================== MAIN PROOF ============================
;; ===================================================================

(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp clause-list formula))
           (not (exists-solution formula))))
