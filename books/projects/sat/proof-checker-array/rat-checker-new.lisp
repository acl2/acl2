(in-package "PROOF-CHECKER-ARRAY")

(include-book "supplemental/ternary")
(include-book "supplemental/literal")
(include-book "supplemental/sets")
(include-book "supplemental/assignment")
(include-book "supplemental/clause")
(include-book "supplemental/evaluator")
(include-book "supplemental/unit-propagation")
(include-book "std/util/bstar" :dir :system)



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



(defthm literal-listp-revappend
  (implies (and (literal-listp x)
                (literal-listp y))
           (literal-listp (revappend x y))))

(defthm unique-literalsp-append
  (implies (and (unique-literalsp (append x y))
                (not (member e x))
                (not (member e y)))
           (unique-literalsp (append x (cons e y)))))

(defthm unique-literalsp-revappend
  (implies (unique-literalsp (append x y))
           (unique-literalsp (revappend x y)))
  :hints (("Goal" :induct (revappend x y))))


(defthm no-conflicting-literalsp-append
  (implies (and (no-conflicting-literalsp (append x y))
                (literalp e)
                (not (member (negate e) x))
                (not (member (negate e) y)))
           (no-conflicting-literalsp (append x (cons e y)))))

(defthm no-conflicting-literalsp-revappend
  (implies (and (no-conflicting-literalsp (append x y))
                (literal-listp x))
           (no-conflicting-literalsp (revappend x y)))
  :hints (("Goal" :induct (revappend x y))))

(defthm assignmentp-revappend-nil
  (implies (assignmentp assignment)
           (assignmentp (revappend assignment nil)))
  :hints (("Goal" :In-theory (enable assignmentp))))





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
                                              (revappend
                                               (negate-clause clause)
                                               nil)
                                              ))))

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

; redudant even with name-from-paper
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

; ****
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


; ****
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


; **
(defthm falsep-EF-UP-implies-truep-EC-na
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            assignment)))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (assignmentp assignment)
                (assignmentp solution))
           (truep (evaluate-clause (negate-assignment assignment) solution))))


;; (defthm falsep-EF-UP-implies-truep-EC-na
;;   (implies (and (falsep (evaluate-formula formula
;;                                           (unit-propagation formula
;;                                                             assignment)))
;;                 (truep (evaluate-formula formula solution))
;;                 (formulap formula)
;;                 (assignmentp assignment)
;;                 (assignmentp solution))
;;            (truep (evaluate-clause (negate-assignment assignment) solution))))

; redudant event with name-from-paper
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

(defthm negate-assignment-revappend
  (implies (and (literal-listp x)
                (literal-listp y))
           (equal (negate-assignment (revappend x y))
                  (revappend (negate-assignment x) (negate-assignment y))))
  :hints (("Goal" :induct (revappend x y))))

(defthm clausep-revappend-nil
  (implies (clausep clause)
           (clausep (revappend clause nil))))

(defthm member-revappend
  (implies (and (true-listp x)
                (true-listp y)
                ;(member e x)
                (member e y)
                )
           (member e (revappend x y))) )

(defthm member-revappend-2
  (implies (and (true-listp x)
                (true-listp y)
                (member e x)
                (not (member e y))
                )
           (member e (revappend x y))) )

(defthm member-revappend-3
  (implies (and (true-listp x)
                (true-listp y)
                (not (member e y))
                (member e (revappend x y)))
           (member e x)))

(defthm truep-EC-rev-implies-truep-EC
  (implies (and (truep (evaluate-clause (revappend clause nil)
                                        solution))
                (clausep clause)
                (assignmentp solution))
           (truep (evaluate-clause clause solution)))
  :hints (("Goal"
           :in-theory (disable
                       truep-evaluate-clause-implies-exists-true-literal
                       member-revappend-3
                       member-revappend-2)
           :use ((:instance truep-evaluate-clause-implies-exists-true-literal
                            (clause (revappend clause nil))
                            (assignment solution))
                 (:instance exists-true-literal
                            (clause (revappend clause nil))
                            (assignment solution))
                 (:instance member-revappend-3
                            (e (exists-true-literal-witness (revappend clause
                                                                       nil) solution))
                            (x clause)
                            (y nil))))))

(in-theory (disable member-revappend-3
                    member-revappend-2
                    member-revappend
                    clausep-revappend-nil
                    ))

(defthm falsep-EF-UP-rev-nc-implies-truep-EC
  (implies (and (falsep (evaluate-formula formula
                                          (unit-propagation formula
                                                            (revappend
                                                             (negate-clause
                                                              clause)
                                                             nil))))
                (truep (evaluate-formula formula solution))
                (formulap formula)
                (clausep clause)
                (assignmentp solution))
           (truep (evaluate-clause clause solution)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable falsep-EF-UP-implies-truep-EC-na
                               ATp-lemma-induction)
           :use ((:instance falsep-EF-UP-implies-truep-EC-na
                            ;; (assignment (negate-clause clause)))))))
                            (assignment (revappend (negate-clause clause)
                                                   nil)))))))


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

; redudant even with name-from-paper
(defthm RATp-lemma
  (implies (and (formulap formula)
                (clausep clause)
                (member literal clause)
                (exists-solution formula)
                (RATp formula clause literal))
           (exists-solution (cons clause formula)))
  :hints (("Goal"
           :use exists-solution-and-RATp-implies-exists-solution-cons)))


; verify-proof induction
(defthm solution-and-member-nil-implies-not-verify-proof
  (implies (and (clause-listp clause-list)
                (formulap formula)
                (exists-solution formula)
                (member *empty-clause* clause-list))
           (not (verify-proof clause-list formula)))
  :hints (("Goal"
           :in-theory (disable RATp ATp clausep))))


; redundant event with name from paper
(defthm verify-proof-induction
  (implies (and (clause-listp clause-list)
                (formulap formula)
                (exists-solution formula)
                (member *empty-clause* clause-list))
           (not (verify-proof clause-list formula)))
  :hints (("Goal"
           :in-theory (disable RATp ATp clausep))))



;; ===================================================================
;; =========================== MAIN PROOF ============================
;; ===================================================================

;; (defun-sk exists-solution (formula)
;;   (exists assignment (solutionp assignment formula)))
;; (in-theory (disable exists-solution
;;                     exists-solution-suff))


(defthm exists-solution-implies-not-refutationp
  (implies (and (formulap formula)
                (exists-solution formula))
           (not (refutationp clause-list formula)))
  :hints (("Goal"
           :in-theory (disable solutionp)
           :use ((:instance exists-solution)))))

(defthm refutationp-implies-not-exists-solution
  (implies (and (formulap formula)
                (refutationp clause-list formula))
           (not (exists-solution formula)))
  :hints (("Goal"
           :use ((:instance exists-solution-implies-not-refutationp)))))

; redundant event with name from paper
(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp clause-list formula))
           (not (exists-solution formula))))


;; ===================================================================
;; ============================= EXAMPLE =============================
;; ===================================================================

;; (ld "rat-parser.lisp")

;; (in-package "PROOF-CHECKER-ACL2")


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
