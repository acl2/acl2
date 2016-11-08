(in-package "PROOF-CHECKER-ARRAY")

(include-book "ternary")
(include-book "literal")
(include-book "unique")
(include-book "sets")
(include-book "assignment")
(include-book "clause")
(include-book "all-literals")


;; ===================================================================
;; ======================= LITERAL EVALUATION ========================

(defun evaluate-literal (literal assignment)
  (declare (xargs :guard (and (literalp literal)
                              (assignmentp assignment))))
  (cond
   ((member literal assignment) (true))
   ((member (negate literal) assignment) (false))
   (t (undef))))


;; ===================================================================
;; ========================= EVALUATE-CLAUSE =========================

(defun evaluate-clause (clause assignment)
  (declare (xargs :guard (and (clausep clause)
                              (assignmentp assignment))))
  (if (atom clause)
      (false)
    (let* ((literal (car clause))
           (literal-value (evaluate-literal literal assignment)))
      (if (truep literal-value)
          (true)
        (let* ((remaining-clause (cdr clause))
               (remaining-clause-value (evaluate-clause remaining-clause
                                                        assignment)))
          (cond
           ((truep remaining-clause-value) (true))
           ((undefp literal-value) (undef))
           (t remaining-clause-value)))))))
       
(defthm ternaryp-evaluate-clause
  (ternaryp (evaluate-clause clause assignment)))


;; ===================================================================
;; ======================== EVALUATE-FORMULA =========================

(defun evaluate-formula (formula assignment)
  (declare (xargs :guard (and (formulap formula)
                              (assignmentp assignment))))
  (if (atom formula)
      (true)
    (let* ((clause (car formula))
           (clause-value (evaluate-clause clause assignment)))
      (if (falsep clause-value)
          (false)
        (let* ((remaining-formula (cdr formula))
               (remaining-formula-value (evaluate-formula remaining-formula
                                                          assignment)))
          (cond
           ((falsep remaining-formula-value) (false))
           ((undefp clause-value) (undef))
           (t remaining-formula-value)))))))

(defthm ternaryp-evaluate-formula
  (ternaryp (evaluate-formula formula assignment)))


;; ===================================================================
;; ============================== CONS ===============================

(defthm iff-truep-evaluate-clause-cons
  (iff (truep (evaluate-clause clause (cons literal assignment)))
       (or (member literal clause)
           (truep (evaluate-clause clause assignment)))))

(defthm truep-evaluate-formula-cons
  (equal (truep (evaluate-formula (cons clause formula) assignment))
         (and (truep (evaluate-clause clause assignment))
              (truep (evaluate-formula formula assignment)))))

(defthm not-undefp-evaluate-clause-cons
  (implies (not (undefp (evaluate-clause clause assignment)))
           (not (undefp (evaluate-clause clause (cons literal assignment))))))



;; ===================================================================
;; =================== SET EQUALITY AND EVALUATION ===================

; We can reduce any of these to truep implies truep.  They might be stronger
; than needed.

(defthm set-equalp-implies-equal-evaluate-literal
  (implies (and (set-equalp x y)
                (literalp literal)
                (assignmentp x)
                (assignmentp y))
           (equal (evaluate-literal literal y)
                  (evaluate-literal literal x))))


(defthm set-equalp-implies-equal-evaluate-clause
  (implies (and (set-equalp x y)
                (clausep clause)
                (assignmentp x)
                (assignmentp y))
           (equal (evaluate-clause clause y)
                  (evaluate-clause clause x))))
  ;; :hints (("Goal" :in-theory (disable
  ;; NOT-SET-DIFFERENCE-VARIABLES-IMPLIES-SUBSET-VARIABLESP
  ;; SUBSETP-AND-SET-EQUAL-VARIABLESP-IMPLIES-SUBSETP
  ;; SUBSET-VARIABLESP-AND-SUBSETP-IMPLIES-SUBSETP))))


(defthm set-equalp-implies-equal-evaluate-formula
  (implies (and (set-equalp x y)
                (formulap formula)
                (assignmentp x)
                (assignmentp y))
           (equal (evaluate-formula formula y)
                  (evaluate-formula formula x)))
  :hints (("Goal" :in-theory (disable set-equalp)))) ; want to remove this



;; ===================================================================
;; ===================== SHORTEN-LONG-ASSIGNMENT =====================

(defun shorten-long-assignment (assignment all-literals)
  (declare (xargs :guard (and (literal-listp assignment)
                              (literal-listp all-literals))))
  (union-variables assignment all-literals))


;; =============== ASSIGNMENTP-SHORTEN-LONG-ASSIGNMENT ===============

(encapsulate
 ()

 (local
  (defthm literal-listp-shorten-long-assignment
    (implies (assignmentp assignment)
             (literal-listp (shorten-long-assignment assignment all-literals)))))
 
 (local
  (defthm unique-literalsp-shorten-long-assignment
    (implies (assignmentp x)
             (unique-literalsp (shorten-long-assignment x y)))))
 
 (local
  (defthm no-conflicting-literalsp-shorten-long-assignment
    (implies (assignmentp x)
             (no-conflicting-literalsp (shorten-long-assignment x y)))))

 (defthm assignmentp-shorten-long-assignment
   (implies (assignmentp x)
            (assignmentp (shorten-long-assignment x y)))
   :hints (("Goal"
            :in-theory (enable assignmentp))))
 )


;; ============ SUBSET-VARIABLESP-SHORTEN-LONG-ASSIGNMENT ============

(defthm subsetp-shorten-long-assignment
  (subsetp (shorten-long-assignment x y) x))

(defthm subset-variablesp-shorten-long-assignment
  (subset-variablesp (shorten-long-assignment x y) y))


;; ========= TRUEP-EVALUATE-FORMULA-SHORTEN-LONG-ASSIGNMENT ==========

(defthm truep-evaluate-literal-shorten-long-assignment
  (implies (and (truep (evaluate-literal literal assignment))
                (member literal all-literals))
           (truep (evaluate-literal literal (shorten-long-assignment
                                             assignment
                                             all-literals)))))

(defthm truep-evaluate-clause-shorten-long-assignment
  (implies (and (truep (evaluate-clause clause assignment))
                (subsetp clause all-literals))
           (truep (evaluate-clause clause (shorten-long-assignment
                                           assignment
                                           all-literals)))))


(defthm subsetp-list-truep-evaluate-formula-shorten-long-assignment
  (implies (and (truep (evaluate-formula formula assignment))
                (subsetp-list formula all-literals))
           (truep (evaluate-formula formula
                                    (shorten-long-assignment
                                     assignment
                                     all-literals))))
  :hints (("Goal"
           :in-theory (disable shorten-long-assignment))))

(defthm truep-evaluate-formula-shorten-long-assignment
  (implies (truep (evaluate-formula formula assignment))
           (truep (evaluate-formula formula
                                    (shorten-long-assignment
                                     assignment
                                     (all-literals formula)))))
  :hints (("Goal" 
           :in-theory (disable shorten-long-assignment))))


;; ============ STRONG-ASSIGNMENT-SHORTEN-LONG-ASSIGNMENT ============

(defthm strong-assignment-shorten-long-assignment
  (implies (and (assignmentp assignment)
                (truep (evaluate-formula formula assignment)))
           (and (assignmentp (shorten-long-assignment
                              assignment
                              (all-literals formula)))
                (truep (evaluate-formula formula 
                                         (shorten-long-assignment
                                          assignment
                                          (all-literals formula))))
                (subset-variablesp (shorten-long-assignment
                                    assignment
                                    (all-literals formula))
                                   (all-literals formula))))
  :hints (("Goal"
           :in-theory (disable shorten-long-assignment))))
                 

;; ===================================================================
;; ===================== EXTEND-SHORT-ASSIGNMENT =====================

; consider switching append order?
(defun extend-short-assignment (assignment all-literals)
  (declare (xargs :guard (and (literal-listp assignment)
                              (literal-listp all-literals))))
  (append (set-difference-variables (remove-conflicting-literals all-literals)
                                    assignment)
          assignment))


;; =============== ASSIGNMENTP-EXTEND-SHORT-ASSIGNMENT ===============

(encapsulate
 ()
 
 (local
  (defthm literal-listp-extend-short-assignment
    (implies (and (assignmentp assignment)
                  (literal-listp all-literals))
             (literal-listp (extend-short-assignment assignment
                                                     all-literals)))))

 (local
  (defthm unique-literalsp-extend-short-assignment
    (implies (and (assignmentp assignment)
                  (unique-literalsp all-literals))
             (unique-literalsp (extend-short-assignment assignment
                                                        all-literals)))))

 (local
  (defthm no-conflicting-literalsp-extend-short-assignment
    (implies (assignmentp assignment)
             (no-conflicting-literalsp (extend-short-assignment
                                        assignment
                                        all-literals)))))

 (defthm assignmentp-extend-short-assignment
   (implies (and (assignmentp assignment)
                 (literal-listp all-literals)
                 (unique-literalsp all-literals))
            (assignmentp (extend-short-assignment assignment all-literals))))
 )


;; ============ SUBSET-VARIABLESP-EXTEND-SHORT-ASSIGNMENT ============

(defthm subset-variablesp-extend-short-assignment
  (implies (literal-listp all-literals)
           (subset-variablesp all-literals
                              (extend-short-assignment assignment
                                                       all-literals))))       
       
(defthm subset-variablesp-extend-short-assignment2
  (implies (subset-variablesp assignment all-literals)
           (subset-variablesp (extend-short-assignment assignment
                                                       all-literals)
                              all-literals)))


;; ========= TRUEP-EVALUATE-FORMULA-EXTEND-SHORT-ASSIGNMENT ==========

(defthm truep-evaluate-literal-extend-long-assignment
  (implies (and (truep (evaluate-literal literal assignment))
                (member literal all-literals))
           (truep (evaluate-literal literal (extend-short-assignment
                                             assignment
                                             all-literals)))))

(defthm truep-evaluate-clause-extend-short-assignment
  (implies (and (truep (evaluate-clause clause assignment))
                (subsetp clause all-literals))
           (truep (evaluate-clause clause (extend-short-assignment
                                           assignment
                                           all-literals)))))

(defthm subsetp-list-truep-evaluate-formula-extend-short-assignment
  (implies (and (truep (evaluate-formula formula assignment))
                (subsetp-list formula all-literals))
           (truep (evaluate-formula formula (extend-short-assignment
                                             assignment
                                             all-literals))))
  :hints (("Goal"
           :in-theory (disable extend-short-assignment))))

(defthm truep-evaluate-formula-extend-short-assignment
  (implies (and (assignmentp assignment)
                (truep (evaluate-formula formula assignment)))
           (truep (evaluate-formula formula (extend-short-assignment
                                             assignment
                                             (all-literals formula)))))
  :hints (("Goal"
           :in-theory (disable extend-short-assignment))))


;; ============ STRONG-ASSIGNMENT-EXTEND-SHORT-ASSIGNMENT ============

(defthm strong-assignment-extend-short-assignment
  (implies (and (formulap formula)
                (assignmentp assignment)
                (truep (evaluate-formula formula assignment)))
           (and (assignmentp (extend-short-assignment
                              assignment
                              (all-literals formula)))
                (truep (evaluate-formula formula (extend-short-assignment
                                                  assignment
                                                  (all-literals formula))))
                (subset-variablesp (all-literals formula)
                                   (extend-short-assignment
                                    assignment
                                    (all-literals formula)))))
  :hints (("Goal"
           :in-theory (disable extend-short-assignment))))


;; ===================================================================
;; ============== SATISFYING-IMPLIES-STRONG-SATISFYING ===============

(defun-sk exists-strong-satisfying-assignment (formula)
  (exists assignment (and (assignmentp assignment)
                          (truep (evaluate-formula formula assignment))
                          (set-equal-variablesp (all-literals formula)
                                                assignment))))
(in-theory (disable exists-strong-satisfying-assignment
                    exists-strong-satisfying-assignment-suff))


(defthm satisfying-assignment-implies-exists-strong-satisfying-assignment
  (implies (and (formulap formula)
                (assignmentp assignment)
                (truep (evaluate-formula formula assignment)))
           (exists-strong-satisfying-assignment formula))
  :hints (("Goal"
           :in-theory (disable extend-short-assignment
                               shorten-long-assignment
                               )
           :use ((:instance exists-strong-satisfying-assignment-suff
                            (assignment (extend-short-assignment
                                         (shorten-long-assignment
                                          assignment
                                          (all-literals formula))
                                         (all-literals formula))))))))
