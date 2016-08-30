(in-package "PROOF-CHECKER-ITP13")

(include-book "literal")
(include-book "unique")

;; ===================================================================
;; ============================= CLAUSE ==============================

(defun clausep (clause)
  (declare (xargs :guard t))
  (and (literal-listp clause)
       (unique-literalsp clause)
       (no-conflicting-literalsp clause)))

(defthm clausep-true-listp
  (implies (clausep clause)
           (true-listp clause)))

(defthm clausep-member
  (implies (and (clausep clause)
                (member e clause))
           (literalp e)))

(defthm clausep-cdr
  (implies (and (clausep clause)
                (consp clause))
           (clausep (cdr clause))))


;; ===================================================================
;; ============================= FORMULA =============================

(defun formulap (formula)
  (declare (xargs :guard t))
  (if (atom formula)
      (null formula)
    (and (clausep (car formula))
         (formulap (cdr formula)))))


(defthm formulap-true-listp
  (implies (formulap formula)
           (true-listp formula)))

(defthm formulap-member
  (implies (and (formulap formula)
                (member e formula))
           (clausep e)))

(defthm formulap-cdr
  (implies (and (formulap formula)
                (consp formula))
           (formulap (cdr formula))))

(defthm formulap-implies-clausep-car
  (implies (and (formulap formula)
                (consp formula))
           (clausep (car formula))))


;; ===================================================================
;; ========================= FLATTEN-FORMULA =========================

(defun flatten-formula (formula)
  (declare (xargs :guard (formulap formula)))
  (if (atom formula)
      nil
    (append (car formula)
            (flatten-formula (cdr formula)))))

(defthm literal-listp-flatten-formula
  (implies (formulap formula)
           (literal-listp (flatten-formula formula))))
