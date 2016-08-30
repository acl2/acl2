(in-package "PROOF-CHECKER-ITP13")

(include-book "literal")
(include-book "unique")
(include-book "sets")
(include-book "clause")

;; ===================================================================
;; ========================== ALL-LITERALS ===========================

(defun all-literals (formula)
  (declare (xargs :guard (formulap formula)))
  (remove-duplicate-literals (flatten-formula formula)))


(defthm literal-listp-all-literals
  (implies (formulap formula)
           (literal-listp (all-literals formula))))

(defthm unique-literalsp-all-literals
  (implies (formulap formula)
           (unique-literalsp (all-literals formula))))

(defthm member-append
  (iff (member e (append x y))
       (or (member e x)
           (member e y))))

; this rule is not firing because of free variable
(defthm member-all-literals
  (implies (and (member literal clause)
                (member clause formula))
           (member literal (all-literals formula))))

(defthm subsetp-all-literals
  (implies (member clause formula)
           (subsetp clause (all-literals formula))))

(defthm subsetp-list-all-literals
  (subsetp-list formula (all-literals formula)))


(in-theory (disable all-literals))