(in-package "PROOF-CHECKER-ITP13")

(include-book "literal")
(include-book "unique")


;; ===================================================================
;; ====================== ASSIGNMENT PREDICATE =======================

(defun assignmentp (x)
  (declare (xargs :guard t))
  (and (literal-listp x)
       (unique-literalsp x)
       (no-conflicting-literalsp x)))


(defthm assignmentp-conjunction
  (implies (assignmentp assignment)
           (and (literal-listp assignment)
                (unique-literalsp assignment)
                (no-conflicting-literalsp assignment))))

(defthm assignmentp-true-listp
  (implies (assignmentp assignment)
           (true-listp assignment)))

(defthm assignmentp-literalp-member
  (implies (and (assignmentp assignment)
                (member e assignment))
           (literalp e)))

(defthm assignmentp-cdr
  (implies (and (assignmentp assignment)
                (consp assignment))
           (assignmentp (cdr assignment))))

(defthm assignmentp-cons
  (implies (and (literalp e)
                (not (member e assignment))
                (not (member (negate e) assignment)))
           (equal (assignmentp (cons e assignment))
                  (assignmentp assignment))))



(in-theory (disable assignmentp))
