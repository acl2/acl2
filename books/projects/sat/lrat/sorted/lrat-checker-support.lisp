; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ./README.

(in-package "LRAT")

(include-book "../stobj-based/lrat-checker")

(defun ordered-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (cond ((endp x) t)
        (t (or (null (cdr x))
               (and (< (abs (car x)) (abs (cadr x)))
                    (ordered-literalsp (cdr x)))))))

(defthm ordered-literalsp-implies-not-member
  (implies (and (consp x)
                (< (abs a) (abs (car x)))
                (ordered-literalsp x))
           (not (member a x))))

(defthm ordered-literalsp-implies-unique-literalsp
  (implies (ordered-literalsp x)
           (unique-literalsp x)))

(defthm ordered-literalsp-implies-not-member-negate
  (implies (and (consp x)
                (< (abs a) (abs (car x)))
                (ordered-literalsp x))
           (not (member (negate a) x))))

(defthm ordered-literalsp-implies-not-conflicting-literalsp
  (implies (ordered-literalsp x)
           (not (conflicting-literalsp x))))

(defun lrat-clausep (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (literal-listp x)
           (not (member (car x) (cdr x)))
           (not (member (negate (car x)) (cdr x)))
           (ordered-literalsp (cdr x)))))

; !! Consider introducing/using ordered versions of clause-max-var,
; formula-max-var, and proof-max-var.

(defun lrat-add-step-p (x)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use (:guard-theorem add-step-p)))))
  (and (weak-add-step-p x)
       (posp (access add-step x :index))
       (lrat-clausep (access add-step x :clause))
       (index-listp (access add-step x :rup-indices))
       (drat-hint-listp (access add-step x :drat-hints))))

(defthm lrat-add-step-p-implies-add-step-p
  (implies (lrat-add-step-p proof)
           (add-step-p proof))
  :rule-classes :forward-chaining)

(defun lrat-proof-entry-p (entry)
  (declare (xargs :guard t))
  (cond ((and (consp entry)
              (eq (car entry) t)) ; deletion
         (index-listp (cdr entry)))
        (t (lrat-add-step-p entry))))

(defthm lrat-proof-entry-p-implies-proof-entry-p
  (implies (lrat-proof-entry-p proof)
           (proof-entry-p proof))
  :rule-classes :forward-chaining)

(defun lrat-proofp (proof)
  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (lrat-proof-entry-p (car proof))
         (lrat-proofp (cdr proof)))))

(defthm lrat-proofp-implies-proofp
  (implies (lrat-proofp proof)
           (proofp proof))
  :rule-classes :forward-chaining)

(defun lrat-valid-proofp$ (formula proof a$)
  (declare (xargs :stobjs a$ ; not necessarily satisfying a$p
                  :guard (formula-p formula)
                  :guard-hints (("Goal" :use (:guard-theorem valid-proofp$)))))
  (let* ((formula (make-fast-alist formula))
         (max-var (and (lrat-proofp proof)
                       (proof-max-var proof
                                      (formula-max-var formula 0)))))
    (cond ((varp max-var)
           (let ((a$ (initialize-a$ max-var a$)))
             (mv-let (v a$)
               (verify-proof$ formula proof a$)
               (mv v
                   (proof-contradiction-p proof)
                   a$))))
          (t (mv nil nil a$)))))

(defun lrat-valid-proofp$-top (formula proof incomplete-okp)
  (declare (xargs :guard t))
  (and (formula-p formula)
       (with-local-stobj a$
         (mv-let (v c a$)
           (lrat-valid-proofp$ formula proof a$)
           (and v
                (or incomplete-okp
                    c))))))

(in-theory (disable verify-proof$))

(encapsulate
  ()
  (local (defthm lrat-valid-proofp$-is-valid-proofp$
           (implies (car (lrat-valid-proofp$ formula proof a$))
                    (equal (valid-proofp$ formula proof a$)
                           (lrat-valid-proofp$ formula proof a$)))))

  (in-theory (disable lrat-valid-proofp$ valid-proofp$))

  (defthm lrat-valid-proofp$-top-implies-valid-proofp$-top
    (implies (lrat-valid-proofp$-top formula proof incomplete-okp)
             (valid-proofp$-top formula proof incomplete-okp))
    :rule-classes :forward-chaining))

(defun lrat-refutation-p$ (proof formula)
  (declare (xargs :guard t))
  (lrat-valid-proofp$-top formula proof nil))

(in-theory (disable valid-proofp$-top lrat-valid-proofp$-top))

(defthm lrat-refutation-p$-implies-refutation-p$
  (implies (lrat-refutation-p$ proof formula)
           (refutation-p$ proof formula))
  :rule-classes :forward-chaining)

(in-theory (disable satisfiable formula-p lrat-refutation-p$))

(local (include-book "../stobj-based/soundness"))

(defthm main-theorem
  (implies (and (formula-p formula)
                (lrat-refutation-p$ proof formula))
           (not (satisfiable formula))))
