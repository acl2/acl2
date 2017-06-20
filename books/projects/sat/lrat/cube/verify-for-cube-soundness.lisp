; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.  Here we complete the proof for (2).

(in-package "LRAT")

(include-book "cube")

(include-book "verify-for-cube-soundness-lemmas")

(encapsulate
  ()
  (local (include-book "verify-for-cube-soundness-main"))
  (defthm verify-for-cube-soundness-main
    (mv-let (ign formula/clause state)
      (verify-for-cube cnf-file clrat-file cube-file chunk-size debug ctx state)
      (declare (ignore ign state)) ; not mentioned below
      (implies formula/clause      ; no error
               (let ((formula (car formula/clause))
                     (clause (cdr formula/clause)))
                 (and (clausep clause)
                      (ordered-formula-p formula)
                      (not (satisfiable (extend-formula-with-cube
                                         formula
; Clauses and cubes have the same format, so the following isn't really a type
; error.
                                         (negate-cube clause))))))))
    :rule-classes nil))

(defun falsify-clause (clause assignment)
  (cond ((atom clause) assignment)
        ((equal (evaluate-literal (car clause) assignment) 0)
         (falsify-clause (cdr clause)
                         (cons (negate (car clause)) assignment)))
        (t (falsify-clause (cdr clause) assignment))))

(defun cube-to-formula (cube next-index)

; This variant of extend-formula-with-cube1 is useful for reasoning, below.

  (cond ((endp cube) nil)
        (t (acons next-index
                  (list (car cube))
                  (cube-to-formula
                   (cdr cube)
                   (1+ next-index))))))

(defthm cube-soundness-2
  (implies
   (and (solution-p assignment formula)
        (ordered-formula-p formula)
        (clausep clause)
        (not (equal (evaluate-clause clause assignment)
                    t)))
   (satisfiable (extend-formula-with-cube formula (negate-cube clause))))
  :hints (("Goal"
           :in-theory (disable satisfiable-suff)
           :use
           ((:instance
             satisfiable-suff
             (assignment (falsify-clause clause assignment))
             (formula (extend-formula-with-cube formula
                                                (negate-cube clause))))))))

(defthm verify-for-cube-soundness
  (mv-let (ign formula/clause state)
    (verify-for-cube cnf-file clrat-file cube-file chunk-size debug ctx state)
    (declare (ignore ign state)) ; not mentioned below
    (implies formula/clause ; no error
             (let ((formula (car formula/clause))
                   (clause (cdr formula/clause)))
               (implies (solution-p assignment formula)
                        (equal (evaluate-clause clause assignment)
                               t)))))
  :hints (("Goal"
           :in-theory (disable verify-for-cube solution-p evaluate-clause)
           :use verify-for-cube-soundness-main)))
