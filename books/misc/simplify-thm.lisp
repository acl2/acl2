

(in-package "ACL2")

(program)
(set-state-ok t)
(include-book "bash")


(defmacro incat (sym &rest strings)
  `(intern-in-package-of-symbol
    (concatenate 'string
                  . ,strings)
    ,sym))


(defun smpl-clause-to-theorem (clause)
  `(implies (and . ,(dumb-negate-lit-lst (butlast clause 1)))
            ,(car (last clause))))

(defun smpl-clauses-to-theorems (clauses)
  (if (atom clauses)
      nil
    (cons (smpl-clause-to-theorem (car clauses))
          (smpl-clauses-to-theorems (cdr clauses)))))

(defun smpl-to-theorems (term hints state)
  (er-let* ((clauses (simplify-with-prover term hints 'smpl-to-theorems state)))
           (value (smpl-clauses-to-theorems clauses))))


(defun smpl-clauses-to-defthms (namebase n clauses args)
  (if (atom clauses)
      nil
    (cons `(defthm ,(incat namebase (symbol-name namebase) "-"
                           (explode-atom n 10))
             ,(car clauses)
             . ,args)
          (smpl-clauses-to-defthms namebase (1+ n) (cdr clauses) args))))



(defun simplify-thm-fn (namebase form smpl-hints args state)
  (er-let* ((forms (smpl-to-theorems form smpl-hints state)))
           (value (smpl-clauses-to-defthms
                   namebase 0 forms args))))

