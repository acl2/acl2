(in-package "ACL2")

;; This book contains the top definitions and soundness theorems for
;; the model and countermodel procedures.  This book is analogous
;; to a combination of the refute-n-check and prover books for the
;; refutation procedure, but it is much simpler, because the soundness
;; proof here is trivial.

(include-book "nnf")            ; nnf
(include-book "rename-top")     ; rename-all
(include-book "skolem-top")     ; skolemize
(include-book "cnf")            ; cnf
(include-book "pull-top")       ; pull-quants

(include-book "derive")

(defstub external-modeler (clauses) t)

;; Function model-attempt is analogous to a combination of
;; refute-n-check and refutation-attempt.  We compose all of the
;; preprocessing steps, build an initial proof object, and
;; call external-modeler, and check the result.

(defun model-attempt (f)
  (declare (xargs :guard (and (wff f) (not (free-vars f)))))
  (if (not (and (wff f) (not (free-vars f))))
      nil
    (let* ((preprocessed
            (cnf
             (pull-quants (skolemize (rename-all (nnf f))))))
           (mace-result
            (external-modeler
             (assign-ids-to-prf
              (initial-proof
               (remove-leading-alls preprocessed)) 1))))
      (if (feval f mace-result)
          mace-result
        nil))))

;; This "soundness" proof is really trivial, because model-attempt
;; checks MACE's answer by calling feval.

(defthm model-attempt-fsound  ;; Top Theorem #3
  (implies (model-attempt f)
	   (and (wff f)
		(not (free-vars f))
		(feval f (model-attempt f)))))

(in-theory (disable model-attempt))

;; Now state it positively.  That is, if we find a model of the negation
;; of a formula, then we have a countermodel of the formula.
;; This is a top function, so check the guard.

(defun countermodel-attempt (f)
  (declare (xargs :guard (and (wff f) (not (free-vars f)))))
  (if (not (and (wff f) (not (free-vars f))))
      nil
    (model-attempt (list 'not f))))

(defthm countermodel-attempt-fsound  ;; Top Theorem #4
  (implies (countermodel-attempt f)
	   (and (wff f)
		(not (free-vars f))
		(not (feval f (countermodel-attempt f)))))
  :hints (("Goal"
           :in-theory (enable model-attempt))))

(in-theory (disable countermodel-attempt))

