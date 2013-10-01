(in-package "ACL2")

;; This book contains the top definitions and soundness theorems for
;; the refutation and proof procedures.
;;
;; The eight components of the refutation procedure:

(include-book "nnf")            ; nnf
(include-book "rename-top")     ; rename-all
(include-book "skolem-top"  )   ; skolemize
(include-book "cnf")            ; cnf
(include-book "right-assoc")    ; ANDs and ORs
(include-book "pull-top")       ; pull-quants
(include-book "derive")         ; refute-n-check
(include-book "simplify")       ; simp-tf

;;-----------------------
;; Function refutation-attempt composes all of the operations.
;;
;; Verifying the guard of refutation-attempt is important and nontrivial,
;; because each operation expects its input to be in a particular form.

(defun refutation-attempt (f)
  (declare (xargs :guard (and (wff f) (not (free-vars f)))))
  (simp-tf
   (refute-n-check
    (right-assoc
     (cnf
      (pull-quants
       (skolemize
	(rename-all
	 (nnf f)))))))))

;; Soundness of refutation-attempt.
;; Note that we skolem-extend the interpretation for the initial
;; part of the refutation-attempt.

(defthm refutation-attempt-fsound
  (equal (feval (refutation-attempt f)
		(skolemize-extend (rename-all (nnf f)) i))
	 (feval f i))
  :rule-classes nil)

(in-theory (disable refutation-attempt))

;; If the refutation attempt gives 'false, we have a refutation.
;; This is a top function, so check the guard.

(defun refuted (f)
  (declare (xargs :guard (and (wff f) (not (free-vars f)))))
  (if (not (and (wff f) (not (free-vars f))))
      nil
    (equal (refutation-attempt f) 'false)))

;; A refuted formula is false in all interpretations.

(defthm refutation-is-fsound  ;; Top Theorem #1
  (implies (refuted f)
	   (and (wff f)
		(not (free-vars f))
		(not (feval f i))))
  :hints (("Goal"
	   :use refutation-attempt-fsound))
  :rule-classes nil)

(in-theory (disable refuted))

;; Now, state it positively.  That is, if we refute the negation of
;; a formula f, then f is true in all interpretations.
;; This is a top function, so check the guard.

(defun proved (f)
  (declare (xargs :guard (and (wff f) (not (free-vars f)))))
  (if (not (and (wff f) (not (free-vars f))))
      nil
    (refuted (list 'not f))))

;; The main event.  A proved formula is true in all interpretations.

(defthm proof-is-fsound  ;; Top Theorem #2
  (implies (proved f)
	   (and (wff f)
		(not (free-vars f))
		(feval f i)))
  :hints (("Goal"
	   :use ((:instance refutation-is-fsound (f (list 'not f))))))
  :rule-classes nil)

(in-theory (disable proved))

