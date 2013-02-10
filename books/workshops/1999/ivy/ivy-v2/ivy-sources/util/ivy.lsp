;;---------------------------------------------
;; ivy
;;
;;  1. Read a formula (wff or sweet-wff) from a file,
;;  2. unsweeten it if necessary,
;;  3. if it is not closed, use the universal closure,
;;  4. perform an operation (prove, refute, disprove, or model),
;;  5. print a message about the result,
;;  6. for otter operations (prove, refute), return t (success) or nil,
;;     for MACE operations (disprove, model), return a model (success) or nil.
;;
;; Messages are output along the way, and no global variables are used.

(defun ivy (operation filename)

  (progn

    (format t "~%~%We are trying to ~a ~a.~%" operation filename)

    (with-open-file (fp filename) (setq in-form (read fp)))

    (format t "~%The input formula:~%")
    (print in-form)

    (cond ((wff in-form) (setq wff in-form))
	  ((wff (unsweeten in-form))
	   (progn (setq wff (unsweeten in-form))
		  (format t "~%~%Unsweetened formula:~%")
		  (print wff)))
	  (t (error "The formula is not a well formed.")))
    
    (if (free-vars wff)
	(progn (format t "~%~%Formula has free variables:~%")
	       (print (free-vars wff))
	       (setq closed-wff (univ-closure-conj wff))
	       (format t "~%~%Using univ-closure-conj:~%")
	       (print closed-wff)
	       )
      (setq closed-wff wff))

    (finish-output)

    (ecase  ;; causes error if nothing is matched

     operation

     ('prove (setq success (proved closed-wff))
	     (if success
		 (format t "The conjecture has been proved!")
	       (format t "The proof attempt failed.")))

     ('refute (setq success (refuted closed-wff))
	      (if success
		  (format t "The formula has been refuted!")
		(format t "The refutation attempt failed.")))

     ('disprove (setq success (countermodel-attempt closed-wff))
		(if success
		    (format t "The formula has been disproved!")
		  (format t "The countermodel attempt failed.")))

     ('model (setq success (model-attempt closed-wff))
	     (if success
		 (format t "The formula has been modeled!")
	       (format t "The model attempt failed.")))
     )

    ;; Success is  nil       for failure,
    ;;             t         for successful prove or refute operation,
    ;;             a model   for successful disprove or model operation.

    success

    )
  )
