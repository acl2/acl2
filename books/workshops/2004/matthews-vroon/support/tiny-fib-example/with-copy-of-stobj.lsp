(defmacro with-copy-of-stobj (stobj mv-let-form)
  (let ((copy-from-stobj (join-symbols stobj 'copy-from- stobj))
	(copy-to-stobj (join-symbols stobj 'copy-to- stobj)))
    `(let ((stobj (,copy-from-stobj ,stobj)))
       (with-local-stobj
	,stobj
	(mv-let ,(nth 1 mv-let-form)
		(let ((,stobj (,copy-to-stobj stobj ,stobj)))
		  ,(nth 2 mv-let-form))
		,(nth 3 mv-let-form))))))

(defun steps-to-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (let ((steps (steps-to-cutpoint-tail 0 (copy-from-tiny-state tiny-state))))
    (if (and (natp steps) ;the number of steps is a natural number
             (with-copy-of-stobj
	      tiny-state
	      (mv-let (result tiny-state)
		      (let ((tiny-state (run steps tiny-state)))
			(mv (at-cutpoint tiny-state) tiny-state))
		      result)))
	steps
      (omega))))

(defun steps-to-cutpoint (tiny-state)
  (declare (xargs :stobjs (tiny-state)))
  (let ((steps (steps-to-cutpoint-tail 0 (copy-from-tiny-state tiny-state))))
    (if (and (natp steps) ;the number of steps is a natural number
             (let ((ts (copy-from-tiny-state tiny-state))) ;all of this is to see if
               (with-local-stobj                           ;we're at a cutpoint
                tiny-state                                 ;if we run the machine for
                (mv-let (result tiny-state)                ;steps steps
                        (let* ((tiny-state (copy-to-tiny-state ts tiny-state))
                               (tiny-state (run steps tiny-state)))
                          (mv (at-cutpoint tiny-state) tiny-state))
                        result))))
        steps
      (omega))))