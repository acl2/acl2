(in-package "ACL2")
(include-book "partial-clock-functions")

(verify-guards omega)

; note that this is admitted as an executable function. this is possible because:
; 1) we never change the original copy of mstate, so it fits with the rules of stobjs
; 2) acl2 allows functions that call partial functions to be declared executable.
; but because we do call a partial function inside steps-to-cutpoint-exec, any attempt
; to actually execute it result in an error;
(defun steps-to-cutpoint-exec (mstate)
  (declare (xargs :stobjs (mstate)))
  (let ((steps (steps-to-cutpoint-tail 0 (copy-from-mstate mstate))))
    (if (and (natp steps)        ;the number of steps is a natural number.
             (with-copy-of-stobj ;running a copy of our machine state forward steps steps
	      mstate             ;gives us a cutpoint.
	      (mv-let (result mstate)
		      (let ((mstate (run steps mstate)))
			(mv (at-cutpoint mstate) mstate))
		      result)))
	steps
      (omega))))

(defthm o-p-steps-to-cutpoint-exec
  (o-p (steps-to-cutpoint-exec mstate))
  :hints (("goal" :in-theory (enable steps-to-cutpoint-exec))))

(defthm steps-to-cutpoint-exec-steps-to-cutpoint
 (implies (mstatep mstate)
	  (equal (steps-to-cutpoint-exec mstate)
		 (steps-to-cutpoint mstate)))
 :hints (("goal" :in-theory (enable steps-to-cutpoint))))

(in-theory (disable steps-to-cutpoint-exec))

(defun dummy-mstate (mstate)
  (declare (xargs :stobjs (mstate)))
  (update-progc -1 mstate))

(defun next-cutpoint-exec (mstate)
  (declare (xargs :stobjs (mstate)
                  :measure (steps-to-cutpoint-exec mstate)
                  :guard (and (mstatep mstate)
                              (natp (steps-to-cutpoint-exec mstate)))))
  (if (mbt (and (mstatep mstate)
		(natp (steps-to-cutpoint-exec mstate))))
      (if (at-cutpoint mstate)
	  mstate
	(let ((mstate (next mstate)))
	  (next-cutpoint-exec mstate)))
    (dummy-mstate mstate)))


; (defexec next-cutpoint-exec (mstate)
;   (declare (xargs :stobjs (mstate)
;                   :measure (steps-to-cutpoint-exec mstate)
;                   :guard (and (mstatep mstate)
;                               (natp (steps-to-cutpoint-exec mstate))))
; 	   (exec-xargs :default-value (dummy-mstate mstate)))
; (mbe :exec (if (at-cutpoint mstate)
;                  mstate
;                (let ((mstate (next mstate)))
;                  (next-cutpoint-exec mstate)))
;        :logic (cond ((at-cutpoint mstate) mstate)
;                     ((or (not (natp (steps-to-cutpoint-exec mstate)))
;                          (not (mstatep mstate)))
;                      (dummy-mstate mstate))
;                     (t (let ((mstate (next mstate)))
;                          (next-cutpoint-exec mstate))))))

(defthm next-cutpoint-exec-cutpoint-exec
 (implies (and (mstatep mstate)
	       (natp (steps-to-cutpoint-exec mstate)))
	  (equal (next-cutpoint-exec mstate)
		 (next-cutpoint mstate)))
 :hints (("goal" :in-theory (e/d (next-cutpoint run)
				 (next-cutpoint-intro-next)))))

(in-theory (disable next-cutpoint-exec))

(defun cutpoint-to-cutpoint-exec (mstate)
  (declare (xargs :stobjs (mstate)
		  :guard (and (at-cutpoint mstate)
			      (not (at-exitpoint mstate)))))
  (let ((mstate (next mstate)))
    (next-cutpoint-exec mstate)))

(defthm cutpoint-to-cutpoint-exec-cutpoint-to-cutpoint
 (implies (and (mstatep mstate)
	       (at-cutpoint mstate)
	       (not (at-exitpoint mstate)))
	  (equal (cutpoint-to-cutpoint-exec mstate)
		 (cutpoint-to-cutpoint mstate)))
 :hints (("goal" :in-theory (enable cutpoint-to-cutpoint))))

(in-theory (disable cutpoint-to-cutpoint-exec))

(defun fast-cutpoint-to-cutpoint (mstate)
  (declare (xargs :stobjs (mstate)
                  :measure (cutpoint-measure mstate)
                  :guard (at-cutpoint mstate)))
  (if (mbt (at-cutpoint mstate))
      (if (at-exitpoint mstate)
          mstate
        (let ((mstate (cutpoint-to-cutpoint-exec mstate)))
          (fast-cutpoint-to-cutpoint mstate)))
    (dummy-mstate mstate)))

#|==================================================================|#