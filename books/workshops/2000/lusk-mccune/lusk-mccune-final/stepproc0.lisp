(in-package "ACL2")

(include-book "mstate")

(in-theory (enable hpidp pidp))

(defun pids-in-use (host pss)
  (declare (xargs :guard (and (hostp host)
			      (pstate-listp pss))))
  (cond ((atom pss) nil)
	((equal host (first (caar pss))) (cons (second (caar pss))
					       (pids-in-use host (cdr pss))))
	(t (pids-in-use host (cdr pss)))))

(defun newpid (host pss)
  (declare (xargs :guard (and (hostp host)
			      (pstate-listp pss))))
  (gen-pos-integer (pids-in-use host pss)))

(defthm newpid-is-pid
  (pidp (newpid host pss)))

(in-theory (disable hpidp pidp))

;;======================================================================
;; When a process forks, we copy all of the connections involving
;; the parent process, updating the hpid to the hpid of the child.

(defun fork-connections (old-hpid new-hpid css)
  (declare (xargs :guard (and (hpidp old-hpid)
			      (hpidp new-hpid)
			      (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal old-hpid (first (caar css)))
	      (equal old-hpid (third (caar css))))
	 (list* (cons (list new-hpid (second (caar css))
			    new-hpid (fourth (caar css)))
		      (cdar css))
		(car css)
		(fork-connections old-hpid new-hpid (cdr css))))
	((equal old-hpid (first (caar css)))
	 (list* (cons (list new-hpid (second (caar css))
			    (third (caar css)) (fourth (caar css)))
		      (cdar css))
		(car css)
		(fork-connections old-hpid new-hpid (cdr css))))
	((equal old-hpid (third (caar css)))
	 (list* (cons (list (first (caar css)) (second (caar css))
			    new-hpid (fourth (caar css)))
		      (cdar css))
		(car css)
		(fork-connections old-hpid new-hpid (cdr css))))
	(t (cons (car css)
		 (fork-connections old-hpid new-hpid (cdr css))))))

;; For example,

#|
(fork-connections '(lutra 320)
		  '(lutra 321)
		  '(
		    (((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2))
		    (((gyro 440) 6 (lutra 320) 5) ('m3 'm4) ('m1 'm2))
		    (((lutra 320) 7 (lutra 320) 8) ('m3 'm4) ('m1 'm2))
		    ))
|#

(defthm fork-connections-preserves-cstate-listp
  (implies (and (cstate-listp css)
		(hpidp new-hpid))
	   (cstate-listp (fork-connections old-hpid new-hpid css))))

;;======================================================================

(defun exec-fork (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'fork)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))
  (let ((newpid (newpid (first (car ps)) (pstates ms))))

    (make-mstate
     (cons (make-pstate (list (first (car ps)) newpid);; child process
			(code ps)
			(+ 1 (cc ps))
			(xstack ps)
			(memory ps))
	   (update-pstate (car ps)
			  (make-pstate (car ps);; parent process
				       (code ps)
				       (+ 1 (cc ps))
				       (xstack ps)
				       (asgn (second stmt)
					     newpid
					     (memory ps)))
			  (pstates ms)))
     (fork-connections (car ps) (list (first (car ps)) newpid) (cstates ms))
     (lstates ms)
     (programs ms))))

;; For example,

#|
(exec-fork '(fork fpid)
	   '((lutra 320) ((asgn z 6)) 13 nil ((x . 4) (y . 6)))
	   '(
	     (;; pstates:
	      ((lutra 320) ((asgn z 6)) 13 nil ((x . 4) (y . 6)))
	      ((gyro  440) ((procedure handle)) 14 nil nil)
	      )

	     (;; cstates:
	      (((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2))
	      )
	     (;; lstates:
	      (((gyro   440) 15) 8585 nil)
	      (((lutra  320) 14) 7483 (((cosmo 354) 16)))
	      (((donner 320) 17) 3535 (((fire  444) 18)))
	      )
	     nil
	     ))
|#

(local (in-theory (enable statementp)))

(verify-guards exec-fork
  :hints (("Goal"
           :in-theory (enable hpidp pidp hostp))))

(defthm exec-fork-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'fork)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-fork stmt ps ms)))
  :hints (("Goal"
           :in-theory (enable hpidp pidp hostp))))

;;===================================================================

(defun exec-exec (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'exec)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))
  (let ((program (assoc-equal (second stmt) (programs ms))))

    (if program

	;; all is well---the program exists

	(make-mstate (update-pstate (car ps)
				    (make-pstate (car ps)
						 (second program)
						 1
						 nil
						 (third stmt))
				    (pstates ms))
		     (cstates ms)
		     (lstates ms)
		     (programs ms))
      ;; error

      (make-mstate (update-pstate (car ps)
				  (make-pstate (car ps)
					       (code ps)
					       0
					       (xstack ps)
					       (asgn 'error
						     ''bad-prog-name-in-exec
						     (memory ps)))
				  (pstates ms))
		   (cstates ms)
		   (lstates ms)
		   (programs ms)))))

(defthm program-listp-assoc-properties
  (implies (and (program-listp pgms)
		(assoc-equal name pgms))
	   (and (consp (assoc-equal name pgms))
		(consp (cdr (assoc-equal name pgms)))
		(codep (second (assoc-equal name pgms))))))

(verify-guards exec-exec
	       :otf-flg t)

(defthm exec-exec-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'exec)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-exec stmt ps ms))))

;;===================================================================

(defun exec-rsh (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'rsh)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))
  (let ((program (assoc-equal (third stmt) (programs ms))))
    (if program

	;; All is well---the program exists.
	;; Cons the new process onto the updated process list.

	(make-mstate

	 (cons (make-pstate (list (second stmt)
				  (newpid (caar ps) (pstates ms)))
			    (second program)
			    1
			    nil
			    (fourth stmt))
	       (update-pstate (car ps)
			      (make-pstate (car ps)
					   (code ps)
					   (+ 1 (cc ps))
					   (xstack ps)
					   (memory ps))
			      (pstates ms)))
	 (cstates ms)
	 (lstates ms)
	 (programs ms))
      ;; error

      (make-mstate (update-pstate (car ps)
				  (make-pstate (car ps)
					       (code ps)
					       0
					       (xstack ps)
					       (asgn 'error
						     ''bad-prog-name-in-rsh
						     (memory ps)))
				  (pstates ms))
		   (cstates ms)
		   (lstates ms)
		   (programs ms)))))

(defthm gen-pos-integer-pidp
  (pidp (gen-pos-integer x))
  :hints (("Goal"
           :in-theory (enable pidp))))

(verify-guards exec-rsh
  :hints (("Goal"
           :in-theory (enable hpidp))))

(defthm exec-rsh-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'rsh)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-rsh stmt ps ms)))
  :hints (("Goal"
           :in-theory (enable hpidp))))

