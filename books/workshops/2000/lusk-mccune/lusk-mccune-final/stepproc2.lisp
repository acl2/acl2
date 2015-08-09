(in-package "ACL2")

(include-book "setup")

(local (in-theory (enable statementp)))

;; The following are useful when disabling mstatep

(defthm mstate-pstate-listp
  (implies (mstatep ms)
	   (pstate-listp (first ms))))

(defthm mstate-cstate-listp
  (implies (mstatep ms)
	   (cstate-listp (second ms))))

(defthm mstate-lstate-listp
  (implies (mstatep ms)
	   (lstate-listp (third ms))))

(defthm mstate-program-listp
  (implies (mstatep ms)
	   (program-listp (fourth ms))))

;;--------------------------------
;; exec-setup-listener

;; [Jared] adding this because the defun below failed when it was added to ACL2.
(local (in-theory (disable FOLD-CONSTS-IN-+)))

(defun exec-setup-listener (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'setup-listener)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))

  (let ((port (evl2 (second stmt) (memory ps))))
    (if (portp port)
	(let* ((x (setup-listener (car ps) port ms))
	       (lfd (first x))
	       (ms1 (second x)))

	  (make-mstate
	   (update-pstate (car ps)
			  (make-pstate (car ps)
				       (code ps)
				       (+ 1 (cc ps))
				       (xstack ps)
				       (asgn (third stmt)
					     lfd
					     (memory ps)))
			  (pstates ms1))
	   (cstates ms1)
	   (lstates ms1)
	   (programs ms)))

      (make-mstate
       (update-pstate (car ps)
		      (make-pstate (car ps)
				   (code ps)
				   0
				   (xstack ps)
				   (asgn 'error
					 ''bad-port-in-setup-listener
					 (memory ps)))
		      (pstates ms))
       (cstates ms)
       (lstates ms)
       (programs ms))
      )))

(defthm evaluated-expressionp-car-setup-listener
  (evaluated-expressionp (car (setup-listener hpid port ms))))

(verify-guards exec-setup-listener
	       :hints (("Goal"
			:in-theory (disable setup-listener)))
	       :otf-flg t)

(defthm exec-setup-listener-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'setup-listener)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-setup-listener stmt ps ms)))
  :hints (("Goal"
	   :in-theory (disable setup-listener))))

;;------------------------------------

(defthm request-listp-is-alistp
  (implies (request-listp rq)
	   (alistp rq))
  :hints (("Goal"
           :in-theory (enable hpid-fdp)))
  :rule-classes :forward-chaining)

(defthm find-ls-alistp
  (implies (and (lstate-listp lss)
		(consp (find-ls dest-host dest-port lss)))
	   (alistp (caddr (find-ls dest-host dest-port lss)))))

(defun connection-status (my-hpid dest-host dest-port ms)
  (declare (xargs :guard (and (hpidp my-hpid)
			      (hostp dest-host)
			      (portp dest-port)
			      (mstatep ms))))
  (let ((ls (find-ls dest-host dest-port (lstates ms))))
    (cond ((atom ls) 'not-listening)
	  ((assoc-equal my-hpid (requestq ls)) 'pending)
	  (t 'ready))))

(defun unkwote (x)
  (declare (xargs :guard t))
  (if (and (equal (len x) 2)
	   (equal (first x) 'quote))
      (second x)
    x))

(in-theory (disable unkwote))

;;------------------------------------------------------------------
;; exec-connect
;;
;; This executes (or continues to execute) a statement like
;; (FDASGN FD (CONNECT remote-host remote-port)).
;;
;; If the remote-host is not listening on the remote-port, we set
;; the FD to -1 and bump the PC (connection refused).
;; If we have already issued a connect-request, and the remote host
;; has not accepted it, we do nothing.
;; Otherwise, we issue a connect-request.
;;
;; Note that the PC is bumped by the accepting process when the connection
;; is accepted.  Perhaps this bit of implicit handshaking should be rethought.

(defun exec-connect (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'connect)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))

  (let ((my-hpid (car ps))
	(dest-host (unkwote (evl2 (second stmt) (memory ps))))
	(dest-port (evl2 (third stmt) (memory ps))))
    (if (or (not (hostp dest-host))
	    (not (portp dest-port)))
	(make-mstate
	 (update-pstate (car ps)
			(make-pstate (car ps)
				     (code ps)
				     0
				     (xstack ps)
				     (asgn 'error
					   ''bad-host-or-port-in-connect
					   (memory ps)))
			(pstates ms))
	 (cstates ms)
	 (lstates ms)
	 (programs ms))

      (let ((status (connection-status my-hpid dest-host dest-port ms)))
	(case status
	      (pending ms)  ;; do nothing

	      (not-listening (make-mstate
			      (update-pstate (car ps)
					     (make-pstate (car ps)
							  (code ps)
							  (+ 1 (cc ps))
							  (xstack ps)
							  (asgn (fourth stmt)
								-1
								(memory ps)))
					     (pstates ms))
			      (cstates ms)
			      (lstates ms)
			      (programs ms)))

	      (ready (let* ((x (connect my-hpid dest-host dest-port ms))
			    (fd (first x))
			    (ms1 (second x)))

		       (make-mstate
			(update-pstate (car ps)
				       (make-pstate (car ps)
						    (code ps)
						    (cc ps)
						    (xstack ps)
						    (asgn (fourth stmt)
							  fd
							  (memory ps)))
				       (pstates ms1))
			(cstates ms1)
			(lstates ms1)
			(programs ms))))

	      (otherwise ms)
	      )))))

(defthm evaluated-expressionp-car-connect
  (evaluated-expressionp (car (connect hpid host port ms))))

(defthm conp-cdr-connect
  (consp (cdr (connect hpid host port ms))))

(defthm cdr-connect
  (cdr (connect hpid host port ms)))

(verify-guards exec-connect
	       :hints (("Goal"
			:in-theory (disable connect mstatep))))

(defthm exec-connect-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'connect)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-connect stmt ps ms)))
  :hints (("Goal"
	   :in-theory (disable connect))))

;;------------------------------------
;; exec-accept
;;
;; This executes a statement like (FDASGN FD (ACCEPT LFD)), where
;; LFD is the listening fd.  When and if we succeed, FD is given
;; the new fd for the conection.  If there are no requests to accept,
;; we do nothing (i.e., we wait).

(defun exec-accept (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'accept)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))

  (let ((lfd (evl2 (second stmt) (memory ps))))
    (if (not (fdp lfd))
	;; The fd is bad, so set pc to 0 and set error variable.
	(make-mstate
	 (update-pstate (car ps)
			(make-pstate (car ps)
				     (code ps)
				     0
				     (xstack ps)
				     (asgn 'error
					   ''bad-fd-in-accept
					   (memory ps)))
			(pstates ms))
	 (cstates ms)
	 (lstates ms)
	 (programs ms))

      ;; The listening FD is ok.  Try to accept a connection.
      (let* ((x (accept (car ps) lfd ms))
	     (fd (first x))
	     (ms1 (second x)))

	(if (equal fd -1)
	    ;; There is nothing to accept, so just wait.
	    ms
	  ;; All is well, so accept, bump our PC, and assign fd.
	  (make-mstate
	   (update-pstate (car ps)
			  (make-pstate (car ps)
				       (code ps)
				       (+ 1 (cc ps))
				       (xstack ps)
				       (asgn (third stmt)
					     fd
					     (memory ps)))
			  (pstates ms1))
	   (cstates ms1)
	   (lstates ms1)
	   (programs ms)))))))

(defthm evaluated-expressionp-car-accept
  (evaluated-expressionp (car (accept hpid fd ms))))

(verify-guards exec-accept
	       :hints (("Goal"
			:in-theory (disable accept))))

(defthm exec-accept-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'accept)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-accept stmt ps ms)))
  :hints (("Goal"
	   :in-theory (disable accept))))
