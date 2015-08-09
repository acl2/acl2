(in-package "ACL2")

(include-book "mstate")

(defun connection-pairsx (css)
  (declare (xargs :guard (cstate-listp css)))
  (cond ((atom css) nil)
	((null (second (caar css)))
	 (cons (list (third (caar css)) (fourth (caar css)))
	       (connection-pairsx (cdr css))))
	(t (list* (list (first (caar css)) (second (caar css)))
		  (list (third (caar css)) (fourth (caar css)))
		  (connection-pairsx (cdr css))))))

(defun newfd (hpid ms)
  (declare (xargs :guard (and (hpidp hpid)
			      (mstatep ms))
		  :verify-guards nil))
  (gen-natural (fds-in-use hpid (append (connection-pairsx (cstates ms))
					(listening-pairs (lstates ms))))))

(defthm request-listp-connection-pairs
  (implies (cstate-listp css)
	   (request-listp (connection-pairsx css)))
  :hints (("Goal"
           :in-theory (enable hpid-fdp))))

(defthm request-listp-listening-pairs
  (implies (lstate-listp lss)
	   (request-listp (listening-pairs lss))))

(defthm request-listp-append
  (implies (and (request-listp a)
		(request-listp b))
	   (request-listp (append a b))))

(in-theory (enable fdp hpidp hpid-fdp))

(defthm natural-listp-fds-in-use
  (implies (request-listp a)
	   (natural-listp (fds-in-use hpid a))))

(verify-guards newfd)

(defthm newfd-fdp
  (fdp (newfd hpid ms)))

(in-theory (disable fdp hpidp hpid-fdp))

(in-theory (disable newfd))

;;------------------------------------------------------------------------
;; accept
;;
;; This takes the first connection-request from the queue, and
;; establishes a new connection.  We return a pair (FD MS), where
;; FD is a new (local, server) fd for the connection.  As usual, MS is
;; the updated mstate.
;;
;; In addition, a kludgey thing happens: we bump the PC of the
;; connecting (remote, client) process.  This, in effect, tells that
;; process to stop waiting.
;;
;; If there is nothing to accept, return (-1 MS).

(defun accept (hpid lfd ms)
  (declare (xargs :guard (and (hpidp hpid)
			      (fdp lfd)
			      (mstatep ms))
		  :verify-guards nil))

  (let ((request (first-request hpid lfd (lstates ms)))
	(newfd (newfd hpid ms)))
    (if (not (consp request))
	(list -1 ms)
      (let* ((client-fd (second request))
	     (client-hpid (first request))
	     (client-ps (assoc-equal client-hpid (pstates ms))))

	(if (not (consp client-ps))
	    (list -1 ms)
	  (list newfd
		(make-mstate (update-pstate client-hpid
					    (make-pstate client-hpid
							 (code client-ps)
							 (+ 1 (cc client-ps))
							 (xstack client-ps)
							 (memory client-ps))
					    (pstates ms))
			     (new-connection hpid
					     newfd
					     client-hpid
					     client-fd
					     (cstates ms))
			     (pop-request hpid lfd (lstates ms))
			     (programs ms))))))))

(defthm requestq-properties
  (implies (and (lstatep ls)
		(consp (third ls)))
	   (and (hpidp (car (car (third ls))))
		(cdr (car (third ls)))
		(consp (cdr (car (third ls))))
		(fdp (second (car (third ls))))))
  :hints (("Goal"
           :in-theory (enable hpid-fdp))))

(defthm first-request-forward
  (implies (and (lstate-listp lss)
		(consp (first-request hpid fd lss)))
	   (consp (cdr (first-request hpid fd lss)))))

(in-theory (disable first-request))

(defthm pstate-listp-assoc-forward
  (implies (and (pstate-listp pss)
		(consp (assoc-equal hpid pss)))
	   (and (consp (cdr (assoc-equal hpid pss)))
		(consp (cddr (assoc-equal hpid pss)))
		(consp (cdddr (assoc-equal hpid pss)))
		(consp (cddddr (assoc-equal hpid pss)))))
  :rule-classes :forward-chaining)

(defthm pstatep-second
  (implies (pstatep ps)
	   (codep (second ps))))

(defthm pstatep-third
  (implies (pstatep ps)
	   (acl2-numberp (third ps))))

(defthm pstatep-third-increment
  (implies (pstatep ps)
	   (ccp (+ 1 (third ps)))))

(defthm pstatep-fourth
  (implies (pstatep ps)
	   (xstackp (fourth ps))))

(defthm pstatep-fourth-again
  (implies (pstatep ps)
	   (natural-listp (fourth ps))))

(defthm pstatep-fifth
  (implies (pstatep ps)
	   (memoryp (fifth ps))))

;;---------------

(verify-guards accept
	       :hints (("Goal"
			:in-theory (disable pop-request statementp))))

#|  For example,
(accept '(lutra 320)   ;; source hpid
	 14             ;; listening fd
	 '(
	   (((cosmo 354) nil 13 nil nil))      ;; pstates
	   nil                                 ;; cstates
	   ((((gyro   440) 15) 8585 nil)
	    (((lutra  320) 14) 7483 (((cosmo 354) 16)))
	    (((donner 320) 17) 3535 (((fire  444) 18))))))
|#

(defthm accept-preserves-mstatep
  (implies (and (hpidp hpid)
		(fdp lfd)
		(mstatep ms))
	   (mstatep (second (accept hpid lfd ms))))
  :hints (("Goal"
           :in-theory (disable pop-request statementp))))

;;-------------------------------------------

(in-theory (enable hpidp hpid-fdp))

(defun find-ls (host port lss)
  (declare (xargs :guard (and (hostp host)
			      (portp port)
			      (lstate-listp lss))))
  (cond ((atom lss) nil)
	((and (equal (caaaar lss) host)
	      (equal (second (car lss)) port)) (car lss))
	(t (find-ls host port (cdr lss)))))

(in-theory (disable hpidp hpid-fdp))

;;------------------------------------------------------------------------
;; connect
;;
;; This attempts a connection request.  If the the remote host is not
;; listening on the specified port, nothing happens.  If he is listening,
;; we insert the request into the listening queue of the remote host,
;; and return a new fd for the connecting process.
;;
;; Note that this returns a pair (FD MSTATE).

(defun connect (source-hpid dest-host dest-port ms)
  (declare (xargs :guard (and (hpidp source-hpid)
			      (hostp dest-host)
			      (portp dest-port)
			      (mstatep ms))
		  :verify-guards nil))
  (let ((ls (find-ls dest-host dest-port (lstates ms)))
	(fd (newfd source-hpid ms)))
    (cond ((not (consp ls)) (list -1 ms))  ;; no one is listening
	  (t (list fd
		   (make-mstate (pstates ms)
				(cstates ms)
				(update-alist-member
				 (car ls)
				 (update-requestq ls (append
						      (requestq ls)
						      (list
						       (list source-hpid fd))))
				 (lstates ms))
				(programs ms)))))))

#|  For example,
(connect '(gyro  440)   ;; source hpid
	 'lutra         ;; destination host
	 7483           ;; destination port
	 '(nil     ;; pstates
	   nil     ;; cstates
	   ((((gyro   440) 15) 8585 nil)
	    (((lutra  320) 14) 7483 (((cosmo 354) 16)))
	    (((donner 320) 17) 3535 (((fire  444) 18))))))
|#

(defthm lstatep-find-ls
  (implies (and (lstate-listp lss)
		(consp (find-ls host port lss)))
	   (lstatep (find-ls host port lss))))

(defthm request-listp-append-list
  (implies (and (lstatep ls)
		(hpidp hpid)
		(fdp fd))
	   (request-listp (append (third ls)
				  (list (list hpid fd)))))
  :hints (("Goal"
           :in-theory (enable hpid-fdp))))

;;(defthm request-listp-is-true-listp
;;  (implies (request-listp x)
;;	   (true-listp x)))

(defthm true-listp-third-lstate
  (implies (lstatep ls)
	   (true-listp (third ls)))
  :otf-flg t)

(defthm lstate-listp-assoc-forward
  (implies (and (lstate-listp lss)
		(consp (find-ls host post lss)))
	   (and (consp (cdr (find-ls host post lss)))
		(consp (cddr (find-ls host post lss)))))
  :rule-classes :forward-chaining)

(defthm find-ls-true-listp
  (implies (and (lstate-listp lss)
		(consp (find-ls host port lss)))
	   (true-listp (find-ls host port lss))))

(defthm lstate-listp-update-alist
  (implies (and (lstate-listp lss)
		(lstatep ls))
	   (lstate-listp (update-alist-member x ls lss))))

(defthm update-requestq-lstate-listp
  (implies (and (lstatep ls)
		(hpidp hpid)
		(fdp fd)
		(lstate-listp lss))
	   (lstate-listp (update-alist-member
			  (car ls)
			  (update-requestq ls (append (requestq ls)
						      (list (list hpid fd))))
			  lss)))
  :hints (("Goal"
           :in-theory (enable hpidp))))

(defthm consp-update-ith
  (implies (consp x)
	   (consp (update-ith x i y))))

(verify-guards connect)

(defthm connect-preserves-mstatep
  (implies (and (hpidp source-hpid)
		(hostp dest-host)
		(portp dest-port)
		(mstatep ms))
	   (mstatep (second (connect source-hpid dest-host dest-port ms)))))

;;------------------------------------------------------------------
;; setup-listener
;;
;; This allocates a new fd and adds an lstate to the lstates.
;;
;; Note that this returns a pair (FD MS), where FD is
;; the new fd that is used for listening, and MS is the updated
;; mstate.

(in-theory (enable hpid-fdp))

(defun setup-listener (hpid port ms)
  (declare (xargs :guard (and (hpidp hpid)
			      (portp port)
			      (mstatep ms))))
  (let ((lfd (newfd hpid ms)))
    (list lfd
	  (make-mstate (pstates ms)
		       (cstates ms)
		       (cons (list (list hpid lfd) port nil)
			     (lstates ms))
		       (programs ms)))))

(defthm setup-listener-preserves-mstatep
  (implies (and (hpidp hpid)
		(portp port)
		(mstatep ms))
	   (mstatep (second (setup-listener hpid port ms)))))

(in-theory (disable hpid-fdp))
