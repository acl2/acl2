(in-package "ACL2")

(include-book "expr")

;;------------------------------------------------------------------------
;; fdexpressionp -- this is a special kind of expression that
;; is a function call, with side effects, that returns an fd.
;; The functions have to do with establishing connections,
;; and the side effects change the lstates and cstates.

#|
    Statements:
  	(asgn variable expression)
        (branch expression name)
	(goto name)
	(label name)
	(call procedure)          ;; what if procedure doesn't exist?
	(return)
        (noop)
	(procedure name)          ;; start of procedure

	(send fd expression)      ;; what if FD doesn't exist?
	(select variable)         ;; returns list of active FDs
	(receive fd variable)
  	(fdasgn variable fdexpression)  ;; for socket primitives
	(fork variable)
	(exec program-name arguments)

|#

(defun statementp (stmt)
  (declare (xargs :guard t))
  (cond ((atom stmt) nil)
	(t (case (car stmt)
		 (asgn (and (equal (len stmt) 3)
			   (varp (second stmt))            ;; variable
			   (expressionp (third stmt))))
		 (setup-listener (and (equal (len stmt) 3)
				      (expressionp (second stmt)) ;; port
				      (varp (third stmt))))       ;; for new FD
		 (connect (and (equal (len stmt) 4)
			       (expressionp (second stmt)) ;; host
			       (expressionp (third stmt))  ;; port
			       (varp (fourth stmt))))      ;; for new FD
		 (accept (and (equal (len stmt) 3)
			      (expressionp (second stmt))  ;; listening FD
			      (varp (third stmt))))        ;; for new FD
		 (my-hpid (and (equal (len stmt) 2)
			       (varp (second stmt))))      ;; for hpid
		 (branch (and (equal (len stmt) 3)
			      (expressionp (second stmt))  ;; test
			      (symbolp (third stmt))))     ;; label
		 (call (and (equal (len stmt) 2)
			    (symbolp (second stmt))))      ;; label
		 (procedure (and (equal (len stmt) 2)
				 (symbolp (second stmt)))) ;; label
		 (label (and (equal (len stmt) 2)
			     (symbolp (second stmt))))     ;; label
		 (goto (and (equal (len stmt) 2)
			    (symbolp (second stmt))))      ;; label
		 (return (and (equal (len stmt) 1)))
		 (send (and (equal (len stmt) 3)
			    (expressionp (second stmt))    ;; fd
			    (expressionp (third stmt))))   ;; message
		 (select (and (equal (len stmt) 3)
			      (expressionp (second stmt))  ;; fds of interest
			      (varp (third stmt))))        ;; receiving var
		 (receive (and (equal (len stmt) 3)
			       (expressionp (second stmt)) ;; fd
			       (varp (third stmt))))       ;; receiving var
		 (fork (and (equal (len stmt) 2)
			    (varp (second stmt))))   ;; for return val of fork
		 (exec (and (equal (len stmt) 3)
			    (symbolp (second stmt))  ;; program name
			    (memoryp (third stmt)))) ;; program args
		 (rsh (and (equal (len stmt) 4)
			   (hostp (second stmt))    ;; host name
			   (symbolp (third stmt))   ;; program name
			   (memoryp (fourth stmt)))) ;; program args
		 (otherwise nil)))))

(in-theory (disable statementp))

(defthm consp-statement-forward
  (implies (statementp stmt)
	   (consp stmt))
  :hints (("Goal"
           :in-theory (enable statementp)))
  :rule-classes :forward-chaining)

;;--------------------------------
;; pstate -- process state

(defun codep (code)
  (declare (xargs :guard t))
  (cond ((atom code) (null code))
	(t (and (statementp (car code))
		(codep (cdr code))))))

(defthm ith-of-code-is-statementp  ;; move to pstate
  (implies (and (codep code)
		(consp (ith n code)))
	   (statementp (ith n code)))
  :hints (("Goal"
           :in-theory (enable statementp))))

(defun ccp (x)  ;; program counter
  (declare (xargs :guard t))
  (naturalp x))

(defun xstackp (x)  ;; execution stack
  (declare (xargs :guard t))
  (natural-listp x))

(defun pstatep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 5)
       (hpidp (first x))
       (codep (second x))
       (ccp (third x))
       (xstackp (fourth x))
       (memoryp (fifth x))))

(defmacro code (ps)
  (list 'second ps))

(defmacro cc (ps)
  (list 'third ps))

(defmacro xstack (ps)
  (list 'fourth ps))

(defmacro memory (ps)
  (list 'fifth ps))

(defmacro update-cc (ps cc)
;;  (declare (xargs :guard (and (pstatep ps)
;;			      (ccp cc))))
  (list 'update-ith ps 3 cc))

(defmacro update-xstack (ps xs)
;;  (declare (xargs :guard (and (pstatep ps)
;;			      (xstackp xs))))
  (list 'update-ith ps 4 xs))

(defmacro update-memory (ps mem)
;;  (declare (xargs :guard (and (pstatep ps)
;;			      (memoryp mem))))
  (list 'update-ith ps 5 mem))

;;----------------------------------------
;; alist of pstates

(defun pstate-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (pstatep (car x))
		(pstate-listp (cdr x))))))

(defthm pstate-list-is-alist
  (implies (pstate-listp x)
	   (alistp x))
  :rule-classes :forward-chaining)

(defthm pstatep-assoc-pstate-listp
  (implies (and (pstate-listp pss)
		(consp (assoc-equal hpid pss)))
	   (pstatep (assoc-equal hpid pss))))

;;---------------

(defun make-pstate (hpid code cc xstack memory)
  (declare (xargs :guard (and (hpidp hpid) (codep code) (ccp cc)
			      (xstackp xstack) (memoryp memory))))
  (list hpid code cc xstack memory))

(defun update-pstate (hpid pstate pstates)
  (declare (xargs :guard (and (hpidp hpid)
			      (pstatep pstate)
			      (pstate-listp pstates))))
  (update-alist-member hpid pstate pstates))

(defthm pstate-listp-update-alist-member
  (implies (and (pstate-listp pss)
		(pstatep ps))
	   (pstate-listp (update-alist-member x ps pss))))

;;---------------------

