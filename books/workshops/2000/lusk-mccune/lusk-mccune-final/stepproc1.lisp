(in-package "ACL2")

(include-book "mstate")

;;---------------

;; forward chaining rules for kinds of statement

(in-theory (enable statementp))

(defthm statement-my-hpid-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'my-hpid))
	   (and (consp (cdr stmt))
		(varp (cadr stmt))))
  :rule-classes :forward-chaining)

(defthm statement-goto-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'goto))
	   (and (consp (cdr stmt))
		(symbolp (cadr stmt))))
  :rule-classes :forward-chaining)

(defthm statement-call-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'call))
	   (and (consp (cdr stmt))
		(symbolp (cadr stmt))))
  :rule-classes :forward-chaining)

(defthm statement-asgn-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'asgn))
	   (and (consp (cdr stmt))
		(consp (cddr stmt))
		(varp (second stmt))
		(expressionp (third stmt))
		))
  :rule-classes :forward-chaining)

(defthm statement-branch-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'branch))
	   (and (consp (cdr stmt))
		(consp (cddr stmt))
		(expressionp (second stmt))
		(symbolp (third stmt))
		))
  :rule-classes :forward-chaining)

(defthm statement-send-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'send))
	   (and (consp (cdr stmt))
		(consp (cddr stmt))
		(expressionp (second stmt))
		(expressionp (third stmt))
		))
  :rule-classes :forward-chaining)

(defthm statement-receive-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'receive))
	   (and (consp (cdr stmt))
		(consp (cddr stmt))
		(expressionp (second stmt))
		(varp (third stmt))
		))
  :rule-classes :forward-chaining)

(defthm statement-select-forward
  (implies (and (statementp stmt)
		(equal (car stmt) 'select))
	   (and (consp (cdr stmt))
		(consp (cddr stmt))
		(expressionp (second stmt))
		(varp (third stmt))
		))
  :rule-classes :forward-chaining)

(in-theory (disable statementp))

;;---------------
;; index-of-name gets the index of a label statment so that
;; we can set the program counter when we execute goto, call, and
;; branch statements.

(in-theory (enable statementp))

(defun index-of-name (name code i)
  (declare (xargs :guard (and (symbolp name)
			      (codep code)
			      (pos-integerp i))))
  (cond ((atom code) 0)
	((and (or (equal (caar code) 'procedure)
		  (equal (caar code) 'label))
	      (equal (second (car code)) name)) i)
	(t (index-of-name name (cdr code) (+ 1 i)))))

(in-theory (disable statementp))

(defthm index-of-name-is-naturalp
  (implies (pos-integerp i)
	   (naturalp (index-of-name name code i))))

;;==================
;; Here are 2 simple operations: return, skip.  Define and
;; prove that they preserve mstatep.

(defun exec-skip (ps ms)  ;; just increment the program counter
  (declare (xargs :guard (and (mstatep ms)
			      (pstatep ps))))
  (make-mstate
   (update-pstate (car ps)
		  (make-pstate (car ps)
			       (code ps)
			       (+ 1 (cc ps))
			       (xstack ps)
			       (memory ps))
		  (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm exec-skip-preserves-mstatep
  (implies (and (mstatep ms)
		(pstatep ps))
	   (mstatep (exec-skip ps ms))))

(defun exec-return (ps ms)
  (declare (xargs :guard (and (mstatep ms)
			      (pstatep ps))))
  (if (atom (xstack ps))
      (make-mstate
       (update-pstate (car ps)
		      (make-pstate (car ps)
				   (code ps)
				   0
				   (xstack ps)
				   (memory ps))
		      (pstates ms))
       (cstates ms)
       (lstates ms)
       (programs ms))

    (make-mstate
     (update-pstate (car ps)
		    (make-pstate (car ps)
				 (code ps)
				 (car (xstack ps))
				 (cdr (xstack ps))
				 (memory ps))
		    (pstates ms))
     (cstates ms)
     (lstates ms)
     (programs ms))))

(defthm exec-return-preserves-mstatep
  (implies (and (mstatep ms)
		(pstatep ps))
	   (mstatep (exec-return ps ms))))

;;---------------------------------------------------

(defun exec-goto (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'goto)
			      (mstatep ms)
			      (pstatep ps))))
  (make-mstate
   (update-pstate (car ps)
		  (make-pstate (car ps)
			       (code ps)
			       (index-of-name (second stmt) (code ps) 1)
			       (xstack ps)
			       (memory ps))
		  (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm exec-goto-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'goto)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-goto stmt ps ms))))

(defun exec-call (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'call)
			      (mstatep ms)
			      (pstatep ps))))
  (make-mstate
   (update-pstate (car ps)
		  (make-pstate (car ps)
			       (code ps)
			       (index-of-name (second stmt) (code ps) 1)
			       (cons (+ 1 (cc ps)) (xstack ps))
			       (memory ps))
		  (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm exec-call-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'call)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-call stmt ps ms))))

;;======================================================

(defun exec-my-hpid (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'my-hpid)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))
  (make-mstate
   (update-pstate (car ps)
		  (make-pstate (car ps)
			       (code ps)
			       (+ 1 (cc ps))
			       (xstack ps)
			       (asgn (second stmt)
				     (list (list 'quote (first (car ps)))
					   (second (car ps)))
				     (memory ps)))
		  (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm my-hpid-helper
  (implies (hpidp hpid)
	   (evaluated-expressionp (list (list 'quote (first hpid))
					(second hpid))))
  :hints (("Goal"
           :in-theory (enable hostp pidp hpidp constp))))

(verify-guards exec-my-hpid
  :hints (("Goal"
           :in-theory (enable hpidp))))

(defthm exec-my-hpid-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'my-hpid)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-my-hpid stmt ps ms)))
  :hints (("Goal"
           :in-theory (enable hpidp))))

;;======================================================

(defun exec-asgn (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'asgn)
			      (mstatep ms)
			      (pstatep ps))))
  (make-mstate
   (update-pstate (car ps)
		  (make-pstate (car ps)
			       (code ps)
			       (+ 1 (cc ps))
			       (xstack ps)
			       (asgn (second stmt)
				     (evl2 (third stmt) (memory ps))
				     (memory ps)))
		  (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm exec-asgn-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'asgn)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-asgn stmt ps ms))))

;;===================================================

;; The following speeds up exec-branch proofs below.

(defun branch-destination (stmt mem code cc)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'branch)
			      (codep code)
			      (ccp cc)
			      (memoryp mem))))
  (if (equal (evl2 (second stmt) mem) ''true)
      (index-of-name (third stmt) code 1)
    (+ 1 cc)))

(defthm branch-destination-ccp
  (implies (ccp cc)
	   (ccp (branch-destination stmt mem code cc))))

(in-theory (disable branch-destination))

(defun exec-branch (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'branch)
			      (mstatep ms)
			      (pstatep ps))))
  (make-mstate
   (update-pstate
    (car ps)
    (make-pstate (car ps)
		 (code ps)
		 (branch-destination stmt (memory ps) (code ps) (cc ps))
		 (xstack ps)
		 (memory ps))
    (pstates ms))
   (cstates ms)
   (lstates ms)
   (programs ms)))

(defthm exec-branch-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'branch)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-branch stmt ps ms))))

;;==================================================

(defthm cstatep-send
  (implies (and (cstatep cs)
		(evaluated-expressionp e))
	   (cstatep (list (car cs)
			  (append (cadr cs) (list e))
			  (caddr cs)))))

(defthm cstatep-receive
  (implies (and (cstatep cs)
		(consp (inboxq cs)))
	   (cstatep (list (first cs)
			  (second cs)
			  (cdr (third cs))))))

(defun sender-cstate (hpid fd css)
  (declare (xargs :guard (and (hpidp hpid) (fdp fd) (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal hpid (first  (caar css)))
	      (equal fd   (second (caar css)))) (car css))
	(t (sender-cstate hpid fd (cdr css)))))

(defthm sender-cstate-cstatep
  (implies (and (cstate-listp css)
		(consp (sender-cstate x y css)))
	   (cstatep (sender-cstate x y css))))

(defun receiver-cstate (hpid fd css)
  (declare (xargs :guard (and (hpidp hpid) (fdp fd) (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal hpid (third  (caar css)))
	      (equal fd   (fourth (caar css)))) (car css))
	(t (receiver-cstate hpid fd (cdr css)))))

(defthm receiver-cstate-cstatep
  (implies (and (cstate-listp css)
		(consp (receiver-cstate x y css)))
	   (cstatep (receiver-cstate x y css))))

;;==================================================

(defun exec-send (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'send)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))
  (let* ((fd (evl2 (second stmt) (memory ps)))
	 (cs (if (fdp fd)
		 (sender-cstate (car ps) fd (cstates ms))
	       nil)))

    (cond ((atom cs)
	   ;; The FD is bad, so set pc to 0 and set error variable.
	   (make-mstate
	    (update-pstate (car ps)
			   (make-pstate (car ps)
					(code ps)
					0
					(xstack ps)
					(asgn 'error
					      ''bad-fd-in-send
					      (memory ps)))
			   (pstates ms))
	    (cstates ms)
	    (lstates ms)
	    (programs ms)))

	  ;; all is well
	  (t (make-mstate
	      (update-pstate (car ps)
			     (make-pstate (car ps)
					  (code ps)
					  (+ 1 (cc ps))
					  (xstack ps)
					  (memory ps))
			     (pstates ms))
	      (update-cstate (car cs)
			     (make-cstate (car cs)
					  (append (transitq cs)
						  (list (evl2 (third stmt)
							     (memory ps))))
					  (inboxq cs))
			     (cstates ms))
	      (lstates ms)
	      (programs ms))))))

(defthm second-of-cstate-is-true-listp
  (implies (cstatep cs)
	   (true-listp (second cs)))
  :otf-flg t)

(defthm cstate-listp-sender-forward
  (implies (and (cstate-listp css)
		(consp (sender-cstate hpid fd css)))
	   (and (consp (cdr (sender-cstate hpid fd css)))
		(consp (cddr (sender-cstate hpid fd css)))))
  :rule-classes :forward-chaining)

(verify-guards exec-send
	       :hints (("Goal"
			:in-theory (disable connectionp
					    cstatep

					    ;; mstatep
					    ;; pstatep
					    ;; xstackp ccp
					    ))))

(defthm exec-send-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'send)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-send stmt ps ms))))

;;==================================================================

(defthm evaluated-expressionp-car-inbox
  (implies (and (cstatep cs)
		(consp (caddr cs)))
	   (evaluated-expressionp (caaddr cs)))
  :hints (("Goal"
           :in-theory (enable constp))))

(defun exec-receive (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'receive)
			      (mstatep ms)
			      (pstatep ps))
		  :verify-guards nil))

  (let* ((fd (evl2 (second stmt) (memory ps)))
	 (cs (if (fdp fd)
		 (receiver-cstate (car ps) fd (cstates ms))
	       nil)))

    (cond ((atom cs)
	   ;; the FD is bad, so halt with error message
	   (make-mstate
	    (update-pstate (car ps)
			   (make-pstate (car ps)
					(code ps)
					0
					(xstack ps)
					(asgn 'error
					      ''bad-fd-in-receive
					      (memory ps)))
			   (pstates ms))
	    (cstates ms)
	    (lstates ms)
	    (programs ms)))

	  ((atom (inboxq cs))
	   ;; no message to receive, so wait (i.e., don't change state)
	   ms)

	  ;; all is well
	  (t (make-mstate
	      (update-pstate (car ps)
			     (make-pstate (car ps)
					  (code ps)
					  (+ 1 (cc ps))
					  (xstack ps)
					  (asgn (third stmt)
						(car (inboxq cs))
						(memory ps)))
			     (pstates ms))
	      (update-cstate (car cs)
			     (make-cstate (car cs)
					  (transitq cs)
					  (cdr (inboxq cs)))
			     (cstates ms))
	      (lstates ms)
	      (programs ms))))))

(defthm cstate-cdr-inbox
  (implies (and (cstatep cs)
		(consp (caddr cs)))
	   (evaluated-expression-listp (cdr (caddr cs)))))

(defthm cstate-listp-receiver-forward
  (implies (and (cstate-listp css)
		(consp (receiver-cstate hpid fd css)))
	   (and (consp (cdr (receiver-cstate hpid fd css)))
		(consp (cddr (receiver-cstate hpid fd css)))))
  :rule-classes :forward-chaining)

(verify-guards exec-receive
	       :hints (("Goal"
			:in-theory (disable connectionp cstatep))))

(defthm exec-receive-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'receive)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-receive stmt ps ms))))

;;===========================================================
;; select - given an hpid, return the list of FDs that have
;; messages or connection-requests available for receiving.
;; This includes both ordinary FSs (from cstates) and listening
;; FDs (from lstates).

(defun select-ordinary-fds (hpid css)
  (declare (xargs :guard (and (hpidp hpid)
			      (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal hpid (third (caar css)))
	      (consp (inboxq (car css))))
	 (cons (fourth (caar css))
	       (select-ordinary-fds hpid (cdr css))))
	(t (select-ordinary-fds hpid (cdr css)))))

(in-theory (enable hpid-fdp))

(defun select-listening-fds (hpid lss)
  (declare (xargs :guard (and (hpidp hpid)
			      (lstate-listp lss))))
  (cond ((atom lss) nil)
	((and (equal hpid (first (caar lss)))
	      (consp (requestq (car lss))))
	 (cons (second (caar lss))
	       (select-listening-fds hpid (cdr lss))))
	(t (select-listening-fds hpid (cdr lss)))))

(in-theory (disable hpid-fdp))

(defun select (hpid fds-of-interest ms)
  (declare (xargs :guard (and (hpidp hpid)
			      (mstatep ms))))
  (intersect-equal (lfix fds-of-interest)
		   (append (select-ordinary-fds hpid (cstates ms))
			   (select-listening-fds hpid (lstates ms)))))

;; For example,

#|
(select-ordinary-fds '(gyro 4) '((((a 1) 7 (gyro 4) 1) nil ('m1 'm2 'm3))
				 (((b 2) 8 (junk 3) 2) nil ('m4 'm5))
				 (((c 3) 9 (gyro 4) 3) nil ('m6))))

(select-listening-fds '(gyro 4) '((((gyro 4) 1) 81 (((donner 101) 6)))
				  (((junk 3) 2) 82 (((juju 102) 7)))
				  (((gyro 4) 3) 83 (((lutra 103) 8)))))

(select '(gyro 4) '(1 6 9) '(nil
		    ((((a 1) 7 (gyro 4) 1) nil ('m1 'm2 'm3))
		     (((b 2) 8 (junk 3) 2) nil ('m4 'm5))
		     (((c 3) 9 (gyro 4) 3) nil ('m6)))
		    ((((gyro 4) 4) 81 (((donner 101) 6)))
		     (((junk 3) 5) 82 (((juju 102) 7)))
		     (((gyro 4) 6) 83 (((lutra 103) 8))))))

|#

(defthm select-ordinary-fds-gives-fd-listp
  (implies (cstate-listp css)
	   (fd-listp (select-ordinary-fds x css))))

(defthm select-listening-fds-gives-fd-listp
  (implies (lstate-listp lss)
	   (fd-listp (select-listening-fds x lss)))
  :hints (("Goal"
           :in-theory (enable hpid-fdp))))

(defthm fd-listp-append
  (implies (and (fd-listp a)
		(fd-listp b))
	   (fd-listp (append a b))))

(defthm fd-listp-intersect
  (implies (or (fd-listp a)
	       (fd-listp b))
	   (fd-listp (intersect-equal a b))))

(defthm select-gives-fd-listp
  (implies (mstatep ms)
	   (fd-listp (select x y ms))))

(defthm select-gives-true-listp
  (true-listp (select x y ms)))

(in-theory (disable select))

(defthm fdp-is-evaluated-expressionp
  (implies (fdp x)
	   (evaluated-expressionp x))
  :hints (("Goal"
           :in-theory (enable fdp))))

(defthm fd-listp-is-evaluated-expressionp
  (implies (fd-listp fds)
	   (evaluated-expressionp fds)))

(defthm select-gives-evaluated-expressionp
  (implies (mstatep ms)
	   (evaluated-expressionp (select x y ms))))

;;-----------------------------------------------------------------
;; exec-select
;;
;; If any messages are available, set the variable to the list of FDs.
;; If not, do nothing (i.e., wait).

(defun exec-select (stmt ps ms)
  (declare (xargs :guard (and (statementp stmt)
			      (equal (car stmt) 'select)
			      (mstatep ms)
			      (pstatep ps))))
  (let ((sel (select (car ps) (evl2 (second stmt) (memory ps)) ms)))
    (if (null sel)
	ms ;; no messages to receive, so wait (i.e., don't change state)
      (make-mstate
       (update-pstate (car ps)
		      (make-pstate (car ps)
				   (code ps)
				   (+ 1 (cc ps))
				   (xstack ps)
				   (asgn (third stmt)
					 sel
					 (memory ps)))
		      (pstates ms))
       (cstates ms)
       (lstates ms)
       (programs ms)))))

(defthm exec-select-preserves-mstatep
  (implies (and (statementp stmt)
		(equal (car stmt) 'select)
		(mstatep ms)
		(pstatep ps))
	   (mstatep (exec-select stmt ps ms))))

;;------------------------------------------------------
