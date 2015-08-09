(in-package "ACL2")

(include-book "cstate")
(include-book "pstate")
(include-book "lstate")

;; At this point we start associating cstates with pstates (because
;; processes alter connections).

(defun something-to-receive (hpid fd css)
  (declare (xargs :guard (and (hpidp hpid)
			      (fdp fd)
			      (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal hpid (third (first (car css))))
	      (equal fd (fourth (first (car css))))
	      (consp (inboxq (car css)))) t)
	(t (something-to-receive hpid fd (cdr css)))))

(defun message-to-select (hpid css)
  (declare (xargs :guard (and (hpidp hpid)
			      (cstate-listp css))))
  (cond ((atom css) nil)
	((and (equal hpid (third (first (car css))))
	      (consp (inboxq (car css)))) t)
	(t (message-to-select hpid (cdr css)))))

(in-theory (enable hpid-fdp))

(defun request-to-select (hpid lss)
  (declare (xargs :guard (and (hpidp hpid)
			      (lstate-listp lss))))
  (cond ((atom lss) nil)
	((and (equal hpid (first (first (car lss))))
	      (consp (requestq (car lss)))) t)
	(t (request-to-select hpid (cdr lss)))))

(in-theory (disable hpid-fdp))

(in-theory (enable statementp))

(defun pstate-status (ps css lss)
  (declare (xargs :guard (and (pstatep ps)
			      (cstate-listp css)
			      (lstate-listp lss))))
  (let ((stmt (if (zp (cc ps)) nil (ith (cc ps) (code ps)))))
    (cond ((atom stmt) 'idle)  ;; cc 0 or out of range
	  ((equal (car stmt) 'receive)
	   (let ((fd (evl2 (second stmt) (memory ps))))
	     (cond ((not (fdp fd)) 'active)  ;; handle error elsewhere
		   (t (if (something-to-receive (car ps) fd css)
			  'active 'waiting)))))
	  ((equal (car stmt) 'select)
	   (if (or (message-to-select (car ps) css)
		   (request-to-select (car ps) lss))
	       'active 'waiting))
	  ;; We should also check here if the process is waiting for
	  ;; a connect or waiting for an accept.  As it is, the
	  ;; simulator will attempt these, so it might spin.
	  (t 'active))))

(in-theory (disable statementp))

(defun waiting-pstates (pss css lss)
  ;; Return the number of processes hanging in receive or select.
  (declare (xargs :guard (and (pstate-listp pss)
			      (cstate-listp css)
			      (lstate-listp lss))))
  (cond ((atom pss) 0)
	(t (+ (if (equal (pstate-status (car pss) css lss)
			 'waiting) 1 0)
	      (waiting-pstates (cdr pss) css lss)))))

(defun active-pstates (pss css lss)
  ;; Return the number of processes with something to do.
  (declare (xargs :guard (and (pstate-listp pss)
			      (cstate-listp css)
			      (lstate-listp lss))))
  (cond ((atom pss) 0)
	(t (+ (if (equal (pstate-status (car pss) css lss)
			 'active) 1 0)
	      (active-pstates (cdr pss) css lss)))))

(defun ith-active-pstate (n pss css lss)  ;; This counts from 1.
  (declare (xargs :guard (and (pos-integerp n)
			      (pstate-listp pss)
			      (cstate-listp css)
			      (lstate-listp lss))))
  (cond ((atom pss) nil)
	((equal (pstate-status (car pss) css lss) 'active)
	 (if (equal n 1)
	     (car pss)
	   (ith-active-pstate (- n 1) (cdr pss) css lss)))
	(t (ith-active-pstate n (cdr pss) css lss))))

(defthm ith-active-pstate-properties
  (implies (and (pstate-listp pss)
		(cstate-listp css)
		(lstate-listp lss)
		(integerp n)
		(> n 0)
		(<= n (active-pstates pss css lss)))
	   (and (pstatep (ith-active-pstate n pss css lss))
	        (member-equal (ith-active-pstate n pss css lss) pss)))
  :hints (("Goal"
           :in-theory (disable pstatep))))

;;----------------------------------------
;; prog: (program-name program-code)

(defun progp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (symbolp (first x))
       (codep (second x))))

(defun program-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (progp (car x))
		(program-listp (cdr x))))))

(defthm program-listp-is-alistp
  (implies (program-listp pgms)
	   (alistp pgms))
  :rule-classes :forward-chaining)

;;----------------------------------------
;; mstate -- multiprocess state

(defun mstatep (x)
  (declare (xargs :guard t))
  (and (equal (len x) 4)
       (pstate-listp (first x))
       (cstate-listp (second x))
       (lstate-listp (third x))
       (program-listp (fourth x))))

(defun pstates (ms)  ;; get the list of pstates from an mstate
  (declare (xargs :guard (mstatep ms)))
  (first ms))

(defun cstates (ms)  ;; get the list of cstates from an mstate
  (declare (xargs :guard (mstatep ms)))
  (second ms))

(defun lstates (ms)  ;; get the list of lstates from an mstate
  (declare (xargs :guard (mstatep ms)))
  (third ms))

(defun programs (ms)  ;; get the list of programs from an mstate
  (declare (xargs :guard (mstatep ms)))
  (fourth ms))

(defun update-pstates (ms pss)
  (declare (xargs :guard (and (mstatep ms)
			      (pstate-listp pss))))
  (update-first ms pss))

(defun update-cstates (ms css)
  (declare (xargs :guard (and (mstatep ms)
			      (cstate-listp css))))
  (update-second ms css))

(defun update-lstates (ms lss)
  (declare (xargs :guard (and (mstatep ms)
			      (lstate-listp lss))))
  (update-third ms lss))


#|
(mstatep '(
	   (  ;; pstates:
	    ((lutra 320) ((asgn z 6)) 13 nil ((x . 4) (y . 6)))
	    ((gyro  440) ((procedure handle)) 14 nil nil)
	    )

	   (  ;; cstates:
	    (((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2))
	    )
	   (  ;; lstates:
	    (((gyro   440) 15) 8585 nil)
	    (((lutra  320) 14) 7483 (((cosmo 354) 16)))
	    (((donner 320) 17) 3535 (((fire  444) 18)))
	    )
	   nil ;; programs
	   ))
|#

(defthm true-listp-append-list
  (true-listp (append a (list x))))

(defthm evaluated-expression-append
  (implies (and (evaluated-expression-listp a)
		(evaluated-expressionp x))
	   (evaluated-expression-listp (append a (list x)))))

(defun deliver-message (ms cs)
  (declare (xargs :guard (and (mstatep ms)
			      (cstatep cs)
			      (member-equal cs (cstates ms))
			      (message-to-transfer cs))))
  (update-cstates
   ms
   (update-alist-member
    (car cs)
    (transfer-message cs)
    (cstates ms))))

;; For example,

#|
(deliver-message '((
		    ((lutra 320) ((asgn z 6)) 13 nil ((x . 4) (y . 6)))
		    ((gyro  440) ((procedure handle)) 14 nil nil)
		    )
		   (
		    (((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2))
		    )
		   nil
		   )

		 '(((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2)))
|#

(defthm mstatep-deliver-message
  (implies (and (mstatep ms)
                (cstatep cs))
           (mstatep (deliver-message ms cs))))

;;---------------

(defun make-mstate (pstates cstates lstates programs)
  (declare (xargs :guard (and (pstate-listp pstates)
			      (cstate-listp cstates)
			      (lstate-listp lstates)
			      (program-listp programs)
			      )))
  (list pstates cstates lstates programs))
