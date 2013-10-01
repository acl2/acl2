(in-package "ACL2")

(include-book "expr")

(defun evaluated-expression-listp (x)  ;; move to expr
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	((not (evaluated-expressionp (car x))) nil)
	(t (evaluated-expression-listp (cdr x)))))

;;----------------------------------------
;; cstate -- connection state

(defun connectionp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (hpidp (first x))          ;; source process
       (or (fdp (second x))       ;; source fd if open, nil if closed
	   (null (second x)))
       (hpidp (third x))          ;; destination process
       (fdp (fourth x))))         ;; destination fd

(defun cstatep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 3)
       (connectionp (first x))       ;; connection
       (evaluated-expression-listp (second x))       ;; transit queue
       (evaluated-expression-listp (third x))))      ;; inbox queue

(defmacro transitq (cs)
;;  (declare (xargs :guard (cstatep cs)))
  (list 'second cs))

(defmacro inboxq (cs)
;;  (declare (xargs :guard (cstatep cs)))
  (list 'third cs))

(defmacro update-transitq (cs tq)
;;  (declare (xargs :guard (and (cstatep cs)
;;			      (evaluated-expression-listp tq))))
  (list 'update-ith cs 2 tq))

(defmacro update-inboxq (cs iq)
;;  (declare (xargs :guard (and (cstatep cs)
;;			      (evaluated-expression-listp iq))))
  (list 'update-ith cs 3 iq))

;;----------------------------------------
;; alist of cstates

(defun cstate-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (cstatep (car x))
		(cstate-listp (cdr x))))))

(defthm cstate-list-is-alist
  (implies (cstate-listp x)
	   (alistp x))
  :rule-classes :forward-chaining)

(defthm cstate-listp-contains-cstates
  (implies (and (cstate-listp css)
		(assoc-equal conn css))
	   (cstatep (assoc-equal conn css)))
  :hints (("Goal"
           :in-theory (disable cstatep))))

;;--------------------------------------

(defun message-to-transfer (cs)
  (declare (xargs :guard (cstatep cs)))
  (consp (transitq cs)))

(in-theory (enable constp varp))

(defun transfer-message (cs)

  ;; Given a cstate with a nonempty transit queue, move the first
  ;; message in the transit queue to the end of the inbox queue.

  (declare (xargs :guard (and (cstatep cs)
			      (message-to-transfer cs))))
  (update-inboxq
   (update-transitq cs (cdr (transitq cs)))
   (append (inboxq cs) (list (car (transitq cs))))))

;; For example,

#|
(transfer-message '(((lutra 320) 5 (gyro 440) 6) ('m3 'm4) ('m1 'm2)))
|#

(defthm transfer-message-preserves-cstatep
  (implies (and (cstatep cs)
		(message-to-transfer cs))
	   (cstatep (transfer-message cs)))
  :otf-flg t)

(defun active-cstates (css)
  ;; Return the number of cstates with messages in transit.
  (declare (xargs :guard (cstate-listp css)))
  (cond ((atom css) 0)
	(t (+ (if (message-to-transfer (car css)) 1 0)
	      (active-cstates (cdr css))))))

(defun ith-active-cstate (n css)  ;; This counts from 1.
  (declare (xargs :guard (and (pos-integerp n)
			      (cstate-listp css))))
  (cond ((atom css) nil)
	((message-to-transfer (car css))
	 (if (equal n 1)
	     (car css)
	   (ith-active-cstate (- n 1) (cdr css))))
	(t (ith-active-cstate n (cdr css)))))

(defthm cstate-listp-update
  (implies (and (cstate-listp css)
		(cstatep cs))
	   (cstate-listp (update-alist-member x cs css))))

(defthm ith-active-cstate-properties
  (implies (and (cstate-listp css)
		(integerp n)
		(> n 0)
		(<= n (active-cstates css)))
	   (and (cstatep (ith-active-cstate n css))
		(member-equal (ith-active-cstate n css) css)
		(message-to-transfer (ith-active-cstate n css))
		(consp (cadr (ith-active-cstate n css)))))
  :hints (("Goal"
           :in-theory (disable cstatep))))

(defun make-cstate (conn tq iq)
  (declare (xargs :guard (and (connectionp conn)
			      (evaluated-expression-listp tq)
			      (evaluated-expression-listp iq))))
  (list conn tq iq))

(defun update-cstate (connection cstate cstates)
  (declare (xargs :guard (and (connectionp connection)
			      (cstatep cstate)
			      (cstate-listp cstates))))
  (update-alist-member connection cstate cstates))

(defthm cstate-properties
  (implies (cstatep cs)
	   (and (connectionp (car cs))
		(evaluated-expression-listp (cadr cs))
		(evaluated-expression-listp (caddr cs)))))

(in-theory (disable constp varp))

