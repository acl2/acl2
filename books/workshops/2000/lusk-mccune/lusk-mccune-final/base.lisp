(in-package "ACL2")

(include-book "util")

;;----------------------------------------
;;
;; mstate:     (pstates cstates lstates)          ;; multiprocess state
;;   pstate:     (hpid code cc xstack memory)     ;; process state
;;   cstate:     (connection transitq inboxq)     ;; connection state
;;     connection: (hpid1 fd1 hpid2 fd2)
;;   lstate:     ((hpid fd) port requestq)        ;; listening state
;;
;;----------------------------------------

;; Simple recognizers used by both pstate and cstate

(defun hostp (x)               ;; host name -- symbolp
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (null x))))

(defun pidp (x)                ;; process ID -- pos-integer
  (declare (xargs :guard t))
  (pos-integerp x))

(defun hpidp (x)               ;; host/process ID -- (hostp pidp)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (hostp (first x))
       (pidp (second x))))

(defun fdp (x)                 ;; file descriptor -- natural
  (declare (xargs :guard t))
  (naturalp x))

(defun fd-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	((not (fdp (car x))) nil)
	(t (fd-listp (cdr x)))))

(defun portp (x)               ;; port name -- pos-integer
  (declare (xargs :guard t))
  (pos-integerp x))

(defun hpid-fdp (x)              ;; hpid-fdp -- (hpidp fpd)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (hpidp (first x))
       (fdp (second x))))

(in-theory (disable hostp pidp hpidp fdp portp hpid-fdp))

;; These are for our programming language.

(defun varp (x)                ;; variable -- symbolp
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (null x))))

(defun constp (x)              ;; constant -- (quote symbolp)
  (declare (xargs :guard t))
  (and (equal (len x) 2)
       (equal (first x) 'quote)
       (symbolp (second x))
       (not (null (second x)))
       (null (cddr x))))

(in-theory (disable varp constp))



