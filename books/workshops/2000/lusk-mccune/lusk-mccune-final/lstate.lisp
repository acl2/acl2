(in-package "ACL2")

(include-book "base")

;;----------------------------------------
;; lstate -- listening state
;;
;; ((hpid lfd) port requestq)
;;
;; This means that hpid is listening on lfd for connections
;; at the port.  When a process p issues a "(connect hpid port)",
;; the pair (p fd) is added to the request queue.  When the
;; listening process issues an (accept lfd), the first request is
;; removed from requestq, and a new connection is established.

(defun request-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (hpid-fdp (car x))
		(request-listp (cdr x))))))

(defun lstatep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 3)
       (hpid-fdp (first x))
       (portp (second x))
       (request-listp (third x))))

(defmacro port (ls)
;;  (declare (xargs :guard (lstatep ls)))
  (list 'second ls))

(defmacro requestq (ls)
;;  (declare (xargs :guard (lstatep ls)))
  (list 'third ls))

(defmacro update-requestq (ls rq)
;;  (declare (xargs :guard (and (lstatep ls)
;;                              (request-listp rq))))
  (list 'update-ith ls 3 rq))

(defun lstate-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
	(t (and (lstatep (car x))
		(lstate-listp (cdr x))))))

(defthm lstate-list-is-alist
  (implies (lstate-listp x)
	   (alistp x))
  :rule-classes :forward-chaining)

(defthm lstate-assoc
  (implies (and (lstate-listp lss)
		(assoc-equal x lss))
	   (lstatep (assoc-equal x lss))))

;; first-request -- get the first pair (hpid fd) from the request
;; queue, or NIL if the queue is empty.

(defun first-request (hpid lfd lss)
  (declare (xargs :guard (and (hpidp hpid)
			      (fdp lfd)
			      (lstate-listp lss))))
  (let ((ls (assoc-equal (list hpid lfd) lss)))
    (cond ((not ls) nil)
	  ((atom (third ls)) nil)
	  (t (car (third ls))))))

(defthm first-request-gets-hpid-fd
  (implies (and (lstate-listp lss)
		(consp (first-request hpid lfd lss)))
	   (and (hpidp (first (first-request hpid lfd lss)))
		(fdp (second (first-request hpid lfd lss)))))
  :hints (("Goal"
           :in-theory (enable hpid-fdp))))

;; pop-request -- remove the first pair (hpid fd) from the request queue.

(defun pop-request (hpid lfd lss)
  (declare (xargs :guard (and (hpidp hpid)
			      (fdp lfd)
			      (lstate-listp lss))))
  (let ((ls (assoc-equal (list hpid lfd) lss)))
    (cond ((not ls) lss)
	  ((not (consp (requestq ls))) lss)
	  (t (update-alist-member (list hpid lfd)
				  (update-requestq ls (cdr (requestq ls)))
				  lss)))))

#|  For example,
(pop-request '(lutra 320)
	     14
	     '((((gyro   440) 15) 8585 nil)
	       (((lutra  320) 14) 7483 (((cosmo 354) 16)))
	       (((donner 320) 17) 3535 (((fire  444) 18)))))
|#

(defthm pop-request-preserves-lstate-listp
  (implies (and (hpidp hpid)
		(fdp lfd)
		(lstate-listp lss))
	   (lstate-listp (pop-request hpid lfd lss))))

(include-book "cstate")

(defun new-connection (hpid1 fd1 hpid2 fd2 css)
  (declare (xargs :guard (and (hpidp hpid1)
			      (fdp fd1)
			      (hpidp hpid2)
			      (fdp fd2)
			      (cstate-listp css))))

  (list* (list (list hpid1 fd1 hpid2 fd2) nil nil)
	 (list (list hpid2 fd2 hpid1 fd1) nil nil)
	 css))

(defthm new-connection-preserves-cstate-listp
  (implies (and (hpidp hpid1)
		(fdp fd1)
		(hpidp hpid2)
		(fdp fd2)
		(cstate-listp css))
	   (cstate-listp (new-connection hpid1 fd1 hpid2 fd2 css))))

;;--------------------------------------------------------------------

(defun listening-pairs (lss)
  (declare (xargs :guard (lstate-listp lss)))
  (cond ((atom lss) nil)
	(t (cons (caar lss)
		 (listening-pairs (cdr lss))))))

(defun connection-pairs (css)
  (declare (xargs :guard (cstate-listp css)))
  (cond ((atom css) nil)
	(t (list* (list (first (caar css)) (second (caar css)))
		  (list (third (caar css)) (fourth (caar css)))
		  (connection-pairs (cdr css))))))

(in-theory (enable hpid-fdp))

(defun fds-in-use (hpid pairs)
  (declare (xargs :guard (and (hpidp hpid)
			      (request-listp pairs))))
  (cond ((atom pairs) nil)
	((equal (first (car pairs)) hpid)
	 (cons (second (car pairs)) (fds-in-use hpid (cdr pairs))))
	(t (fds-in-use hpid (cdr pairs)))))

(in-theory (disable hpid-fdp))


