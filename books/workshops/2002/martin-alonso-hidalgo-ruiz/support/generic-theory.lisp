;;;============================================================================
;;;
;;; Generic theory tools.
;;;
;;;============================================================================

#| Certification code:

(certify-book "generic-theory")

|#

(in-package "ACL2")

;;;----------------------------------------------------------------------------
;;;
;;; Tools to obtain the event list:
;;;
;;;----------------------------------------------------------------------------

(defun get-event-lst-fn (event-name-lst wrld)
  (declare (xargs :mode :program))
  (cond ((endp event-name-lst) nil)
	(t (cons (get-event (car event-name-lst) wrld)
		 (get-event-lst-fn (cdr event-name-lst) wrld)))))

(defmacro get-event-lst (event-name-lst)
  `(get-event-lst-fn ,event-name-lst (w state)))

;;; Use this as follows

#|

; (get-event-lst <event-name-lst>) => <event-lst>

(defconst *theory*
  <event-lst>
  )

|#

;;;----------------------------------------------------------------------------
;;;
;;; Tools to instantiate the generic theory:
;;;
;;;----------------------------------------------------------------------------

;;; Substitutions:

(defun subst-equal (old new tree)
  (cond ((equal old tree) new)
	((atom tree) tree)
	(t (cons (subst-equal old new (car tree))
		 (subst-equal old new (cdr tree))))))

(defun subst-equal-lst (lst tree)
  (cond ((endp lst) tree)
	(t (subst-equal-lst (cdr lst)
			    (subst-equal (caar lst) (cadar lst) tree)))))

;;; Generating new names:

(defun packn-string-in-pkg (string pkg-witness)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol string pkg-witness))

(defun add-name-subst (name subst suffix)
  (declare (xargs :mode :program))
  (cons (list name
	      (packn-string-in-pkg (string-append (string name) suffix) name))
	subst))

;;; Generating the instantiation:

(defun remove-old-hints (event)
  (cond ((endp event) nil)
	((eq ':hints (car event))
	 (cddr event))
	(t (cons (car event) (remove-old-hints (cdr event))))))

(defun functional-instance (event old-name subst)
  (append (remove-old-hints event)
	  `(:hints
	    (("Goal" :by
	      (:functional-instance ,old-name ,@subst))))))

(defun functional-instance-lst (event-lst subst suffix)
  (declare (xargs :mode :program))
  (cond ((endp event-lst) nil)
	((equal (car (car event-lst)) 'defun)
	 (let ((new-subst
		(add-name-subst (cadr (car event-lst)) subst suffix)))
	   (cons (subst-equal-lst new-subst (car event-lst))
		 (functional-instance-lst (cdr event-lst) new-subst suffix))))
	((equal (car (car event-lst)) 'defthm)
	 (let ((new-subst
		(add-name-subst (cadr (car event-lst)) subst suffix)))
	   (cons (functional-instance
		   (subst-equal-lst new-subst (car event-lst))
		   (cadr (car event-lst))
		   subst)
		 (functional-instance-lst (cdr event-lst) subst suffix))))
	(t (functional-instance-lst (cdr event-lst) subst suffix))))

(defmacro make-generic-theory (theory)
  (let ((definstance-theory
	  (packn-string-in-pkg
	   (string-append "DEFINSTANCE-" (string theory)) theory)))
    `(defmacro ,definstance-theory (subst suffix)
       (list* 'encapsulate
	      'nil
	      (functional-instance-lst ,theory subst
				       (string-upcase suffix))))
    ))

;;; This must be use as follows:

#|

(make-generic-theory *theory*)

|#

;;;============================================================================
