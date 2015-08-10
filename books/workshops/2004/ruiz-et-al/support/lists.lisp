;;;============================================================================
;;;
;;; List tools
;;; Created: 13-02-02
;;;
;;;============================================================================

#| To certify this book:

(certify-book "lists")

|#

(in-package "ACL2")

(set-verify-guards-eagerness 2)

;;;----------------------------------------------------------------------------
;;;
;;; Conjunctive extension to lists
;;;
;;;----------------------------------------------------------------------------

(encapsulate
 (((list-strategy-prop *) => *)
  ((list-strategy-hyp) => *)
  ((list-strategy-list) => *))

 (local
  (defun list-strategy-prop (x)
    (atom x)))

 (local
  (defun list-strategy-hyp ()
    t))

 (local
  (defun list-strategy-list ()
    nil))

 (defthm member-list-prop
   (implies (and (list-strategy-hyp)
		 (member e (list-strategy-list)))
	    (list-strategy-prop e))))

(defun list-strategy-prop-list (list)
  (declare (xargs :guard (true-listp list)))
  (if (endp list)
      t
      (and (list-strategy-prop (car list))
	   (list-strategy-prop-list (cdr list)))))

(encapsulate
 ()

 (local
  (defun sublist-strategy (list1 list2)
    (declare (xargs :guard (and (true-listp list1)
				(eqlable-listp list1)
				(true-listp list2)
				(eqlable-listp list2))))
    (if (endp list1)
	t
	(and (member (car list1) list2)
	     (sublist-strategy (cdr list1) list2)))))

 (local
  (defthm sublist-strategy-cons
    (implies (sublist-strategy list1 list2)
	     (sublist-strategy list1 (cons e list2)))))

 (local
  (defthm sublist-strategy-reflexive
    (sublist-strategy list list)))

 (local
  (defthm sublist-strategy-list-strategy-prop-list
    (implies (and (list-strategy-hyp)
		  (sublist-strategy list (list-strategy-list)))
	     (list-strategy-prop-list list))))

 (defthm list-strategy-prop-list-strategy-list
   (implies (list-strategy-hyp)
	    (list-strategy-prop-list (list-strategy-list)))))

;;; Computed-hint

(defun components-strategy-list (form)
  (declare (xargs :mode :program))

  (case-match form

	      (('IMPLIES form-hyp form-list)
	       (declare (ignore form-list))
	       form-hyp)

	      (& t)))

(defun defun-defstrategy-list-hint (form list prop prop-list)
  (declare (xargs :mode :program))

  `(:use (:functional-instance
	  list-strategy-prop-list-strategy-list
	  (list-strategy-hyp
	   (lambda () ,(components-strategy-list (first form))))
	  (list-strategy-list (lambda () ,list))
          (list-strategy-prop ,prop)
          (list-strategy-prop-list ,prop-list))))

(defmacro conjunctive-extension-list (list prop prop-list)
  `(defun-defstrategy-list-hint clause
     (quote ,list) (quote ,prop) (quote ,prop-list)))

;;;----------------------------------------------------------------------------
;;;
;;; Conjunctive extension to true lists
;;;
;;;----------------------------------------------------------------------------

(encapsulate
 (((true-list-strategy-prop *) => *)
  ((true-list-strategy-hyp) => *)
  ((true-list-strategy-list) => *))

 (local
  (defun true-list-strategy-prop (x)
    (atom x)))

 (local
  (defun true-list-strategy-hyp ()
    t))

 (local
  (defun true-list-strategy-list ()
    nil))

 (defthm member-true-list-prop
   (implies (and (true-list-strategy-hyp)
		 (member e (true-list-strategy-list)))
	    (true-list-strategy-prop e)))

 (defthm true-list-strategy-list-true-listp
   (implies (true-list-strategy-hyp)
	    (true-listp (true-list-strategy-list)))))

(defun true-list-strategy-prop-list (list)
  (declare (xargs :guard (true-listp list)))
  (if (consp list)
      (and (true-list-strategy-prop (car list))
	   (true-list-strategy-prop-list (cdr list)))
      (eq list nil)))

(encapsulate
 ()

 (local
  (defun true-sublist-strategy (list1 list2)
    (declare (xargs :guard (and (true-listp list1)
				(eqlable-listp list1)
				(true-listp list2)
				(eqlable-listp list2))))
    (if (consp list1)
	(and (member (car list1) list2)
	     (true-sublist-strategy (cdr list1) list2))
	(eq list1 nil))))

 (local
  (defthm true-sublist-strategy-cons
    (implies (true-sublist-strategy list1 list2)
	     (true-sublist-strategy list1 (cons e list2)))))

 (local
  (defthm true-sublist-strategy-reflexive
    (implies (true-listp list)
	     (true-sublist-strategy list list))))

 (local
  (defthm true-sublist-strategy-list-strategy-prop-list
    (implies (and (true-list-strategy-hyp)
		  (true-sublist-strategy list (true-list-strategy-list)))
	     (true-list-strategy-prop-list list))))

 (defthm true-list-strategy-prop-list-strategy-list
   (implies (true-list-strategy-hyp)
	    (true-list-strategy-prop-list (true-list-strategy-list)))))

;;; Computed-hint

(defun components-strategy-true-list (form)
  (declare (xargs :mode :program))

  (case-match form

	      (('IMPLIES form-hyp form-list)
	       (declare (ignore form-list))
	       form-hyp)

	      (& t)))

(defun defun-defstrategy-true-list-hint (form list prop prop-list)
  (declare (xargs :mode :program))

  `(:use (:functional-instance
	  true-list-strategy-prop-list-strategy-list
	  (true-list-strategy-hyp
	   (lambda () ,(components-strategy-true-list (first form))))
	  (true-list-strategy-list (lambda () ,list))
          (true-list-strategy-prop ,prop)
          (true-list-strategy-prop-list ,prop-list))))

(defmacro conjunctive-extension-true-list (list prop prop-list)
  `(defun-defstrategy-true-list-hint clause
     (quote ,list) (quote ,prop) (quote ,prop-list)))

;;;============================================================================
