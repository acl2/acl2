;;;============================================================================
;;;
;;; An instance of generic multiset theory.
;;;
;;;============================================================================

#| Certification code:

(certify-book "multiset-assoc")

|#

(in-package "ACL2")

;;;----------------------------------------------------------------------------
;;;
;;; A multiset implementation based on association lists:
;;;
;;;----------------------------------------------------------------------------

(include-book "generic-multiset")

(defun select-assoc (alist)
  (cond ((endp alist) nil)
	((and (integerp (cdr (car alist)))
	      (> (cdr (car alist)) 0))
	 (car (car alist)))
	(t (select-assoc (cdr alist)))))

(defun reduct-assoc (alist)
  (cond ((endp alist) nil)
	((and (integerp (cdr (car alist)))
	      (= (cdr (car alist)) 1))
	 (cdr alist))
	((and (integerp (cdr (car alist)))
	      (> (cdr (car alist)) 0))
	 (cons (cons (car (car alist)) (- (cdr (car alist)) 1))
	       (cdr alist)))
	(t (cons (car alist) (reduct-assoc (cdr alist))))))

(defun include-assoc (elt alist)
  (cond ((endp alist) (list (cons elt 1)))
	((and (equal elt (car (car alist)))
	      (integerp (cdr (car alist)))
	      (> (cdr (car alist)) 0))
	 (cons (cons elt (+ (cdr (car alist)) 1))
	       (cdr alist)))
	(t (cons (car alist) (include-assoc elt (cdr alist))))))

(defun empty-assoc (alist)
  (cond ((atom alist) t)
	((or (not (integerp (cdr (car alist))))
	     (<= (cdr (car alist)) 0))
	 (empty-assoc (cdr alist)))
	(t nil)))

(defun measure-assoc (alist)
  (cond ((endp alist) 0)
	((and (integerp (cdr (car alist)))
	      (> (cdr (car alist)) 0))
	 (+ (cdr (car alist)) (measure-assoc (cdr alist))))
	(t (measure-assoc (cdr alist)))))

(defthm o-p-measure-assoc
  (o-p (measure-assoc alist)))

(defthm reduct-assoc-measure-assoc
  (implies (not (empty-assoc alist))
	   (o< (measure-assoc (reduct-assoc alist))
	       (measure-assoc alist))))

(defun count-bag-equal-assoc (elt alist)
  (cond ((endp alist) 0)
	((and (equal elt (car (car alist)))
	      (integerp (cdr (car alist)))
	      (> (cdr (car alist)) 0))
	 (+ (cdr (car alist))
	    (count-bag-equal-assoc elt (cdr alist))))
	(t (count-bag-equal-assoc elt (cdr alist)))))

(defthm another-definition-count-bag-equal-assoc
  (equal (count-bag-equal-assoc e m)
	 (cond ((empty-assoc m) 0)
	       ((equal e (select-assoc m))
		(+ 1 (count-bag-equal-assoc e (reduct-assoc m))))
	       (t (count-bag-equal-assoc e (reduct-assoc m)))))
  :rule-classes :definition)

(defthm count-include-assoc
  (equal (count-bag-equal-assoc e1 (include-assoc e2 m))
	 (if (equal e1 e2)
	     (1+ (count-bag-equal-assoc e1 m))
	     (count-bag-equal-assoc e1 m))))

(definstance-*multiset*
  ((select select-assoc)
   (reduct reduct-assoc)
   (include include-assoc)
   (empty empty-assoc)
   (measure measure-assoc)
   (equiv equal)
   (count-bag-equiv count-bag-equal-assoc))
  "-assoc")

;;;----------------------------------------------------------------------------
;;;
;;; A working example:
;;;
;;;----------------------------------------------------------------------------

#|

(defconst *ma-assoc*
  (include-assoc
   'a (include-assoc
       'a (include-assoc 'b (include-assoc 'b (include-assoc 'c nil))))))

*ma-assoc*
;; ((C . 1) (B . 2) (A . 2))

(defconst *mb-assoc*
  (include-assoc
   'b (include-assoc
       'c (include-assoc 'c (include-assoc 'b (include-assoc 'c nil))))))

*mb-assoc*
;; ((C . 3) (B . 2))

(pe 'union-bag-equiv-assoc)
;; (DEFUN UNION-BAG-EQUIV-ASSOC (M1 M2)
;;   (DECLARE (XARGS :MEASURE (MEASURE-ASSOC M1)))
;;   (COND ((EMPTY-ASSOC M1) M2)
;; 	   (T (INCLUDE-ASSOC (SELECT-ASSOC M1)
;; 			     (UNION-BAG-EQUIV-ASSOC (REDUCT-ASSOC M1) M2)))))

(pe 'inter-bag-equiv-greatest-assoc)
;; (DEFTHM INTER-BAG-EQUIV-GREATEST-ASSOC
;;   (IMPLIES
;;    (AND (SUB-BAG-EQUIV-ASSOC M1 M2)
;; 	   (SUB-BAG-EQUIV-ASSOC M1 M3))
;;    (SUB-BAG-EQUIV-ASSOC M1 (INTER-BAG-EQUIV-ASSOC M2 M3)))
;;   ...)

(union-bag-equiv-assoc *ma-assoc* *mb-assoc*)
;; ((C . 4) (B . 4) (A . 2))

(inter-bag-equiv-assoc *ma-assoc* *mb-assoc*)
;; ((B . 2) (C . 1))

(unimin-bag-equiv-assoc *ma-assoc* *mb-assoc*)
;; ((C . 3) (A . 2) (B . 2))

(diff-bag-equiv-assoc *ma-assoc* *mb-assoc*)
;; ((A . 2))

|#

;;;============================================================================
