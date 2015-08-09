;;;============================================================================
;;;
;;; An instance of generic multiset theory.
;;;
;;;============================================================================

#| Certification code:

(certify-book "multiset-list")

|#

(in-package "ACL2")

;;;----------------------------------------------------------------------------
;;;
;;; A multiset implementation based on lists:
;;;
;;;----------------------------------------------------------------------------

(include-book "generic-multiset")

;; select = car
;; reduct = cdr
;; include = cons
;; empty = atom
;; measure = acl2-count

(defun count-bag-equal-list (e m)
  (declare (xargs :measure (acl2-count m)))
  (cond ((atom m) 0)
	((equal e (car m))
	 (1+ (count-bag-equal-list e (cdr m))))
	(t (count-bag-equal-list e (cdr m)))))

(defthm count-include-list
  (equal (count-bag-equal-list e1 (cons e2 m))
	 (if (equal e1 e2)
	     (1+ (count-bag-equal-list e1 m))
	     (count-bag-equal-list e1 m))))

(definstance-*multiset*
  ((select car)
   (reduct cdr)
   (include cons)
   (empty atom)
   (measure acl2-count)
   (equiv equal)
   (count-bag-equiv count-bag-equal-list))
  "-list")

;;;----------------------------------------------------------------------------
;;;
;;; A working example:
;;;
;;;----------------------------------------------------------------------------

#|

(defconst *ma-list* '(a a b b c))

(defconst *mb-list* '(b c c b c))

(pe 'union-bag-equiv-list)
;; (DEFUN UNION-BAG-EQUIV-LIST (M1 M2)
;;   (DECLARE (XARGS :MEASURE (ACL2-COUNT M1)))
;;   (COND ((ATOM M1) M2)
;; 	   (T (CONS (CAR M1)
;; 		    (UNION-BAG-EQUIV-LIST (CDR M1) M2)))))

(pe 'inter-bag-equiv-greatest-list)
;; (DEFTHM INTER-BAG-EQUIV-GREATEST-LIST
;;   (IMPLIES (AND (SUB-BAG-EQUIV-LIST M1 M2)
;; 		   (SUB-BAG-EQUIV-LIST M1 M3))
;; 	      (SUB-BAG-EQUIV-LIST M1 (INTER-BAG-EQUIV-LIST M2 M3)))
;;   ...)

(union-bag-equiv-list *ma-list* *mb-list*)
;; (A A B B C B C C B C)

(inter-bag-equiv-list *ma-list* *mb-list*)
;; (B B C)

(unimin-bag-equiv-list *ma-list* *mb-list*)
;; (A A B B C C C)

(diff-bag-equiv-list *ma-list* *mb-list*)
;; (A A)

|#

;;;============================================================================
