;;;============================================================================
;;;
;;; Finite multiset generic theory.
;;;
;;;============================================================================

#| Certification code:

(certify-book "generic-multiset")

|#

(in-package "ACL2")

;;;----------------------------------------------------------------------------
;;;
;;; A finite multiset generic model:
;;;
;;;----------------------------------------------------------------------------

(encapsulate
 (((select *) => *)
  ((reduct *) => *)
  ((include * *) => *)
  ((empty *) => *)
  ((measure *) => *)
  ((equiv * *) => *))

 (local
  (defun select (m)
    (car m)))

 (local
  (defun reduct (m)
    (cdr m)))

 (local
  (defun include (e m)
    (cons e m)))

 (local
  (defun empty (m)
    (atom m)))

 (local
  (defun measure (m)
    (acl2-count m)))

 (defthm o-p-measure
   (o-p (measure m)))

 (defthm reduct-measure
   (implies (not (empty m))
	    (o< (measure (reduct m)) (measure m))))

 (local
  (defun equiv (e1 e2)
    (equal e1 e2)))

 (defequiv equiv)

 (defun count-bag-equiv (e m)
   (declare (xargs :measure (measure m)))
   (cond ((empty m) 0)
	 ((equiv e (select m))
	  (1+ (count-bag-equiv e (reduct m))))
	 (t (count-bag-equiv e (reduct m)))))

; The following was added by Matt Kaufmann after ACL2 Version 3.4 because of
; a soundness bug fix; see ``subversive'' in :doc note-3-5.
 (defthm count-bag-equiv-type
   (natp (count-bag-equiv e m))
   :rule-classes :type-prescription)

 (defthm count-include
   (equal (count-bag-equiv e1 (include e2 m))
	  (if (equiv e1 e2)
	      (1+ (count-bag-equiv e1 m))
	      (count-bag-equiv e1 m))))

 )

(defun count-bag-equiv-induct (e m)
  (declare (xargs :measure (measure m)))
  (cond ((empty m) t)
	((equiv e (select m))
	 (count-bag-equiv-induct e (reduct m)))
	(t (count-bag-equiv-induct e (reduct m)))))

(defthm count-bag-equiv-induction t
  :rule-classes
  ((:induction :pattern (count-bag-equiv e m)
	       :condition t
	       :scheme (count-bag-equiv-induct e m))))

(defcong equiv equal (count-bag-equiv e m) 1)

;;;----------------------------------------------------------------------------
;;;
;;; Multiset membership relation:
;;;
;;;----------------------------------------------------------------------------

(defun member-bag-equiv (e m)
  (declare (xargs :measure (measure m)))
  (cond ((empty m) nil)
	((equiv e (select m)) t)
	(t (member-bag-equiv e (reduct m)))))

(defcong equiv iff (member-bag-equiv e m) 1)

(defthm member-bag-equiv-count->=-1
  (iff (member-bag-equiv e m)
       (>= (count-bag-equiv e m) 1))
  :rule-classes
  ((:definition

; Added by Matt Kaufmann, 3/25/06, after v2-9-4 in order to accommodate new
; check that equivalence relation for a definition rule must be 'equal if we
; are to expand with it.

    :install-body nil)))

;;;----------------------------------------------------------------------------
;;;
;;; Removing one occurrence from a multiset:
;;;
;;;----------------------------------------------------------------------------

(defun remove-one-bag-equiv (e m)
  (declare (xargs :measure (measure m)))
  (cond ((empty m) m)
	((equiv e (select m)) (reduct m))
	(t (include (select m)
		    (remove-one-bag-equiv e (reduct m))))))

(defcong equiv equal (remove-one-bag-equiv e m) 1)

(defthm remove-one-count
  (equal (count-bag-equiv e1 (remove-one-bag-equiv e2 m))
	 (if (and (member-bag-equiv e2 m)
		  (equiv e1 e2))
	     (1- (count-bag-equiv e1 m))
	     (count-bag-equiv e1 m))))

;;;----------------------------------------------------------------------------
;;;
;;; Sub-multiset relation:
;;;
;;;----------------------------------------------------------------------------

(defun sub-bag-equiv (m1 m2)
  (declare (xargs :measure (measure m1)))
  (cond ((empty m1) t)
	((member-bag-equiv (select m1) m2)
	 (sub-bag-equiv (reduct m1)
			(remove-one-bag-equiv (select m1) m2)))
	(t nil)))

(defthm sub-bag-equiv-reflexive
  (sub-bag-equiv m m))

(defthm sub-bag-equiv-count
  (implies (sub-bag-equiv m1 m2)
    (<= (count-bag-equiv e m1) (count-bag-equiv e m2)))
  :rule-classes :linear)

;;; A useful strategy to prove the sub-multiset relation:

(encapsulate
 (((sub-bag-strategy-m1) => *)
  ((sub-bag-strategy-m2) => *)
  ((sub-bag-strategy-hyp) => *))

 (local (defun sub-bag-strategy-m1 () nil))

 (local (defun sub-bag-strategy-m2 () nil))

 (local (defun sub-bag-strategy-hyp () t))

 (defthm sub-bag-equiv-strategy-constraint
   (implies (sub-bag-strategy-hyp)
     (<= (count-bag-equiv strategy-e (sub-bag-strategy-m1))
	 (count-bag-equiv strategy-e (sub-bag-strategy-m2))))))

(encapsulate
 ()

 (local
  (defun bag-sub-bag-equiv (m1 m2 m3)
    (declare (xargs :measure (measure m1)))
    (cond ((empty m1) t)
	  ((<= (count-bag-equiv (select m1) m2)
	       (count-bag-equiv (select m1) m3))
	   (bag-sub-bag-equiv (reduct m1) m2 m3))
	  (t nil))))

 (local
  (defthm bag-sub-bag-equiv-remove-one
    (implies (bag-sub-bag-equiv m1 m2 m3)
      (bag-sub-bag-equiv m1 (remove-one-bag-equiv e m2)
			 (remove-one-bag-equiv e m3)))))

 (local
  (defthm bag-sub-bag-equiv-sub-bag
    (implies (bag-sub-bag-equiv m1 m1 m2)
      (sub-bag-equiv m1 m2))
    :hints (("Goal" :induct (sub-bag-equiv m1 m2))
	    ("Subgoal *1/2" :use (:instance bag-sub-bag-equiv-remove-one
					    (m1 (reduct m1))
					    (e (select m1))
					    (m2 m1)
					    (m3 m2))))))

 (local
  (defthm sub-bag-equiv-strategy-aux
    (implies (sub-bag-strategy-hyp)
      (bag-sub-bag-equiv m (sub-bag-strategy-m1) (sub-bag-strategy-m2)))))

 (defthm sub-bag-equiv-strategy
   (implies (sub-bag-strategy-hyp)
     (sub-bag-equiv (sub-bag-strategy-m1) (sub-bag-strategy-m2))))

)

(defun components-equal-sub-bag (form)
  (declare (xargs :mode :program))

  (case-match form

	      (('IMPLIES form-hyp
			 ('EQUAL-BAG-EQUIV form-m1 form-m2))
	       (mv form-hyp form-m1 form-m2))

	      (('EQUAL-BAG-EQUIV form-m1 form-m2)
	       (mv t form-m1 form-m2))

	      (('IMPLIES form-hyp
			 ('SUB-BAG-EQUIV form-m1 form-m2))
	       (mv form-hyp form-m1 form-m2))

	      (('SUB-BAG-EQUIV form-m1 form-m2)
	       (mv t form-m1 form-m2))

	      (& (mv nil nil nil))))

(defun defstrategy-sub-bag-hint (id clause world)
  (declare (xargs :mode :program)
	   (ignore id world))

  (mv-let (form-hyp form-m1 form-m2)
	  (components-equal-sub-bag (first clause))
	  (if form-hyp
	      `(:use (:functional-instance
		      sub-bag-equiv-strategy
		      (sub-bag-strategy-m1 (lambda () ,form-m1))
		      (sub-bag-strategy-m2 (lambda () ,form-m2))
		      (sub-bag-strategy-hyp (lambda () ,form-hyp))))
	      nil)))

;;; The first use of the above strategy:

(defthm sub-bag-equiv-transitive
  (implies (and (sub-bag-equiv m1 m2)
		(sub-bag-equiv m2 m3))
    (sub-bag-equiv m1 m3))
  :hints (defstrategy-sub-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Multiset equality relation:
;;;
;;;----------------------------------------------------------------------------

(defun equal-bag-equiv (m1 m2)
  (and (sub-bag-equiv m1 m2)
       (sub-bag-equiv m2 m1)))

(defequiv equal-bag-equiv)

(defcong equal-bag-equiv iff (member-bag-equiv e m) 2)

(defcong equal-bag-equiv equal (count-bag-equiv e m) 2)

(defcong equal-bag-equiv iff (sub-bag-equiv m1 m2) 1)

(defcong equal-bag-equiv iff (sub-bag-equiv m1 m2) 2)

;;; A useful strategy to check multiset equality

(encapsulate
 (((equal-bag-strategy-m1) => *)
  ((equal-bag-strategy-m2) => *)
  ((equal-bag-strategy-hyp) => *))

 (local (defun equal-bag-strategy-m1 () nil))

 (local (defun equal-bag-strategy-m2 () nil))

 (local (defun equal-bag-strategy-hyp () t))

 (defthm equal-bag-equiv-strategy-constraint
   (implies (equal-bag-strategy-hyp)
     (equal (count-bag-equiv strategy-e (equal-bag-strategy-m1))
	    (count-bag-equiv strategy-e (equal-bag-strategy-m2))))))

(encapsulate
 ()

 (local
  (defthm equal-bag-equiv-strategy-aux-1
    (implies (equal-bag-strategy-hyp)
      (sub-bag-equiv (equal-bag-strategy-m1)
		     (equal-bag-strategy-m2)))
    :hints (defstrategy-sub-bag-hint)))

 (local
  (defthm equal-bag-equiv-strategy-aux-2
    (implies (equal-bag-strategy-hyp)
      (sub-bag-equiv (equal-bag-strategy-m2)
		     (equal-bag-strategy-m1)))
    :hints (defstrategy-sub-bag-hint)))

 (defthm equal-bag-equiv-strategy
   (implies (equal-bag-strategy-hyp)
     (equal-bag-equiv (equal-bag-strategy-m1)
		      (equal-bag-strategy-m2))))

)

(defun defstrategy-equal-bag-hint (id clause world)
  (declare (xargs :mode :program)
	   (ignore id world))

  (mv-let (form-hyp form-m1 form-m2)
	  (components-equal-sub-bag (first clause))
	  (if form-hyp
	      `(:use (:functional-instance
		      equal-bag-equiv-strategy
		      (equal-bag-strategy-m1 (lambda () ,form-m1))
		      (equal-bag-strategy-m2 (lambda () ,form-m2))
		      (equal-bag-strategy-hyp (lambda () ,form-hyp))))
	      nil)))

;;; The first use of the above strategy

(defcong equal-bag-equiv equal-bag-equiv (remove-one-bag-equiv e m) 2
  :hints (defstrategy-equal-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Multiset union:
;;;
;;;----------------------------------------------------------------------------

(defun union-bag-equiv (m1 m2)
  (declare (xargs :measure (measure m1)))
  (cond ((empty m1) m2)
	(t (include (select m1)
		    (union-bag-equiv (reduct m1) m2)))))

(defthm count-union-bag-equiv
  (equal (count-bag-equiv e (union-bag-equiv m1 m2))
	 (+ (count-bag-equiv e m1)
	    (count-bag-equiv e m2))))

(defcong equal-bag-equiv equal-bag-equiv (union-bag-equiv m1 m2) 1
   :hints (defstrategy-equal-bag-hint))

(defcong equal-bag-equiv equal-bag-equiv (union-bag-equiv m1 m2) 2
   :hints (defstrategy-equal-bag-hint))

(defthm union-bag-equiv-conmutative
  (equal-bag-equiv (union-bag-equiv m2 m1)
		   (union-bag-equiv m1 m2))
  :hints (defstrategy-equal-bag-hint))

(defthm union-bag-equiv-associative
  (equal-bag-equiv (union-bag-equiv m1 (union-bag-equiv m2 m3))
		   (union-bag-equiv (union-bag-equiv m1 m2) m3))
  :hints (defstrategy-equal-bag-hint))

(defthm sub-union-bag-equiv-1
  (sub-bag-equiv m1 (union-bag-equiv m1 m2))
  :hints (defstrategy-sub-bag-hint))

(defthm sub-union-bag-equiv-2
  (sub-bag-equiv m2 (union-bag-equiv m1 m2))
  :hints (defstrategy-sub-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Multiset intersection:
;;;
;;;----------------------------------------------------------------------------

(defun inter-bag-equiv (m1 m2)
  (declare (xargs :measure (measure m1)))
  (cond ((empty m1) m1)
	((member-bag-equiv (select m1) m2)
	 (include (select m1)
		  (inter-bag-equiv (reduct m1)
				   (remove-one-bag-equiv (select m1) m2))))
	(t (inter-bag-equiv (reduct m1) m2))))

(defthm count-inter-bag-equiv
  (equal (count-bag-equiv e (inter-bag-equiv m1 m2))
	 (min (count-bag-equiv e m1)
	      (count-bag-equiv e m2))))

(defcong equal-bag-equiv equal-bag-equiv (inter-bag-equiv m1 m2) 1
  :hints (defstrategy-equal-bag-hint))

(defcong equal-bag-equiv equal-bag-equiv (inter-bag-equiv m1 m2) 2
  :hints (defstrategy-equal-bag-hint))

(defthm inter-bag-equiv-idempotent
  (equal-bag-equiv (inter-bag-equiv m m) m)
  :hints (defstrategy-equal-bag-hint))

(defthm inter-bag-equiv-conmutative
  (equal-bag-equiv (inter-bag-equiv m2 m1)
		   (inter-bag-equiv m1 m2))
  :hints (defstrategy-equal-bag-hint))

(defthm inter-bag-equiv-associative
  (equal-bag-equiv (inter-bag-equiv m1 (inter-bag-equiv m2 m3))
		   (inter-bag-equiv (inter-bag-equiv m1 m2) m3))
  :hints (defstrategy-equal-bag-hint))

(defthm sub-inter-bag-equiv-1
  (sub-bag-equiv (inter-bag-equiv m1 m2) m1)
  :hints (defstrategy-sub-bag-hint))

(defthm sub-inter-bag-equiv-2
  (sub-bag-equiv (inter-bag-equiv m1 m2) m2)
  :hints (defstrategy-sub-bag-hint))

(defthm inter-bag-equiv-greatest
  (implies (and (sub-bag-equiv m1 m2)
		(sub-bag-equiv m1 m3))
    (sub-bag-equiv m1 (inter-bag-equiv m2 m3)))
  :hints (defstrategy-sub-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Multiset minimal union:
;;;
;;;----------------------------------------------------------------------------

(defun unimin-bag-equiv (m1 m2)
  (declare (xargs :measure (measure m1)))
  (cond ((empty m1) m2)
	((member-bag-equiv (select m1) m2)
	 (include (select m1)
		  (unimin-bag-equiv (reduct m1)
				    (remove-one-bag-equiv (select m1) m2))))
	(t (include (select m1) (unimin-bag-equiv (reduct m1) m2)))))

(defthm count-unimin-bag-equiv
  (equal (count-bag-equiv e (unimin-bag-equiv m1 m2))
	 (max (count-bag-equiv e m1)
	      (count-bag-equiv e m2))))

(defcong equal-bag-equiv equal-bag-equiv (unimin-bag-equiv m1 m2) 1
  :hints (defstrategy-equal-bag-hint))

(defcong equal-bag-equiv equal-bag-equiv (unimin-bag-equiv m1 m2) 2
  :hints (defstrategy-equal-bag-hint))

(defthm unimin-bag-equiv-idempotent
  (equal-bag-equiv (unimin-bag-equiv m m) m)
  :hints (defstrategy-equal-bag-hint))

(defthm unimin-bag-equiv-conmutative
  (equal-bag-equiv (unimin-bag-equiv m2 m1)
		   (unimin-bag-equiv m1 m2))
  :hints (defstrategy-equal-bag-hint))

(defthm unimin-bag-equiv-associative
  (equal-bag-equiv (unimin-bag-equiv m1 (unimin-bag-equiv m2 m3))
		   (unimin-bag-equiv (unimin-bag-equiv m1 m2) m3))
  :hints (defstrategy-equal-bag-hint))

(defthm sub-unimin-bag-equiv-1
  (sub-bag-equiv m1 (unimin-bag-equiv m1 m2))
  :hints (defstrategy-sub-bag-hint))

(defthm sub-unimin-bag-equiv-2
  (sub-bag-equiv m2 (unimin-bag-equiv m1 m2))
  :hints (defstrategy-sub-bag-hint))

(defthm unimin-bag-equiv-least
  (implies (and (sub-bag-equiv m1 m3)
		(sub-bag-equiv m2 m3))
    (sub-bag-equiv (unimin-bag-equiv m1 m2) m3))
  :hints (defstrategy-sub-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Multiset difference:
;;;
;;;----------------------------------------------------------------------------

(defun diff-bag-equiv (m1 m2)
  (declare (xargs :measure (measure m2)))
  (cond ((empty m2) m1)
	(t (diff-bag-equiv (remove-one-bag-equiv (select m2) m1)
			   (reduct m2)))))

(defthm count-bag-equiv-diff-bag
  (equal (count-bag-equiv e (diff-bag-equiv m1 m2))
	 (if (> (- (count-bag-equiv e m1)
		   (count-bag-equiv e m2)) 0)
	     (- (count-bag-equiv e m1)
		(count-bag-equiv e m2))
	     0)))

(defcong equal-bag-equiv equal-bag-equiv (diff-bag-equiv m1 m2) 1
  :hints (defstrategy-equal-bag-hint))

(defcong equal-bag-equiv equal-bag-equiv (diff-bag-equiv m1 m2) 2
  :hints (defstrategy-equal-bag-hint))

(defthm diff-union-1-equal-bag-equiv
  (equal-bag-equiv (diff-bag-equiv (union-bag-equiv l1 l2)
				   (union-bag-equiv l1 l3))
		   (diff-bag-equiv l2 l3))
  :hints (defstrategy-equal-bag-hint))

(defthm diff-union-2-equal-bag-equiv
  (equal-bag-equiv (diff-bag-equiv (union-bag-equiv l2 l1)
				   (union-bag-equiv l3 l1))
		   (diff-bag-equiv l2 l3))
  :hints (defstrategy-equal-bag-hint))

;;;----------------------------------------------------------------------------
;;;
;;; Defining the generic theory:
;;;
;;;----------------------------------------------------------------------------

(include-book "generic-theory")

#|

(get-event-lst
 '(member-bag-equiv
   EQUIV-IMPLIES-IFF-MEMBER-BAG-EQUIV-1
   remove-one-bag-equiv
   EQUIV-IMPLIES-EQUAL-REMOVE-ONE-BAG-EQUIV-1
   sub-bag-equiv
   sub-bag-equiv-reflexive
   sub-bag-equiv-transitive
   equal-bag-equiv
   EQUAL-BAG-EQUIV-IS-AN-EQUIVALENCE
   EQUAL-BAG-EQUIV-IMPLIES-IFF-MEMBER-BAG-EQUIV-2
   EQUAL-BAG-EQUIV-IMPLIES-IFF-SUB-BAG-EQUIV-1
   EQUAL-BAG-EQUIV-IMPLIES-IFF-SUB-BAG-EQUIV-2
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-REMOVE-ONE-BAG-EQUIV-2
   union-bag-equiv
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNION-BAG-EQUIV-1
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNION-BAG-EQUIV-2
   union-bag-equiv-conmutative
   union-bag-equiv-associative
   sub-union-bag-equiv-1
   sub-union-bag-equiv-2
   inter-bag-equiv
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-INTER-BAG-EQUIV-1
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-INTER-BAG-EQUIV-2
   inter-bag-equiv-idempotent
   inter-bag-equiv-conmutative
   inter-bag-equiv-associative
   sub-inter-bag-equiv-1
   sub-inter-bag-equiv-2
   inter-bag-equiv-greatest
   unimin-bag-equiv
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNIMIN-BAG-EQUIV-1
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNIMIN-BAG-EQUIV-2
   unimin-bag-equiv-idempotent
   unimin-bag-equiv-conmutative
   unimin-bag-equiv-associative
   sub-unimin-bag-equiv-1
   sub-unimin-bag-equiv-2
   unimin-bag-equiv-least
   diff-bag-equiv
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-DIFF-BAG-EQUIV-1
   EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-DIFF-BAG-EQUIV-2
   diff-union-1-equal-bag-equiv
   diff-union-2-equal-bag-equiv))

|#

(defconst *multiset*
  '((DEFUN MEMBER-BAG-EQUIV (E M)
      (DECLARE (XARGS :MEASURE (MEASURE M)))
      (COND ((EMPTY M) NIL)
	    ((EQUIV E (SELECT M)) T)
	    (T (MEMBER-BAG-EQUIV E (REDUCT M)))))
    (DEFTHM EQUIV-IMPLIES-IFF-MEMBER-BAG-EQUIV-1
      (IMPLIES (EQUIV E E-EQUIV)
	       (IFF (MEMBER-BAG-EQUIV E M)
		    (MEMBER-BAG-EQUIV E-EQUIV M)))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFUN REMOVE-ONE-BAG-EQUIV (E M)
      (DECLARE (XARGS :MEASURE (MEASURE M)))
      (COND ((EMPTY M) M)
	    ((EQUIV E (SELECT M)) (REDUCT M))
	    (T (INCLUDE (SELECT M)
			(REMOVE-ONE-BAG-EQUIV E (REDUCT M))))))
    (DEFTHM EQUIV-IMPLIES-EQUAL-REMOVE-ONE-BAG-EQUIV-1
      (IMPLIES (EQUIV E E-EQUIV)
	       (EQUAL (REMOVE-ONE-BAG-EQUIV E M)
		      (REMOVE-ONE-BAG-EQUIV E-EQUIV M)))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFUN SUB-BAG-EQUIV (M1 M2)
      (DECLARE (XARGS :MEASURE (MEASURE M1)))
      (COND ((EMPTY M1) T)
	    ((MEMBER-BAG-EQUIV (SELECT M1) M2)
	     (SUB-BAG-EQUIV (REDUCT M1)
			    (REMOVE-ONE-BAG-EQUIV (SELECT M1) M2)))
	    (T NIL)))
    (DEFTHM SUB-BAG-EQUIV-REFLEXIVE
      (SUB-BAG-EQUIV M M))
    (DEFTHM SUB-BAG-EQUIV-TRANSITIVE
      (IMPLIES (AND (SUB-BAG-EQUIV M1 M2)
		    (SUB-BAG-EQUIV M2 M3))
	       (SUB-BAG-EQUIV M1 M3))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFUN EQUAL-BAG-EQUIV (M1 M2)
      (AND (SUB-BAG-EQUIV M1 M2)
	   (SUB-BAG-EQUIV M2 M1)))
    (DEFTHM EQUAL-BAG-EQUIV-IS-AN-EQUIVALENCE
      (AND (BOOLEANP (EQUAL-BAG-EQUIV X Y))
	   (EQUAL-BAG-EQUIV X X)
	   (IMPLIES (EQUAL-BAG-EQUIV X Y)
		    (EQUAL-BAG-EQUIV Y X))
	   (IMPLIES (AND (EQUAL-BAG-EQUIV X Y)
			 (EQUAL-BAG-EQUIV Y Z))
		    (EQUAL-BAG-EQUIV X Z)))
      :RULE-CLASSES (:EQUIVALENCE))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-IFF-MEMBER-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M M-EQUIV)
	       (IFF (MEMBER-BAG-EQUIV E M)
		    (MEMBER-BAG-EQUIV E M-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-IFF-SUB-BAG-EQUIV-1
      (IMPLIES (EQUAL-BAG-EQUIV M1 M1-EQUIV)
	       (IFF (SUB-BAG-EQUIV M1 M2)
		    (SUB-BAG-EQUIV M1-EQUIV M2)))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-IFF-SUB-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M2 M2-EQUIV)
	       (IFF (SUB-BAG-EQUIV M1 M2)
		    (SUB-BAG-EQUIV M1 M2-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-REMOVE-ONE-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M M-EQUIV)
	       (EQUAL-BAG-EQUIV (REMOVE-ONE-BAG-EQUIV E M)
				(REMOVE-ONE-BAG-EQUIV E M-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFUN UNION-BAG-EQUIV (M1 M2)
      (DECLARE (XARGS :MEASURE (MEASURE M1)))
      (COND ((EMPTY M1) M2)
	    (T (INCLUDE (SELECT M1)
			(UNION-BAG-EQUIV (REDUCT M1) M2)))))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNION-BAG-EQUIV-1
      (IMPLIES (EQUAL-BAG-EQUIV M1 M1-EQUIV)
	       (EQUAL-BAG-EQUIV (UNION-BAG-EQUIV M1 M2)
				(UNION-BAG-EQUIV M1-EQUIV M2)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNION-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M2 M2-EQUIV)
	       (EQUAL-BAG-EQUIV (UNION-BAG-EQUIV M1 M2)
				(UNION-BAG-EQUIV M1 M2-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM UNION-BAG-EQUIV-CONMUTATIVE
      (EQUAL-BAG-EQUIV (UNION-BAG-EQUIV M2 M1)
		       (UNION-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM UNION-BAG-EQUIV-ASSOCIATIVE
      (EQUAL-BAG-EQUIV (UNION-BAG-EQUIV M1 (UNION-BAG-EQUIV M2 M3))
		       (UNION-BAG-EQUIV (UNION-BAG-EQUIV M1 M2)
					M3))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM SUB-UNION-BAG-EQUIV-1
      (SUB-BAG-EQUIV M1 (UNION-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFTHM SUB-UNION-BAG-EQUIV-2
      (SUB-BAG-EQUIV M2 (UNION-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFUN INTER-BAG-EQUIV (M1 M2)
      (DECLARE (XARGS :MEASURE (MEASURE M1)))
      (COND ((EMPTY M1) M1)
	    ((MEMBER-BAG-EQUIV (SELECT M1) M2)
	     (INCLUDE (SELECT M1)
		      (INTER-BAG-EQUIV (REDUCT M1)
				       (REMOVE-ONE-BAG-EQUIV (SELECT M1) M2))))
	    (T (INTER-BAG-EQUIV (REDUCT M1) M2))))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-INTER-BAG-EQUIV-1
      (IMPLIES (EQUAL-BAG-EQUIV M1 M1-EQUIV)
	       (EQUAL-BAG-EQUIV (INTER-BAG-EQUIV M1 M2)
				(INTER-BAG-EQUIV M1-EQUIV M2)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-INTER-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M2 M2-EQUIV)
	       (EQUAL-BAG-EQUIV (INTER-BAG-EQUIV M1 M2)
				(INTER-BAG-EQUIV M1 M2-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM INTER-BAG-EQUIV-IDEMPOTENT
      (EQUAL-BAG-EQUIV (INTER-BAG-EQUIV M M)
		       M)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM INTER-BAG-EQUIV-CONMUTATIVE
      (EQUAL-BAG-EQUIV (INTER-BAG-EQUIV M2 M1)
		       (INTER-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM INTER-BAG-EQUIV-ASSOCIATIVE
      (EQUAL-BAG-EQUIV (INTER-BAG-EQUIV M1 (INTER-BAG-EQUIV M2 M3))
		       (INTER-BAG-EQUIV (INTER-BAG-EQUIV M1 M2)
					M3))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM SUB-INTER-BAG-EQUIV-1
      (SUB-BAG-EQUIV (INTER-BAG-EQUIV M1 M2)
		     M1)
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFTHM SUB-INTER-BAG-EQUIV-2
      (SUB-BAG-EQUIV (INTER-BAG-EQUIV M1 M2)
		     M2)
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFTHM INTER-BAG-EQUIV-GREATEST
      (IMPLIES (AND (SUB-BAG-EQUIV M1 M2)
		    (SUB-BAG-EQUIV M1 M3))
	       (SUB-BAG-EQUIV M1 (INTER-BAG-EQUIV M2 M3)))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFUN UNIMIN-BAG-EQUIV (M1 M2)
      (DECLARE (XARGS :MEASURE (MEASURE M1)))
      (COND ((EMPTY M1) M2)
	    ((MEMBER-BAG-EQUIV (SELECT M1) M2)
	     (INCLUDE
	      (SELECT M1)
	      (UNIMIN-BAG-EQUIV (REDUCT M1)
				(REMOVE-ONE-BAG-EQUIV (SELECT M1) M2))))
	    (T (INCLUDE (SELECT M1)
			(UNIMIN-BAG-EQUIV (REDUCT M1) M2)))))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNIMIN-BAG-EQUIV-1
      (IMPLIES (EQUAL-BAG-EQUIV M1 M1-EQUIV)
	       (EQUAL-BAG-EQUIV (UNIMIN-BAG-EQUIV M1 M2)
				(UNIMIN-BAG-EQUIV M1-EQUIV M2)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-UNIMIN-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M2 M2-EQUIV)
	       (EQUAL-BAG-EQUIV (UNIMIN-BAG-EQUIV M1 M2)
				(UNIMIN-BAG-EQUIV M1 M2-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM UNIMIN-BAG-EQUIV-IDEMPOTENT
      (EQUAL-BAG-EQUIV (UNIMIN-BAG-EQUIV M M)
		       M)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM UNIMIN-BAG-EQUIV-CONMUTATIVE
      (EQUAL-BAG-EQUIV (UNIMIN-BAG-EQUIV M2 M1)
		       (UNIMIN-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM UNIMIN-BAG-EQUIV-ASSOCIATIVE
      (EQUAL-BAG-EQUIV (UNIMIN-BAG-EQUIV M1 (UNIMIN-BAG-EQUIV M2 M3))
		       (UNIMIN-BAG-EQUIV (UNIMIN-BAG-EQUIV M1 M2)
					 M3))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM SUB-UNIMIN-BAG-EQUIV-1
      (SUB-BAG-EQUIV M1 (UNIMIN-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFTHM SUB-UNIMIN-BAG-EQUIV-2
      (SUB-BAG-EQUIV M2 (UNIMIN-BAG-EQUIV M1 M2))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFTHM UNIMIN-BAG-EQUIV-LEAST
      (IMPLIES (AND (SUB-BAG-EQUIV M1 M3)
		    (SUB-BAG-EQUIV M2 M3))
	       (SUB-BAG-EQUIV (UNIMIN-BAG-EQUIV M1 M2)
			      M3))
      :HINTS (DEFSTRATEGY-SUB-BAG-HINT))
    (DEFUN DIFF-BAG-EQUIV (M1 M2)
      (DECLARE (XARGS :MEASURE (MEASURE M2)))
      (COND ((EMPTY M2) M1)
	    (T (DIFF-BAG-EQUIV (REMOVE-ONE-BAG-EQUIV (SELECT M2) M1)
			       (REDUCT M2)))))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-DIFF-BAG-EQUIV-1
      (IMPLIES (EQUAL-BAG-EQUIV M1 M1-EQUIV)
	       (EQUAL-BAG-EQUIV (DIFF-BAG-EQUIV M1 M2)
				(DIFF-BAG-EQUIV M1-EQUIV M2)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM EQUAL-BAG-EQUIV-IMPLIES-EQUAL-BAG-EQUIV-DIFF-BAG-EQUIV-2
      (IMPLIES (EQUAL-BAG-EQUIV M2 M2-EQUIV)
	       (EQUAL-BAG-EQUIV (DIFF-BAG-EQUIV M1 M2)
				(DIFF-BAG-EQUIV M1 M2-EQUIV)))
      :RULE-CLASSES (:CONGRUENCE)
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM DIFF-UNION-1-EQUAL-BAG-EQUIV
      (EQUAL-BAG-EQUIV (DIFF-BAG-EQUIV (UNION-BAG-EQUIV L1 L2)
				       (UNION-BAG-EQUIV L1 L3))
		       (DIFF-BAG-EQUIV L2 L3))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT))
    (DEFTHM DIFF-UNION-2-EQUAL-BAG-EQUIV
      (EQUAL-BAG-EQUIV (DIFF-BAG-EQUIV (UNION-BAG-EQUIV L2 L1)
				       (UNION-BAG-EQUIV L3 L1))
		       (DIFF-BAG-EQUIV L2 L3))
      :HINTS (DEFSTRATEGY-EQUAL-BAG-HINT)))
  )

(make-generic-theory *multiset*)

;;;============================================================================
