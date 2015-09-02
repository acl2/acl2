; Alist-defthms.lisp - Theorems about functions in the theory of alists.;
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(include-book "alist-defuns")
(include-book "list-defuns")
(include-book "set-defuns")
(local (include-book "arithmetic/equalities" :dir :system))
(local (include-book "set-defthms"))


; ------------------------------------------------------------
; Equality Trichotomy
; ------------------------------------------------------------

; Rewrite the EQL and EQ versions of various functions to
; the EQUAL version. This way, we can build one set of rules about
; the EQUAL functions.

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc->assoc-equal
;   (equal (assoc x a)
;          (assoc-equal x a)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq->assoc-equal
;   (equal (assoc-eq x a)
;          (assoc-equal x a)))

(defthm bind->bind-equal
  (equal (bind x y a)
	 (bind-equal x y a)))

(defthm bind-eq->bind-equal
  (equal (bind-eq x y a)
	 (bind-equal x y a)))

(defthm bind-all->bind-all-equal
  (equal (bind-all x y a)
	 (bind-all-equal x y a)))

(defthm bind-all-eq->bind-all-equal
  (equal (bind-all-eq x y a)
	 (bind-all-equal x y a)))

(defthm bound?->bound?-equal
  (equal (bound? x a)
	 (bound?-equal x a)))

(defthm bound?-eq->bound?-equal
  (equal (bound?-eq x a)
	 (bound?-equal x a)))

(defthm binding->binding-equal
  (equal (binding x a)
	 (binding-equal x a)))

(defthm binding-eq->binding-equal
  (equal (binding-eq x a)
	 (binding-equal x a)))

(defthm all-bindings->all-bindings-equal
  (equal (all-bindings l a)
	 (all-bindings-equal l a)))

(defthm all-bindings-eq->all-bindings-equal
  (equal (all-bindings-eq l a)
	 (all-bindings-equal l a)))

(defthm all-bound?->all-bound?-equal
  (equal (all-bound? l a)
	 (all-bound?-equal l a)))

(defthm all-bound?-eq->all-bound?-equal
  (equal (all-bound?-eq l a)
	 (all-bound?-equal l a)))

(defthm rembind->rembind-equal
  (equal (rembind x a)
	 (rembind-equal x a)))

(defthm rembind-eq->rembind-equal
  (equal (rembind-eq x a)
	 (rembind-equal x a)))

(defthm rembind-all->rembind-all-equal
  (equal (rembind-all x a)
	 (rembind-all-equal x a)))

(defthm rembind-all-eq->rembind-all-equal
  (equal (rembind-all-eq x a)
	 (rembind-all-equal x a)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local (defthm member->member-equal
;          (equal (member x l)
;                 (member-equal x l))))

(defthm domain-restrict->domain-restrict-equal
  (equal (domain-restrict l a)
	 (domain-restrict-equal l a)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local (defthm member-eq->member-equal
;          (equal (member-eq x l)
;                 (member-equal x l))))

(defthm domain-restrict-eq->domain-restrict-equal
  (equal (domain-restrict-eq l a)
	 (domain-restrict-equal l a)))

(defthm bind-pairs->bind-pairs-equal
  (equal (bind-pairs pairs a)
	 (bind-pairs-equal pairs a)))

(defthm bind-pairs-eq->bind-pairs-equal
  (equal (bind-pairs-eq pairs a)
	 (bind-pairs-equal pairs a)))

(defthm collect-bound->collect-bound-equal
  (equal (collect-bound x a)
	 (collect-bound-equal x a)))

(defthm collect-bound-eq->collect-bound-equal
  (equal (collect-bound-eq x a)
	 (collect-bound-equal x a)))

(defthm alist-compose-domain->alist-compose-domain-equal
  (equal (alist-compose-domain dom a1 a2)
	 (alist-compose-domain-equal dom a1 a2)))

(defthm alist-compose-domain-eq->alist-compose-domain-equal
  (equal (alist-compose-domain-eq dom a1 a2)
	 (alist-compose-domain-equal dom a1 a2)))

; ------------------------------------------------------------
; TYPE lemmas
; ------------------------------------------------------------

(defthm assoc-equal-consp-or-nil
  (implies (alistp a)
	   (or (consp (assoc-equal x a))
	       (equal (assoc-equal x a) nil)))
  :rule-classes :type-prescription)

(defthm true-listp-domain
  (true-listp (domain a))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-listp-domain
  (implies (eqlable-alistp a)
	   (eqlable-listp (domain a))))

(defthm symbol-listp-domain
  (implies (symbol-alistp a)
	   (symbol-listp (domain a))))

(defthm true-listp-range
  (true-listp (range a))
  :rule-classes (:rewrite :type-prescription))

; We prove ALISTP, EQLABLE-ALISTP and SYMBOL-ALISTP lemmas
; for each alist constructor. These will be used in guard proofs.

(defthm alistp-acons
  (implies (alistp a)
	   (alistp (acons x y a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-acons
  (implies (and (eqlablep x)
		(eqlable-alistp a))
	   (eqlable-alistp (acons x y a))))

(defthm symbol-alistp-acons
  (implies (and (symbolp x)
		(symbol-alistp a))
	   (symbol-alistp (acons x y a))))



(defthm alistp-append
  (implies (and (alistp a1)
		(alistp a2))
	   (alistp (append a1 a2))))

(defthm eqlable-alistp-append
  (implies (and (eqlable-alistp a1)
		(eqlable-alistp a2))
	   (eqlable-alistp (append a1 a2))))

(defthm symbol-alistp-append
  (implies (and (symbol-alistp a1)
		(symbol-alistp a2))
	   (symbol-alistp (append a1 a2))))


(defthm alistp-bind-equal
  (implies (alistp a)
	   (alistp (bind-equal x y a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-bind-equal
  (implies (and (eqlablep x)
		(eqlable-alistp a))
	   (eqlable-alistp (bind-equal x y a))))

(defthm symbol-alistp-bind-equal
  (implies (and (symbolp x)
		(symbol-alistp a))
	   (symbol-alistp (bind-equal x y a))))


(defthm alistp-pairlis$
  (alistp (pairlis$ a b)))

(defthm eqlable-alistp-pairlis$
  (implies (eqlable-listp a)
	   (eqlable-alistp (pairlis$ a b))))

(defthm symbol-alistp-pairlis$
  (implies (symbol-listp a)
	   (symbol-alistp (pairlis$ a b))))



(defthm alistp-rembind-equal
  (implies (alistp a)
	   (alistp (rembind-equal x a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-rembind-equal
  (implies (eqlable-alistp a)
	   (eqlable-alistp (rembind-equal x a))))

(defthm symbol-alistp-rembind-equal
  (implies (symbol-alistp a)
	   (symbol-alistp (rembind-equal x a))))


(defthm alistp-bind-all-equal
  (implies (alistp a)
	   (alistp (bind-all-equal keys vals a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-bind-all-equal
  (implies (and (eqlable-listp keys)
		(eqlable-alistp a))
	   (eqlable-alistp (bind-all-equal keys vals a))))

(defthm symbol-alistp-bind-all-equal
  (implies (and (symbol-listp keys)
		(symbol-alistp a))
	   (symbol-alistp (bind-all-equal keys vals a))))



(defthm alistp-domain-restrict-equal
  (implies (alistp a)
	   (alistp (Domain-restrict-equal l a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-domain-restrict-equal
  (implies (eqlable-alistp a)
	   (eqlable-alistp (domain-restrict-equal l a))))

(defthm symbol-alistp-domain-restrict-equal
  (implies (symbol-alistp a)
	   (symbol-alistp (domain-restrict-equal l a))))



(defthm alistp-rembind-all-equal
  (implies (alistp a)
	   (alistp (rembind-all-equal keys a)))
  :rule-classes (:rewrite :type-prescription))

(defthm eqlable-alistp-rembind-all-equal
  (implies (and (eqlable-listp keys)
		(eqlable-alistp a))
	   (eqlable-alistp (rembind-all-equal keys a))))

(defthm symbol-alistp-rembind-all-equal
  (implies (and (symbol-listp keys)
		(symbol-alistp a))
	   (symbol-alistp (rembind-all-equal keys a))))


(defthm alistp-bind-pairs-equal
  (implies (alistp a)
	   (alistp (bind-pairs-equal pairs a))))

(defthm eqlable-alistp-bind-pairs-equal
  (implies (and (eqlable-alistp pairs)
		(eqlable-alistp a))
	   (eqlable-alistp (bind-pairs-equal pairs a))))

(defthm symbol-alistp-bind-pairs-equal
  (implies (and (symbol-alistp pairs)
		(symbol-alistp a))
	   (symbol-alistp (bind-pairs-equal pairs a))))


(local
 (defthm alistp-alist-compose-domain-equal
   (alistp (alist-compose-domain-equal dom a1 a2))))

(defthm alistp-alist-compose-equal
  (alistp (alist-compose-equal a1 a2))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm eqlable-alistp-alist-compose-domain-equal
   (implies (eqlable-listp dom)
	    (eqlable-alistp (alist-compose-domain-equal dom a1 a2)))))

(local
 (defthm eqlable-listp-strip-cars
  (implies (eqlable-alistp a)
	   (eqlable-listp (strip-cars a)))))

(defthm eqlable-alistp-alist-compose-equal
  (implies (eqlable-alistp a1)
	   (eqlable-alistp (alist-compose-equal a1 a2)))
  :rule-classes (:rewrite :type-prescription))


(local
 (defthm symbol-alistp-alist-compose-domain-equal
   (implies (symbol-listp dom)
	    (symbol-alistp (alist-compose-domain-equal dom a1 a2)))))

(local
 (defthm symbol-listp-strip-cars
  (implies (symbol-alistp a)
	   (symbol-listp (strip-cars a)))))

(defthm symbol-alistp-alist-compose-equal
  (implies (symbol-alistp a1)
	   (symbol-alistp (alist-compose-equal a1 a2)))
  :rule-classes (:rewrite :type-prescription))



(defthm eqlable-listp-collect-bound-equal
  (implies (eqlable-listp l)
	   (eqlable-listp (collect-bound-equal l a))))

(defthm symbol-listp-collect-bound-equal
  (implies (symbol-listp l)
	   (symbol-listp (collect-bound-equal l a))))

; ------------------------------------------------------------
; MEMBER-EQUAL
; ------------------------------------------------------------

(defthm member-equal-domain
  (implies (alistp a)
	   (iff (member-equal x (domain a))
		(bound?-equal x a)))
  :hints (("Goal" :induct (assoc-equal x a))))

(defthm subsetp-equal-domain
  (implies (alistp a)
	   (iff (subsetp-equal l (domain a))
		(all-bound?-equal l a)))
  :hints (("Goal" :in-theory (disable domain))))

(defthm member-equal-binding-equal-range
  (implies (bound?-equal x a)
	   (member-equal (binding-equal x a)
			 (range a)))
  :hints (("Goal" :induct (assoc-equal x a))))

; ------------------------------------------------------------
; POSITION facts
; ------------------------------------------------------------

;; Throughout the rest of this script, we'll take the strategy of
;; proving facts about POSITION by first proving the fact about XPOSITION.

(local
 (defun xposition-equal (x l)
   (declare (xargs :guard (and (true-listp l)
			       (or (symbolp x) (symbol-listp l)))))
   (cond ((endp l) nil)
	 ((eq x (car l)) 0)
	 (t (let ((N (xposition-equal x (cdr l))))
	      (and n (1+ n)))))))

(local
 (defthm position-equal-ac-equals-xposition-equal1
   (implies (integerp ac)
	    (iff (position-equal-ac x l ac)
		 (xposition-equal x l)))))

(local
 (defthm position-equal-ac-equal-xposition-equal2
   (implies (and (integerp ac)
		 (position-equal-ac x l ac))
	    (equal (position-equal-ac x l ac)
		   (+ (xposition-equal x l) ac)))))

(local
 (defthm position-equal-ac-iff-member-equal
   (implies (integerp ac)
	    (iff (position-equal-ac x l ac)
		 (member-equal x l)))))

(local
 (defthm member-equal-implies-xposition
   (implies (member-equal x l)
	    (xposition-equal x l))))

; ------------------------------------------------------------
; ASSOC-EQUAL
; ------------------------------------------------------------

(defthm assoc-equal-acons
  (equal (assoc-equal x (acons y z a))
	 (if (equal x y)
	     (cons y z)
	     (assoc-equal x a))))

(defthm assoc-equal-append
  (implies (alistp a1)
	   (equal (assoc-equal x (append a1 a2))
		  (or (assoc-equal x a1)
		      (assoc-equal x a2)))))

(defthm assoc-equal-bind-equal
  (equal (assoc-equal x (bind-equal y v a))
	 (if (equal x y)
	     (cons y v)
	     (assoc-equal x a))))
(local
 (defthm xassoc-equal-pairlis$
   (equal (assoc-equal x (pairlis$ a b))
	  (if (member-equal x a)
	      (cons x (nth (xposition-equal x a) b))
	    nil))))

(defthm assoc-equal-pairlis$
  (equal (assoc-equal x (pairlis$ a b))
	 (if (member-equal x a)
	     (cons x (nth (position-equal x a) b))
	   nil)))

(defthm assoc-equal-rembind-equal
  (equal (assoc-equal x (rembind-equal y a))
	 (and (not (equal x y))
	      (assoc-equal x a))))

(local
 (defthm xassoc-equal-bind-all-equal
   (equal (assoc-equal x (bind-all-equal keys vals a))
	  (if (member-equal x keys)
	      (if (< (xposition-equal x keys) (len vals))
		  (cons x (nth (xposition-equal x keys) vals))
		(assoc-equal x a))
	    (assoc-equal x a)))))

(defthm assoc-equal-bind-all-equal
  (equal (assoc-equal x (bind-all-equal keys vals a))
	 (if (member-equal x keys)
	     (if (< (position-equal x keys) (len vals))
		 (cons x (nth (position-equal x keys) vals))
	       (assoc-equal x a))
	   (assoc-equal x a)))
  :hints (("Goal" :do-not-induct t)))

(defthm assoc-equal-domain-restrict-equal
  (equal (assoc-equal x (domain-restrict-equal l a))
	 (if (member-equal x l)
	     (assoc-equal x a)
	   nil)))

(defthm assoc-equal-rembind-all-equal
  (equal (assoc-equal x (rembind-all-equal l a))
	 (if (member-equal x l)
	     nil
	   (assoc-equal x a))))

(defthm assoc-equal-bind-pairs-equal
  (implies (alistp pairs)
	   (equal (assoc-equal x (bind-pairs-equal pairs a))
		  (if (assoc-equal x pairs)
		      (assoc-equal x pairs)
		    (assoc-equal x a)))))

(local
 (defthm assoc-equal-alist-compose-domain1
   (implies (and (alistp a1)
		 (alistp a2)
		 (not (assoc-equal x a1)))
	    (not (assoc-equal x (alist-compose-domain-equal dom a1 a2))))))

(local
 (defthm assoc-equal-alist-compose-domain
   (implies (and (alistp a1)
		 (alistp a2))
	    (equal (assoc-equal x (alist-compose-domain-equal dom a1 a2))
		   (if (member-equal x dom)
		       (let ((pair1 (assoc-equal x a1)))
			 (if pair1
			     (let ((pair2 (assoc-equal (cdr pair1) a2)))
			       (if pair2
				   (cons x (cdr pair2))
				 nil))
			   nil))
		     nil)))))

(defthm assoc-equal-alist-compose-equal
  (implies (and (alistp a1)
		(alistp a2))
	   (equal (assoc-equal x (alist-compose-equal a1 a2))
		  (let ((pair1 (assoc-equal x a1)))
		    (if pair1
			(let ((pair2 (assoc-equal (cdr pair1) a2)))
			  (if pair2
			      (cons x (cdr pair2))
			    nil))
		      nil))))
  :hints (("Goal" :do-not-induct t :in-theory (disable domain))))

; ------------------------------------------------------------
; BINDING-EQUAL
; ------------------------------------------------------------

(defthm binding-equal-acons
  (equal (binding-equal x (acons y z a))
	 (if (equal x y)
	     z
	   (binding-equal x a))))

(defthm binding-equal-append
  (implies (alistp a1)
	   (equal (binding-equal x (append a1 a2))
		  (if (bound?-equal x a1)
		      (binding-equal x a1)
		    (binding-equal x a2)))))

(defthm binding-equal-bind-equal
  (equal (binding-equal x (bind-equal y v a))
	 (if (equal x y)
	     v
	     (binding-equal x a))))

(local
 (defthm xbinding-equal-pairlis$
   (equal (binding-equal x (pairlis$ a b))
	  (if (member-equal x a)
	      (nth (xposition-equal x a) b)
	    nil))
   :hints (("Goal" :induct t))))

(defthm binding-equal-pairlis$
  (equal (binding-equal x (pairlis$ a b))
	 (if (member-equal x a)
	     (nth (position-equal x a) b)
	     nil))
  :hints (("Goal" :do-not-induct t :in-theory (disable binding-equal))))

(defthm binding-equal-rembind-equal
  (equal (binding-equal x (rembind-equal y a))
	 (if (eq x y)
	     nil
	     (binding-equal x a)))
  :hints (("Goal" :induct t)))

(local
 (defthm xbinding-equal-bind-all-equal
   (equal (binding-equal x (bind-all-equal keys vals a))
	  (if (member-equal x keys)
	      (if (< (xposition-equal x keys) (len vals))
		  (nth (xposition-equal x keys) vals)
		(binding-equal x a))
	    (binding-equal x a)))
   :hints (("Subgoal *1/1.9"
	    :expand ((NTH (+ 1 (XPOSITION-EQUAL X (CDR KEYS))) VALS))))))

(defthm binding-equal-bind-all-equal
  (equal (binding-equal x (bind-all-equal keys vals a))
	 (if (member-equal x keys)
	     (if (< (position-equal x keys) (len vals))
		 (nth (position-equal x keys) vals)
	       (binding-equal x a))
	   (binding-equal x a)))
  :hints (("Goal" :do-not-induct t :in-theory (disable binding-equal))))

(defthm binding-equal-domain-restrict-equal
  (equal (binding-equal x (domain-restrict-equal l a))
	 (if (member-equal x l)
	     (if (bound?-equal x a)
		 (binding-equal x a)
	       nil)
	   nil))
  :hints (("Goal" :in-theory (enable binding-equal bound?-equal))))

(defthm binding-equal-rembind-all-equal
  (equal (binding-equal x (rembind-all-equal l a))
	 (if (member x l)
	     nil
	   (binding-equal x a))))

(defthm binding-equal-bind-pairs-equal
  (implies (alistp pairs)
	   (equal (binding-equal x (bind-pairs-equal pairs a))
		  (if (bound?-equal x pairs)
		      (binding-equal x pairs)
		    (binding-equal x a)))))

(defthm binding-equal-alist-compose-equal
  (implies (and (alistp a1)
		(alistp a2))
	   (equal (binding-equal x (alist-compose-equal a1 a2))
		  (if (bound?-equal x a1)
		      (if (bound?-equal (binding-equal x a1) a2)
			  (binding-equal (binding-equal x a1) a2)
			nil)
		    nil)))
  :hints (("Goal" :do-not-induct t :in-theory (disable domain))))

; ------------------------------------------------------------
; BOUND?
; ------------------------------------------------------------

(local
 (defun double-list-induction (a b)
   (declare (xargs :guard (and (true-listp a) (true-listp b))))
   (cond ((endp a) nil)
	 ((endp b) nil)
	 (t (double-list-induction (cdr a) (cdr b))))))

(defthm equal-domain-fwd-to-bound?-equal
  (implies (and (equal (domain a) (domain b))
		(bound?-equal x a)
		(alistp a)
		(alistp b))
	   (bound?-equal x b))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (double-list-induction a b))))

(defthm bound?-equal-acons
  (equal (bound?-equal x (acons y z a))
	 (or (equal x y)
	     (bound?-equal x a))))

(defthm bound?-equal-append
  (implies (alistp a1)
	   (equal (bound?-equal x (append a1 a2))
		  (or (bound?-equal x a1)
		      (bound?-equal x a2)))))

(defthm bound?-equal-bind-equal
  (equal (bound?-equal x (bind-equal y v a))
	 (or (equal x y)
	     (bound?-equal x a))))

(defthm bound?-equal-pairlis$
  (iff (bound?-equal x (pairlis$ a b))
       (member-equal x a)))

(defthm bound?-equal-rembind-equal
  (equal (bound?-equal x (rembind-equal y a))
	 (and (not (equal x y))
	      (bound?-equal x a))))

(local
 (defthm xbound?-equal-bind-all-equal
   (equal (bound?-equal x (bind-all-equal keys vals a))
	  (if (member-equal x keys)
	      (or (< (xposition-equal x keys) (len vals))
		  (bound?-equal x a))
	    (bound?-equal x a)))
   :hints (("Goal" :do-not-induct t :in-theory (enable bound?-equal)))))

(defthm bound?-equal-bind-all-equal
  (equal (bound?-equal x (bind-all-equal keys vals a))
	 (if (member-equal x keys)
	     (or (< (position-equal x keys) (len vals))
		 (bound?-equal x a))
	   (bound?-equal x a)))
  :hints (("Goal" :do-not-induct t)))

(defthm bound?-equal-domain-restrict-equal
  (equal (bound?-equal x (domain-restrict-equal l a))
	 (and (member-equal x l)
	      (bound?-equal x a)))
  :hints (("Goal" :do-not-induct t :in-theory (enable bound?-equal))))

(defthm bound?-equal-rembind-all-equal
  (equal (bound?-equal x (rembind-all-equal l a))
	 (if (member-equal x l)
	     nil
	   (bound?-equal x a))))

(defthm bound?-equal-bind-pairs-equal
  (implies (alistp pairs)
	   (equal (bound?-equal x (bind-pairs-equal pairs a))
		  (or (bound?-equal x pairs)
		      (bound?-equal x a)))))

(defthm bound?-equal-alist-compose-equal
  (implies (and (alistp a1)
		(alistp a2))
	   (equal (bound?-equal x (alist-compose-equal a1 a2))
		  (and (bound?-equal x a1)
		       (bound?-equal (binding-equal x a1) a2))))
  :hints (("Goal" :do-not-induct t :in-theory (disable domain))))

; ------------------------------------------------------------
; ALL-BOUND?-EQUAL
; ------------------------------------------------------------

(defthm all-bound?-equal-acons
  (implies (all-bound?-equal l a)
	   (all-bound?-equal l (acons x y a))))

(defthm all-bound?-equal-append1
  (equal (all-bound?-equal (append x y) a)
	 (and (all-bound?-equal x a)
	      (all-bound?-equal y a))))

(defthm all-bound?-equal-append2a
  (implies (all-bound?-equal l a)
	   (all-bound?-equal l (append a b))))

(defthm all-bound?-equal-append2b
  (implies (and (alistp a)
		(all-bound?-equal l b))
	   (all-bound?-equal l (append a b))))

(defthm all-bound?-firstn
  (implies (all-bound?-equal l a)
	   (all-bound?-equal (firstn n l) a)))

(defthm all-bound?-nthcdr
  (implies (all-bound?-equal l a)
	   (all-bound?-equal (nthcdr n l) a)))

(defthm all-bound?-equal-bind-equal
  (implies (all-bound?-equal l a)
	   (all-bound?-equal l (bind-equal x y a))))

(defthm all-bound?-equal-pairlis$
  (iff (all-bound?-equal x (pairlis$ a b))
       (subsetp-equal x a)))

(defthm all-bound?-equal-rembind-equal
  (equal (all-bound?-equal l (rembind-equal x a))
	 (if (member-equal x l)
	     nil
	   (all-bound?-equal l a))))

(defthm all-bound?-equal-bind-all-equal
  (implies (<= (len keys) (len vals))
	   (all-bound?-equal keys (bind-all-equal keys vals a))))

(defthm all-bound?-equal-domain-restrict-equal
  (implies (and (all-bound?-equal l a)
		(subsetp-equal l l1))
	   (all-bound?-equal l (domain-restrict-equal l1 a))))

(defthm all-bound?-equal-rembind-all-equal
  (equal (all-bound?-equal l1 (rembind-all-equal l2 a))
	 (if (intersection-equal l1 l2)
	     nil
	   (all-bound?-equal l1 a))))

(defthm all-bound?-equal-bind-pairs-equal1
  (implies (all-bound?-equal l pairs)
	   (all-bound?-equal l (bind-pairs-equal pairs a))))

(defthm all-bound?-equal-bind-pairs-equal2
  (implies (all-bound?-equal l a)
	   (all-bound?-equal l (bind-pairs-equal pairs a))))

(local
  (defthm bound?-equal-alist-compose-domain-equal
    (implies (and (alistp a1)
 		 (alistp a2))
 	    (equal (bound?-equal x (alist-compose-domain-equal dom a1 a2))
 		   (and (member x dom)
			(bound?-equal x a1)
 			(bound?-equal (binding-equal x a1) a2))))))

(defthm all-bound?-equal-alist-compose-equal
  (implies (and (alistp a1)
		(alistp a2)
		(all-bound?-equal l a1)
		(all-bound?-equal (all-bindings-equal l a1) a2))
	   (all-bound?-equal l (alist-compose-equal a1 a2)))
  :hints (("Goal" :in-theory (Disable bound?-equal domain))))

(defthm all-bound?-equal-collect-bound-equal
  (all-bound?-equal (collect-bound-equal l a) a))

; ------------------------------------------------------------
; COLLECT-BOUND-EQUAL
; ------------------------------------------------------------

(defthm  all-bound?-equal-collect-bound-equal1
  (implies (and (true-listp l)
		(all-bound?-equal l a))
	   (equal (collect-bound-equal l a) l)))

(defthm collect-bound-equal-append
  (equal (collect-bound-equal (append x y) a)
	 (append (collect-bound-equal x a)
		 (collect-bound-equal y a))))

; ------------------------------------------------------------
; ALL-BINDINGS
; ------------------------------------------------------------

(defthm all-bindings-equal-append
  (equal (all-bindings-equal (append x y) a)
	 (append (all-bindings-equal x a)
		 (all-bindings-equal y a))))

; ------------------------------------------------------------
; DOMAIN
; ------------------------------------------------------------

(defthm domain-acons
  (equal (domain (acons x v a))
	 (cons x (domain a))))

(defthm domain-append
  (equal (domain (append a1 a2))
	 (append (domain a1) (domain a2))))

(defthm domain-cons
  (equal (domain (cons pair a))
	 (cons (car pair) (domain a))))

(defthm domain-bind-equal
  (implies (alistp a)
	   (equal (domain (bind-equal x v a))
		  (if (bound?-equal x a)
		      (domain a)
		      (append (domain a) (list x)))))
  :hints (("Goal" :induct t)))

(defthm domain-pairlis$
  (implies (true-listp a)
	   (equal (domain (pairlis$ a b)) a))
  :hints (("Goal" :induct t)))

(defthm domain-rembind-equal
  (equal (domain (rembind-equal x a))
	 (remove-equal x (domain a)))
  :hints (("Goal" :induct t)))

(defthm domain-bind-all-equal
  (implies (and (alistp a)
		(all-bound?-equal l a))
	   (equal (domain (bind-all-equal l vals a))
		  (domain a)))
  :hints (("Goal" :induct (bind-all-equal l vals a)
	  :in-theory (disable bound?-equal bind-equal domain))))

(defthm domain-domain-restrict-equal
  (equal (domain (domain-restrict-equal l a))
	 (intersection-equal (domain a) l))
  :hints (("Goal" :in-theory (enable domain))))

(defthm domain-rembind-all-equal
  (subsetp-equal (domain (rembind-all-equal l a))
		 (domain a)))

(defthm domain-bind-pairs-equal
  (implies (and (alistp pairs)
		(alistp a)
		(all-bound?-equal (domain pairs) a))
	   (equal (domain (bind-pairs-equal pairs a))
		  (domain a)))
  :hints (("Goal" :induct (bind-pairs-equal pairs a)
	   :in-theory (disable domain bind-equal bound?-equal))))

(local
 (defthm domain-alist-compose-domain-equal
  (implies (and (alistp a1)
		(alistp a2))
	   (subsetp-equal (domain (alist-compose-domain-equal dom a1 a2))
			  dom))
  :hints (("Goal" :in-theory (disable domain bound?-equal binding-equal)))))

(defthm domain-alist-compose-equal
  (implies (and (alistp a1)
		(alistp a2))
	   (subsetp-equal (domain (alist-compose-equal a1 a2))
			  (domain a1)))
  :hints (("Goal" :in-theory (disable domain bound?-equal binding-equal))))

; ------------------------------------------------------------
; RANGE
; ------------------------------------------------------------

(defthm range-acons
  (equal (range (acons x y a))
	 (cons y (range a))))

(defthm range-append
  (equal (range (append a1 a2))
	 (append (range a1) (range a2))))

(defthm range-cons
  (equal (range (cons pair a))
	 (cons (cdr pair) (range a))))

(defthm range-bind-equal
  (implies (and (alistp a)
		(not (bound?-equal x a)))
	   (equal (range (bind-equal x v a))
		  (append (range a) (list v))))
  :hints
  (("goal" :induct t)))

(defthm range-pairlis$
  (implies (and (true-listp y)
		(equal (len x) (len y)))
	   (equal (range (pairlis$ x y))
		  y))
  :hints (("Goal" :in-theory (enable range)
	   :induct (Pairlis$ x y))))

(defthm subsetp-equal-range-rembind-equal
  (subsetp-equal (range (rembind-equal x l))
		 (range l))
  :hints (("Goal" :in-theory (enable range))))

(in-theory (disable acons
		    alist-compose alist-compose-eq alist-compose-equal
		    bound? bound?-eq bound?-equal
		    binding binding-eq binding-equal
		    domain range))
