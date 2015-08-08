; set-defthms.lisp -- theorems about functions in the theory of sets
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(include-book "set-defuns")


; ------------------------------------------------------------
; SUBSETP-EQUAL
; ------------------------------------------------------------

(defthm subsetp-equal-cons
  (implies (subsetp-equal a b)
	   (subsetp-equal a (cons x b))))

(defthm subsetp-equal-reflexive
  (subsetp-equal l l))

(defthm subsetp-equal-transitive
  (implies (and (subsetp-equal a b)
		(subsetp-equal b c))
	   (subsetp-equal a c))
  :rule-classes nil)

(defthm subsetp-equal-append-crock
  (implies (subsetp-equal l1 l2)
	   (subsetp-equal (append l1 (list x)) (cons x l2))))

(defthm subsetp-equal-append2
  (implies (subsetp-equal l1 l2)
	   (subsetp-equal l1 (append l2 l3))))

(defthm subsetp-equal-adjoin-equal1
  (equal (subsetp-equal (adjoin-equal x a) b)
	 (and (memberp-equal x b)
	      (subsetp-equal a b))))

(defthm subsetp-equal-adjoin-equal2
  (implies (subsetp-equal a b)
	   (subsetp-equal a (adjoin-equal x b))))

(defthm subsetp-equal-intersection-equal
  (implies (and (subsetp-equal a b)
	      (subsetp-equal a c))
	 (subsetp-equal a (intersection-equal b c))))

(defthm subsetp-equal-set-difference-equal
  (implies (and (subsetp-equal a b)
		(equal (intersection-equal a c) nil))
	   (subsetp-equal a (set-difference-equal b c))))

(defthm subsetp-equal-union-equal
  (implies (or (subsetp-equal a b)
	       (subsetp-equal a c))
	   (subsetp-equal a (union-equal b c))))

; ------------------------------------------------------------
; SET-EQUAL is an equivalence relation.
; ------------------------------------------------------------

(defthm set-equal-reflexive
  (set-equal l l)
  :hints (("Goal" :do-not-induct t)))

(defthm set-equal-symmetric
  (implies (set-equal a b)
	   (set-equal b a))
  :rule-classes nil)

(defthm set-equal-transitive
  (implies (and (set-equal a b)
		(set-equal b c))
	   (set-equal a c))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
	   :use ((:instance subsetp-equal-transitive (a a) (b b) (c c))
		 (:instance subsetp-equal-transitive (a c) (b b) (c a))))))

; ------------------------------------------------------------
; MEMBERP-EQUAL
; ------------------------------------------------------------

(defthm memberp-equal-subsetp-equal
  (implies (and (memberp-equal x a)
		(subsetp-equal a b))
	   (memberp-equal x b))
  :rule-classes ())

(defthm memberp-equal-set-equal
  (implies (set-equal a b)
	   (iff (memberp-equal x a)
		(memberp-equal x b)))
  :rule-classes ()
  :hints (("Goal" :do-not-induct t
	   :use ((:instance memberp-equal-subsetp-equal (x x) (a a) (b b))
		 (:instance memberp-equal-subsetp-equal (x x) (a b) (b a))))))

(defthm memberp-equal-adjoin-equal
  (iff (memberp-equal x (adjoin-equal y l))
       (or (equal x y)
	   (memberp-equal x l))))

(defthm memberp-equal-intersection-equal
  (iff (memberp-equal x (intersection-equal a b))
       (and (memberp-equal x a)
	    (memberp-equal x b))))

(defthm memberp-equal-set-difference-equal
  (iff (memberp-equal x (set-difference-equal a b))
       (and (memberp-equal x a)
	    (not (memberp-equal x b)))))

(defthm memberp-equal-union-equal
  (iff (memberp-equal x (union-equal a b))
       (or (memberp-equal x a)
	   (memberp-equal x b))))

; ------------------------------------------------------------
; SETP
; ------------------------------------------------------------

(defthm setp-equal-cons
  (equal (setp-equal (cons x l))
	 (and (setp-equal l)
	      (not (memberp-equal x l))))
  :hints (("Goal" :in-theory (enable setp-equal))))

(defthm setp-equal-adjoin-equal
  (implies (setp-equal a)
	   (setp-equal (adjoin-equal x a))))

(local
 (defthm member-equal-intersection-equal
   (iff (member-equal x (intersection-equal a b))
	(and (member-equal x a)
	     (member-equal x b)))))

(defthm setp-equal-intersection-equal
  (implies (setp-equal a)
	   (setp-equal (intersection-equal a b))))

(local
 (defthm member-equal-set-difference-equal
  (iff (member-equal x (set-difference-equal a b))
       (and (member-equal x a)
	    (not (member-equal x b))))))

(defthm setp-equal-set-difference-equal
  (implies (setp-equal a)
	   (setp-equal (set-difference-equal a b))))

(local
 (defthm member-equal-union-equal
   (iff (member-equal x (union-equal a b))
	(or (member-equal x a)
	    (member-equal x b)))))

(defthm setp-equal-union-equal
  (implies (and (setp-equal a) (setp-equal b))
	   (setp-equal (union-equal a b))))

; ------------------------------------------------------------
; INTERSECTION-EQUAL
; ------------------------------------------------------------

(defthm intersection-equal-nil
  (equal (intersection-equal a nil) nil))

(defthm subsetp-equal-intersection-equal-instance
  (implies (and (true-listp a)
		(subsetp-equal a b))
	   (equal (intersection-equal a b) a)))

(defthm intersection-equal-identity
  (implies (true-listp a)
	   (equal (intersection-equal a a) a))
  :hints (("Goal" :do-not-induct t)))

; ------------------------------------------------------------
; UNION-EQUAL
; ------------------------------------------------------------

(defthm union-equal-nil
  (implies (true-listp a)
	   (equal (union-equal a nil) a)))

(defthm subsetp-equal-union-equal-instance
  (implies (and (true-listp b)
		(subsetp-equal a b))
	   (equal (union-equal a b) b)))

(defthm union-equal-identity
  (implies (true-listp a)
	   (equal (union-equal a a) a))
  :hints (("Goal" :do-not-induct t)))

; ------------------------------------------------------------
; SET-DIFFERENCE-EQUAL
; ------------------------------------------------------------

(defthm set-difference-equal-nil
  (implies (true-listp a)
	   (equal (set-difference-equal a nil) a)))

(defthm subsetp-equal-set-difference-equal-instance
  (implies (and (true-listp b)
		(subsetp-equal a b))
	   (equal (set-difference-equal a b) nil)))

(defthm set-difference-equal-identity
  (implies (true-listp a)
	   (equal (set-difference-equal a a) nil))
  :hints (("Goal" :do-not-induct t)))

(defthm set-difference-equal-cons
  (implies (member-equal x b)
	   (equal (set-difference-equal a (cons x b))
		  (set-difference-equal a b))))

(defthm set-difference-null-intersection
  (implies (and (true-listp a)
		(equal (intersection-equal a b) nil))
	   (equal (set-difference-equal a b) a)))


; ------------------------------------------------------------
; Other Facts
; ------------------------------------------------------------

(local
 (defthm member-equal-append
   (iff (member-equal x (append a b))
	(or (member-equal x a)
	    (member-equal x b)))))

(defthm no-duplicatesp-equal-append
  (iff (no-duplicatesp-equal (append a b))
       (and (no-duplicatesp-equal a)
	    (no-duplicatesp-equal b)
	    (not (intersection-equal a b)))))

(local
 (defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
	 (true-listp b))))

(defthm setp-equal-append
  (implies (true-listp a)
	   (iff (setp-equal (append a b))
		(and (setp-equal a)
		     (setp-equal b)
		     (not (intersection-equal a b)))))
  :hints (("Goal" :do-not-induct t)))


(in-theory (disable set-equal setp-equal adjoin-equal memberp-equal))