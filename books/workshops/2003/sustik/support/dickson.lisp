(in-package "ACL2")

#|

Updated     : 09-08-03
By          : Daron Vroon

File        : dickson.lisp
Authors     : Matyas, Sandip
Date created: 2002-04-24
Revision    : $Id: dickson.lisp,v 1.62 2003/07/04 01:06:26 sustik Exp $

The constructive proof described in the dickson.dvi file is formulated
in this file.  An embedding of monomial sets to ordinals is defined
such that if a monomial sequence is such that no monomial divides
another one further in the sequence, then the corresponding ordinal
sequence assigned to the monomial sets forming proper subsequences is
decreasing according to e0-ord-<.  This will establish by the
well-foundedness of ordinals that there can be no infinitely
decreasing sequence of such monomials.  The direct formulation uses
the ordinals in Cantor normal form as defined in the 'ordinals' book
by written by Panagiotis Manolios and Daron Vroon and the mapping is
lifted to the ACL2 ordinals in a subsequent step.

I am thankful to Sandip Ray for his contributions early in the
project.  His insight lead to simplify the proof attempt by realizing
independence of certain lemmas.

|#

;; (set-match-free-error nil)

;(include-book "ordinal-arith" :skip-proofs-okp nil)
(include-book "../../../../ordinals/ordinals")
;(include-book "../../../../ordinals/e0-ordinal")

(defun o-min (x y)
  (if (o< x y) x y))

;; We start by defining a recognizer for k-tuple of naturals, which is the
;; representation of monomials so far as we are concerned.

(defun natural-tuplep (k x)
  (cond ((zp k) (null x))
	((not (natp (first x))) nil)
	(T (natural-tuplep (1- k) (rest x)))))

(defthm natural-tuplep-length
  (implies (and (natural-tuplep k x)
		(natp k))
	   (equal (length x) k)))

;; The function partial-tuple-<= is the partial order on tuples which
;; coincides with monomial divisibility.

(defun partial-tuple-<= (k x y)
  (cond ((zp k) t)
        ((< (car y) (car x)) nil)
        (t (partial-tuple-<= (1- k) (cdr x) (cdr y)))))

;; We prove now that it is indeed a partial order, namely it is
;; reflexive, transitive, and antisymmetric.

(defthm partial-tuple-<=-transitivity
  (implies (and (partial-tuple-<= k x y)
		(partial-tuple-<= k y z))
	   (partial-tuple-<= k x z))
  :rule-classes :forward-chaining)

(defthm partial-tuple-<=-reflexivity
  (partial-tuple-<= k x x))

(defthm partial-tuple-<=-antisymmetry
  (implies (and (partial-tuple-<= k x y)
                (partial-tuple-<= k y x)
                (natural-tuplep k x)
                (natural-tuplep k y))
           (equal x y))
  :rule-classes :forward-chaining)

;; We define a recognizer for a set of k-tuples.

(defun tuple-setp (k A)
  (cond ((atom A) (equal A nil))
	((not (natural-tuplep k (first A))) nil)
	(T (tuple-setp k (rest A)))))

;; (tuple-setp 1 '((1) (2) (3)))
;; (tuple-setp 3 '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)))

;; We now define a recognizer of the membership of a tuple in a tuple
;; set.

(defun tuple-in-set (x S)
  (cond ((endp S) nil)
	((equal x (first S)) T)
	(T (tuple-in-set x (rest S)))))

;; (tuple-in-set '(1 2 3) '((2 2 5) (8 1 3) (1 2 3) (4 3 4)))

;; And then we can now define a subset relation on tuple sets in the
;; natural way.

(defun tuple-set-subsetp (A B)
  (cond ((endp A) T)
	((not (tuple-in-set (first A) B)) nil)
	(T (tuple-set-subsetp (rest A) B))))

;; (tuple-set-subsetp '((1 2) (3 4) (4 5)) '((3 4) (4 5) (1 4) (2 3) (1 2)))

;; We prove now, that the subset relation is transitive and reflexive,
;; more for sanity check than anything else. Note that we cannot prove
;; anti-symmetry here, since we are not using set equality, but just
;; the vanilla equality.

(defthm tuple-set-subsetp-transitive
  (implies (and (tuple-set-subsetp A B)
                (tuple-set-subsetp B C))
           (tuple-set-subsetp A C))
  :rule-classes :forward-chaining)

(defthm subset-cons
  (implies (tuple-set-subsetp A B)
           (tuple-set-subsetp A (cons e B))))

(defthm tuple-set-subsetp-reflexive
  (tuple-set-subsetp x x))

(in-theory (disable subset-cons))

(defun tuple-set-filter (S i)
  (cond ((endp S) NIL)
	((and (consp (first S)) (<= (first (first S)) i))
	 (cons (first S) (tuple-set-filter (rest S) i)))
	(T (tuple-set-filter (rest S) i))))

;; (tuple-set-filter '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)) 2)

(defthm tuple-set-filter-creates-tuple-set
  (implies (and (tuple-setp k S)
		(natp i))
	   (tuple-setp k (tuple-set-filter S i))))

(defthm tuple-set-filter-monoton
  (implies (and	(natp i)
		(natp j)
		(<= i j))
	   (tuple-set-subsetp (tuple-set-filter S i)
			      (tuple-set-filter S j))))

(defthm tuple-set-filter-element
  (implies (and (tuple-in-set x S)
		(consp x)
		(<= (car x) i)
		(natp i))
	   (tuple-in-set x (tuple-set-filter S i))))

(defthm tuple-set-filter-preserves-subset
  (implies (and	(natp i)
		(tuple-set-subsetp A B))
	   (tuple-set-subsetp (tuple-set-filter A i)
			      (tuple-set-filter B i))))

(defun tuple-set-projection (S)
  (cond ((endp S) NIL)
	((consp (first S)) (cons (rest (first S))
				 (tuple-set-projection (rest S))))
	(T (tuple-set-projection (rest S)))))

;; (tuple-set-projection '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)))

(defthm tuple-set-projection-creates-tuple-set
  (implies (and (tuple-setp k S)
		(natp i))
	   (tuple-setp (1- k) (tuple-set-projection S))))

(defthm tuple-set-projection-element
  (implies (and (tuple-in-set x S)
		(consp x))
	   (tuple-in-set (rest x) (tuple-set-projection S))))

(defthm tuple-set-projection-preserves-subset
  (implies (tuple-set-subsetp A B)
	   (tuple-set-subsetp (tuple-set-projection A)
			      (tuple-set-projection B))))

(defun tuple-set-filter-projection (S i)
  (tuple-set-projection (tuple-set-filter S i)))

(defun tuple-set-max-first (S)
  (cond ((endp S) 0)
	((and (consp (first S)) (natp (first (first S))))
	 (max (first (first S))
	      (tuple-set-max-first (rest S))))
	(T (tuple-set-max-first (rest S)))))

(defthm tuple-set-max-first-property
  (implies (and (tuple-in-set x S)
		(consp x)
		(natp (first x)))
	   (<= (first x) (tuple-set-max-first S))))

(defthm tuple-set-filter-max
  (implies (and (tuple-setp k S)
		(natp k)
		(not (zp k))
		(<= (tuple-set-max-first S) i))
	   (equal (tuple-set-filter S i) S)))

(in-theory (disable tuple-set-filter))
(in-theory (disable tuple-set-projection))

(defthm tuple-set-max-first-subset
  (implies (tuple-set-subsetp A B)
	   (<= (tuple-set-max-first A)
	       (tuple-set-max-first B)))
  :rule-classes :linear)

(in-theory (disable tuple-set-max-first))

(defun tuple-set-min-first (S)
  (cond ((endp S) (omega))
	((and (consp (first S)) (natp (first (first S))))
	 (o-min (first (first S))
                (tuple-set-min-first (rest S))))
	(T (tuple-set-min-first (rest S)))))

;; (tuple-set-min-first '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)))
;; (tuple-set-min-first '( nil ))

(defthm tuple-set-min-first-produces-ordinal
  (o-p (tuple-set-min-first S)))

(defthm tuple-set-min-first-property
  (implies (and (tuple-in-set x S)
		(consp x)
		(natp (first x)))
	   (<= (tuple-set-min-first S) (first x)))
  :hints (("goal" :in-theory (enable o<))))

(defthm tuple-set-min-first-nat
  (implies (and (posp k)
		(tuple-setp k S)
		(consp S))
	   (natp (tuple-set-min-first S)))
  :rule-classes ((:rewrite :match-free :all)
		 (:forward-chaining :trigger-terms ((tuple-setp k S)))))

(defthm technical-tuple-set-min-first-non-empty
  (implies (and (posp k)
		(tuple-setp k S)
		(tuple-in-set x S))
	   (natp (tuple-set-min-first S)))
  :rule-classes ((:forward-chaining
                  :match-free :all
                  :trigger-terms ((tuple-setp k S)
                                  (tuple-in-set x S)))))

(defun tuple-set->ordinal-partial-sum (k S i)
  (declare (xargs :measure (o+ (o* (omega) (nfix k))
			       (nfix (- (tuple-set-max-first S) i)))))
  (cond ((or (not (natp k)) (not (natp i))) 0)
	((zp k) 0)
	((equal k 1)
	 (tuple-set-min-first S))
	((<= (tuple-set-max-first S) i)
	 (o^ (omega)
	     (o+ (tuple-set->ordinal-partial-sum
		  (1- k)
		  (tuple-set-projection S)
		  0)
		 1)))
	(T (o+
	    (o^ (omega)
		(tuple-set->ordinal-partial-sum
		 (1- k)
		 (tuple-set-filter-projection S i)
		 0))
	    (tuple-set->ordinal-partial-sum k S (1+ i))))))

(defun tuple-set->ordinal (k S)
  (if (and (natp k)
	   (tuple-setp k S))
      (tuple-set->ordinal-partial-sum k S 0)
    0))

;; (tuple-set->ordinal 1 '((5) (3) (4) (2) (3)))
;; (tuple-set->ordinal 2 '((2 5) (3 3) (2 4) (4 2) (3 1)))
;; (tuple-set->ordinal 3 '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)))
;; (tuple-set->ordinal 3 '((1 2 3) (1 2 2) (3 1 1) (3 4 1) (2 0 2)))

(defthm tuple-set->ordinal-partial-sum-produces-ordinal
  (o-p (tuple-set->ordinal-partial-sum k A i))
  :rule-classes ((:rewrite)
		 (:forward-chaining
		  :trigger-terms ((tuple-set->ordinal-partial-sum K A i)))))

(defthm tuple-set->ordinal-produces-ordinal
  (o-p (tuple-set->ordinal k A)))

(defthm tuple-set->ordinal-partial-sum-k=1
  (implies (and (tuple-setp 1 S)
		(natp i))
	   (equal (tuple-set->ordinal-partial-sum 1 S i)
		  (tuple-set-min-first S))))

(in-theory (disable tuple-set->ordinal-partial-sum))

(defthm technical-5
  (implies (and (tuple-setp k S)
		(natp k)
		(natp i))
	   (o<= (tuple-set->ordinal-partial-sum k S (1+ i))
		(tuple-set->ordinal-partial-sum k S i)))
  :hints (("Goal" :expand (tuple-set->ordinal-partial-sum k S i))
	  ("Subgoal 4'" :expand (tuple-set->ordinal-partial-sum 0 S (1+ i)))
	  ("Subgoal 1'" :expand (tuple-set->ordinal-partial-sum k S (1+ i)))))

(defthm tuple-set-subset-consp
  (implies (and (tuple-set-subsetp a b)
		(consp a))
	   (consp b))
  :rule-classes :forward-chaining)

(encapsulate
 ()
 (local
  (defthm l1
    (implies (and (consp a)
		  (consp (car a))
		  (natp (caar a))
		  (o<= (tuple-set-min-first b)
		       (tuple-set-min-first (cdr a)))
		  (tuple-setp 1 a)
		  (tuple-setp 1 b)
		  (tuple-set-subsetp a b))
	     (o<= (tuple-set-min-first b)
		  (tuple-set-min-first a)))
    :hints (("goal"
	     :do-not-induct t
	     :in-theory (disable tuple-set-min-first-property)
	     :use ((:instance tuple-set-min-first-property
			      (x (car a))
			      (S B)))))
    :rule-classes :forward-chaining))

 (defthm subset-tuple-set-min-first-<=
   (implies (and (tuple-setp 1 a)
		 (tuple-setp 1 b)
		 (tuple-set-subsetp a b))
	    (o<= (tuple-set-min-first b)
		 (tuple-set-min-first a)))))

(defun map-lemma-1.1-induction-hint (k A B i)
  (declare (xargs :measure (o+ (o* (omega) (nfix k)) (nfix (- (tuple-set-max-first B) i)))))
  (cond	((not (natp i)) A)
	((zp k) B)
	((equal 1 k) 0)
	((<= (tuple-set-max-first B) i)
	 (map-lemma-1.1-induction-hint
	  (1- k)
	  (tuple-set-projection A)
	  (tuple-set-projection B)
	  0))
	(T (list (map-lemma-1.1-induction-hint
		  (1- k)
		  (tuple-set-filter-projection A i)
		  (tuple-set-filter-projection B i)
		  0)
		 (map-lemma-1.1-induction-hint
		  k A B (1+ i))))))

(in-theory (enable tuple-set-min-first-property))

(defthm tuple-set-min-first-upper-bound
  (o<= (tuple-set-min-first S) (omega)))

(in-theory (disable tuple-set-min-first-property))

(defthm map-lemma-1.1
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (tuple-set-subsetp A B)
                (natp k)
		(natp i))
           (o<= (tuple-set->ordinal-partial-sum
		   k B i)
		  (tuple-set->ordinal-partial-sum
		   k A i)))
  :hints (("Goal"
	   :do-not generalize
	   :induct (map-lemma-1.1-induction-hint k A B i))
	  ("Subgoal *1/4"
	   :expand ((tuple-set->ordinal-partial-sum k B i)
		    (tuple-set->ordinal-partial-sum k A i)))
	  ("Subgoal *1/4.1'"
	   :in-theory (disable |a <= b & c <= d  =>  a+c <= b+d|)
	   :use (:instance |a <= b & c <= d  =>  a+c <= b+d|
			   (a (O^ (OMEGA)
                                  (TUPLE-SET->ORDINAL-PARTIAL-SUM
                                   (+ -1 K)
                                   (TUPLE-SET-PROJECTION
                                    (TUPLE-SET-FILTER B I))
                                   0)))
			   (b (O^ (OMEGA)
                                  (TUPLE-SET->ORDINAL-PARTIAL-SUM
                                   (+ -1 K)
                                   (TUPLE-SET-PROJECTION A)
                                   0)))
			   (c (TUPLE-SET->ORDINAL-PARTIAL-SUM K B (+ 1 I)))
			   (d (O^ (OMEGA)
                                  (O+ (TUPLE-SET->ORDINAL-PARTIAL-SUM
                                       (+ -1 K)
                                       (TUPLE-SET-PROJECTION A)
                                       0)
                                      1)))))
	  ("Subgoal *1/4.1''"
	   :expand (TUPLE-SET->ORDINAL-PARTIAL-SUM K A (+ 1 I)))
	  ("Subgoal *1/3"
	   :expand ((tuple-set->ordinal-partial-sum k A i)
		    (tuple-set->ordinal-partial-sum k B i)))
	  ("Subgoal *1/1''"
	   :expand ((TUPLE-SET->ORDINAL-PARTIAL-SUM 0 B I)
		    (TUPLE-SET->ORDINAL-PARTIAL-SUM 0 A I)))))

(in-theory (disable map-lemma-1.1))

(defthm map-lemma-1
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (tuple-set-subsetp A B)
                (natp k))
           (o<= (tuple-set->ordinal k B)
                (tuple-set->ordinal k A)))
  :hints (("Goal"
	   :do-not-induct t
	   :expand ((tuple-set->ordinal k B)
		    (tuple-set->ordinal k A))
	   :use (:instance map-lemma-1.1 (i 0)))))

(in-theory (disable tuple-set->ordinal))

(defthm map-lemma-2
  (implies (and (tuple-setp k A)
                (natp k)
                (< 1 k)
		(natp i))
	   (o<= (tuple-set->ordinal (1- k)
				    (tuple-set-filter-projection A (1+ i)))
		(tuple-set->ordinal (1- k)
				    (tuple-set-filter-projection A i)))))

(defthm map-lemma-2.1
  (implies (and (tuple-setp k A)
                (natp k)
                (< 1 k)
		(natp i))
	   (o<= (tuple-set->ordinal-partial-sum
		 (1- k)
		 (tuple-set-projection (tuple-set-filter A (1+ i)))
		 0)
		(tuple-set->ordinal-partial-sum
		 (1- k)
		 (tuple-set-projection (tuple-set-filter A i))
		 0)))
  :hints (("Goal"
	   :use (:instance map-lemma-1.1
			   (k (1- k))
			   (i 0)
			   (A (tuple-set-filter-projection A i))
			   (B (tuple-set-filter-projection A (1+ i)))))))


(defun map-lemma-3.1-induction-hint (A i)
  (declare (xargs :measure (nfix (- (tuple-set-max-first A) i))))
  (cond	((not (natp i)) A)
	((<= (tuple-set-max-first A) i) T)
	(T (list (map-lemma-3.1-induction-hint A (1+ i))))))

(encapsulate
 ()

 (local
  (defthm l1
    (implies
     (and (natp i)
	  (< i (tuple-set-max-first a))
	  (o<= (tuple-set->ordinal-partial-sum k a (+ 1 i))
	       (o* (o^ (omega)
		       (tuple-set->ordinal-partial-sum
			(+ -1 k)
			(tuple-set-projection (tuple-set-filter a (+ 1 i)))
			0))
		   (omega)))
	  (tuple-setp k a)
	  (posp k)
	  (< 1 k))
     (o<= (o^ (omega)
	      (o+ (tuple-set->ordinal-partial-sum
		   (+ -1 k)
		   (tuple-set-projection (tuple-set-filter a (+ 1 i)))
		   0)
		  1))
	  (o^ (omega)
	      (o+ (tuple-set->ordinal-partial-sum
		   (+ -1 k)
		   (tuple-set-projection
		    (tuple-set-filter a i))
		   0)
		  1))))))

 (local
  (defthm l2
    (implies
     (and (natp i)
	  (< i (tuple-set-max-first a))
	  (o<= (tuple-set->ordinal-partial-sum k a (+ 1 i))
	       (o* (o^ (omega)
		       (tuple-set->ordinal-partial-sum
			(+ -1 k)
			(tuple-set-projection (tuple-set-filter a (+ 1 i)))
			0))
		   (omega)))
	  (tuple-setp k a)
	  (posp k)
	  (< 1 k))
     (o<= (tuple-set->ordinal-partial-sum k a (+ 1 i))
	  (o^ (omega)
	      (o+ (tuple-set->ordinal-partial-sum
		   (+ -1 k)
		   (tuple-set-projection (tuple-set-filter a i))
		   0)
		  1))))
    :hints (("goal"
	     :use ((:instance |a <= b & b <= c  =>  a <= c|
			      (a (tuple-set->ordinal-partial-sum k a (+ 1 i)))
			      (b (o* (o^ (omega)
					 (tuple-set->ordinal-partial-sum
					  (+ -1 k)
					  (tuple-set-projection (tuple-set-filter a (+ 1 i)))
					  0))
				     (omega)))
			      (c (o^ (omega)
				     (o+ (tuple-set->ordinal-partial-sum
					  (+ -1 k)
					  (tuple-set-projection
					   (tuple-set-filter a i))
					  0)
					 1)))))))))
 (local
  (defthm l3
    (implies
     (and (natp i)
	  (< i (tuple-set-max-first a))
	  (o<= (tuple-set->ordinal-partial-sum k a (+ 1 i))
	       (o* (o^ (omega)
		       (tuple-set->ordinal-partial-sum
			(+ -1 k)
			(tuple-set-projection (tuple-set-filter a (+ 1 i)))
			0))
		   (omega)))
	  (tuple-setp k a)
	  (posp k)
	  (< 1 k))
     (o<= (o+ (o^ (omega)
		  (tuple-set->ordinal-partial-sum
		   (+ -1 k)
		   (tuple-set-filter-projection a i)
		   0))
	      (tuple-set->ordinal-partial-sum k a (+ 1 i)))
	  (o+ (o^ (omega)
		  (tuple-set->ordinal-partial-sum
		   (+ -1 k)
		   (tuple-set-filter-projection a i)
		   0))
	      (o^ (omega)
		  (o+ (tuple-set->ordinal-partial-sum
		       (+ -1 k)
		       (tuple-set-filter-projection a i)
		       0)
		      1)))))
    :hints (("goal"
	     :do-not-induct t
	     :in-theory (disable l2 |a < b  <=>  c+a < c+b|)
	     :use (l2
		   (:instance |a < b  <=>  c+a < c+b|
			      (c (o^ (omega)
				     (tuple-set->ordinal-partial-sum
				      (+ -1 k)
				      (tuple-set-filter-projection a i)
				      0)))
			      (b (tuple-set->ordinal-partial-sum k a (+ 1 i)))
			      (a (o^ (omega)
				     (o+ (tuple-set->ordinal-partial-sum
					  (+ -1 k)
					  (tuple-set-filter-projection a i)
					  0)
					 1)))))))))

 (defthm map-lemma-3.1
   (implies (and (tuple-setp k A)
		 (posp k)
		 (< 1 k)
		 (natp i))
	    (o<= (tuple-set->ordinal-partial-sum k A i)
		 (o^ (omega) (o+ (tuple-set->ordinal-partial-sum
				  (1- k)
				  (tuple-set-filter-projection A i)
				  0)
				 1))))
   :hints (("Goal"
	    :induct (map-lemma-3.1-induction-hint A i))
	   ("Subgoal *1/2''"
	    :expand (tuple-set->ordinal-partial-sum k A i)
	    :in-theory (disable l3)
	    :use ((:instance l3)))
	   ("Subgoal *1/1'"
	    :expand (TUPLE-SET->ORDINAL-PARTIAL-SUM K A I)))))

(defthm map-lemma-3.2
  (implies (and (tuple-setp k A)
		(natp k)
		(< 1 k)
		(natp i))
	   (o< (o^ (omega) (tuple-set->ordinal-partial-sum
			    (1- k)
			    (tuple-set-filter-projection A i)
			    0))
	       (tuple-set->ordinal-partial-sum k A i)))
  :hints (("Goal"
	   :expand (tuple-set->ordinal-partial-sum k A i))
	  ("Subgoal 2" ; Matt K. mod 5/2016 (type-set bit for {1})
	   :expand (tuple-set->ordinal-partial-sum k A (+ 1 i)))))

(defthm map-lemma-3.3
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (natp k)
                (natp i)
                (< 1 k)
		(o< (tuple-set->ordinal-partial-sum
		     (1- k)
		     (tuple-set-projection (tuple-set-filter A i))
		     0)
		    (tuple-set->ordinal-partial-sum
		     (1- k)
		     (tuple-set-projection (tuple-set-filter B i))
		     0)))
	   (o< (tuple-set->ordinal-partial-sum k A i)
	       (tuple-set->ordinal-partial-sum k B i)))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable |a <= b & b < c  =>  a < c|)
	   :use (map-lemma-3.1
		 (:instance map-lemma-3.2
			    (a b))
		 (:instance |a <= b & b < c  =>  a < c|
			    (a (o* (o^ (omega)
				       (tuple-set->ordinal-partial-sum
					(+ -1 k)
					(tuple-set-projection (tuple-set-filter a i))
					0))
				   (omega)))
			    (b (o^ (omega)
				   (tuple-set->ordinal-partial-sum
				    (+ -1 k)
				    (tuple-set-projection (tuple-set-filter b i))
				    0)))
			    (c (tuple-set->ordinal-partial-sum k b i)))
		 (:instance |a <= b  =>  c^a <= c^b|
			    (a (o+ (tuple-set->ordinal-partial-sum
				    (+ -1 k)
				    (tuple-set-filter-projection a i)
				    0)
				   1))
			    (b (tuple-set->ordinal-partial-sum
				(+ -1 k)
				(tuple-set-filter-projection b i)
				0))
			    (c (omega)))))))

(defthm map-lemma-3.4
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (posp k)
                (natp i)
                (< 1 k)
                (equal (tuple-set->ordinal-partial-sum k A i)
                       (tuple-set->ordinal-partial-sum k B i)))
	   (equal (tuple-set->ordinal-partial-sum
		   (1- k)
		   (tuple-set-projection (tuple-set-filter A i))
		   0)
		  (tuple-set->ordinal-partial-sum
		   (1- k)
		   (tuple-set-projection (tuple-set-filter B i))
		   0)))
  :hints (("Goal" :use (map-lemma-3.3
			(:instance map-lemma-3.3
				   (A B)
				   (B A))))))

(in-theory (disable map-lemma-3.4))

(defthm map-lemma-3.5
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (posp k)
                (natp i)
                (< 1 k)
                (equal (tuple-set->ordinal-partial-sum k A i)
                       (tuple-set->ordinal-partial-sum k B i)))
           (equal (tuple-set->ordinal-partial-sum k A (1+ i))
                  (tuple-set->ordinal-partial-sum k B (1+ i))))
  :hints ; Matt K. mod 5/2016 (type-set bit for {1}): avoid subgoal hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable |a^(b+c)  =  a^b * a^c|)
    :use map-lemma-3.4
    :expand ((tuple-set->ordinal-partial-sum k a i)
             (tuple-set->ordinal-partial-sum k b i)
             (tuple-set->ordinal-partial-sum k a (+ 1 i))
             (tuple-set->ordinal-partial-sum k b (+ 1 i))))))

(defun map-lemma-3.6-induction-hint (i j)
  (cond ((not (natp i)) nil)
	((not (natp j)) nil)
	((<= j i) nil)
	(T (map-lemma-3.6-induction-hint i (1- j)))))

(defthm map-lemma-3.6
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (natp k)
                (< 1 k)
                (natp i)
		(natp j)
		(<= i j)
                (equal (tuple-set->ordinal-partial-sum k A i)
                       (tuple-set->ordinal-partial-sum k B i)))
	   (equal (equal (tuple-set->ordinal-partial-sum k A j)
			 (tuple-set->ordinal-partial-sum k B j))
		  T))
  :hints (("Goal"
	   :induct (map-lemma-3.6-induction-hint i j))
	  ("Subgoal *1/2'"
	   :use (:instance map-lemma-3.5
			   (i (+ -1 j))))))

(defthm map-lemma-3.7
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (natp k)
                (< 1 k)
                (natp i)
		(natp j)
		(<= i j)
                (equal (tuple-set->ordinal-partial-sum k A i)
                       (tuple-set->ordinal-partial-sum k B i)))
	   (equal (equal (tuple-set->ordinal-partial-sum
			  (1- k)
			  (tuple-set-projection (tuple-set-filter A j))
			  0)
			 (tuple-set->ordinal-partial-sum
			  (1- k)
			  (tuple-set-projection (tuple-set-filter B j))
			  0))
		  T))
  :hints (("Goal"
	   :use (map-lemma-3.6
		 (:instance map-lemma-3.4
			    (i j))))))

(defthm map-lemma-3
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (natp k)
                (natp i)
                (< 1 k)
                (equal (tuple-set->ordinal-partial-sum k A 0)
                       (tuple-set->ordinal-partial-sum k B 0)))
	   (equal (tuple-set->ordinal-partial-sum
		     (1- k)
		     (tuple-set-projection (tuple-set-filter A i))
		     0)
		  (tuple-set->ordinal-partial-sum
		     (1- k)
		     (tuple-set-projection (tuple-set-filter B i))
		     0)))
  :hints (("Goal"
	   :use (:instance map-lemma-3.7
			   (i 0)
			   (j i)))))

(defun exists-partial-tuple-<=-set-witness (k S x)
  (cond ((endp S) nil)
        ((partial-tuple-<= k (first S) x) (first S))
        (t (exists-partial-tuple-<=-set-witness k (rest S) x))))

(defun exists-partial-tuple-<=-set (k S x)
  (let ((w (exists-partial-tuple-<=-set-witness k S x)))
    (and (natural-tuplep k w)
	 (tuple-in-set w S)
	 (partial-tuple-<= k w x))))

(defthm exists-partial-tuple-<=-set-suff
  (implies (and (tuple-setp k S)
		(tuple-in-set w S)
		(partial-tuple-<= k w x))
	   (exists-partial-tuple-<=-set k S x)))

(defthm exists-partial-tuple-<=-set-impl
  (implies (and (natp k)
		(<= 1 k)
		(natural-tuplep k x)
		(tuple-setp k S)
		(exists-partial-tuple-<=-set k S x))
	   (and (equal (natural-tuplep
			k
			(exists-partial-tuple-<=-set-witness k S x))
		       T)
		(equal (tuple-in-set
			(exists-partial-tuple-<=-set-witness k S x)
			S)
		       T)
		(partial-tuple-<=
		 k
		 (exists-partial-tuple-<=-set-witness k S x)
		 x))))

(in-theory (disable exists-partial-tuple-<=-set))

(defun exists-projection-filter-inverse-witness (S v i)
  (cond ((endp S) nil)
	((and (equal v (rest (first S)))
	      (<= (first (first S)) i)) (first S))
	(T (exists-projection-filter-inverse-witness (rest S) v i))))

(defun exists-projection-filter-inverse (S v i)
  (let ((w (exists-projection-filter-inverse-witness S v i)))
    (and (tuple-in-set w S)
	 (equal v (rest w))
	 (<= (first w) i))))

(defthm exists-projection-filter-inverse-suff
  (implies (and (tuple-in-set w S)
		(equal v (rest w))
		(<= (first w) i))
	   (exists-projection-filter-inverse S v i)))

(defthm exists-projection-filter-inverse-impl
  (implies (and (tuple-setp k S)
		(natural-tuplep (1- k) v)
		(<= 1 k)
		(exists-projection-filter-inverse S v i))
	   (and (equal (natural-tuplep
			k
			(exists-projection-filter-inverse-witness S v i))
		       T)
		(equal (tuple-in-set
			(exists-projection-filter-inverse-witness S v i)
			S)
		       T)
		(equal (rest (exists-projection-filter-inverse-witness S v i))
		       v)
		(<= (first (exists-projection-filter-inverse-witness S v i))
		    i))))

(in-theory (enable tuple-set-filter))
(in-theory (enable tuple-set-projection))

(defthm map-lemma-4.1.1
  (implies (and (tuple-setp k A)
                (natural-tuplep (1- k) u)
		(natp i)
		(natp k)
		(< 1 k)
                (tuple-in-set u (tuple-set-projection (tuple-set-filter A i))))
	   (exists-projection-filter-inverse A u i)))

(defthm map-lemma-4.1
  (implies (and (tuple-setp k A)
                (natural-tuplep (1- k) u)
		(natp i)
		(natp k)
		(< 1 k)
                (tuple-in-set u (tuple-set-projection (tuple-set-filter A i))))
	   (and (equal (rest (exists-projection-filter-inverse-witness A u i))
		       u)
		(<= (first
		     (exists-projection-filter-inverse-witness A u i)) i))))

(defthm map-lemma-4.2
  (implies (and (tuple-setp k S)
		(natp k)
		(<= 2 k)
		(natural-tuplep k v)
		(tuple-in-set v S))
	   (tuple-in-set
	    (cdr v)
	    (tuple-set-projection (tuple-set-filter S (car v))))))

(in-theory (disable tuple-set-filter))
(in-theory (disable tuple-set-projection))

(defun map-lemma-4-induction-hint (A B v k)
  (cond ((zp k) nil)
	((< k 2) (list A B v))
	(T (map-lemma-4-induction-hint
	    (tuple-set-projection (tuple-set-filter A (first v)))
	    (tuple-set-projection (tuple-set-filter B (first v)))
	    (rest v)
	    (1- k)))))

(in-theory (disable map-lemma-4.1))

(defthm partial-tuple-<=-decomposition
  (implies (and (natural-tuplep k x)
		(natural-tuplep k y)
		(<= (first x) (first y))
		(partial-tuple-<= (1- k) (rest x) (rest y)))
	   (partial-tuple-<= k x y)))

(in-theory (disable map-lemma-3))

(defthm tuple-set-min-first-special
  (implies (and (tuple-setp 1 S)
		(o< (tuple-set-min-first S) (omega)))
	   (tuple-in-set (list (tuple-set-min-first S)) S)))

(defthm map-lemma-4
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (tuple-set-subsetp A B)
                (natural-tuplep k v)
                (tuple-in-set v B)
                (equal (tuple-set->ordinal-partial-sum k A 0)
                       (tuple-set->ordinal-partial-sum k B 0))
                (natp k)
		(<= 1 k))
           (exists-partial-tuple-<=-set k A v))
  :hints (("Goal"
	   :induct (map-lemma-4-induction-hint A B v k))
	  ("Subgoal *1/3.2"
	   :use ((:instance map-lemma-4.1
			    (i (car v))
			    (u (exists-partial-tuple-<=-set-witness
				(+ -1 k)
				(tuple-set-projection
				 (tuple-set-filter A (car v)))
				(cdr v))))))
	  ("Subgoal *1/3.2''"
	   :use ((:instance
		  exists-partial-tuple-<=-set-suff
		  (S A)
		  (w (EXISTS-PROJECTION-FILTER-INVERSE-WITNESS
		      A
		      (EXISTS-PARTIAL-TUPLE-<=-SET-WITNESS
		       (+ -1 K)
		       (TUPLE-SET-PROJECTION (TUPLE-SET-FILTER A (CAR V)))
		       (CDR V))
		      (CAR V)))
		  (x v))))
	  ("Subgoal *1/3.1"
	   :use ((:instance map-lemma-3
			    (i (car v)))))
	  ("Subgoal *1/2'''"
	   :use ((:instance tuple-set-min-first-property
			    (x v)
			    (S B))
		 (:instance exists-partial-tuple-<=-set-suff
			    (k 1)
			    (S A)
			    (w (list (TUPLE-SET-MIN-FIRST A)))
			    (x v))))
	  ("Subgoal *1/2.1''"
	   :use ((:instance tuple-set-min-first-special
			    (S A))))

	  ("Subgoal *1/2.1'5'"
	   :use ((:instance tuple-set-min-first-nat
			    (k 1)
			    (S B))))))

(defthm map-lemma-4-alt
  (implies (and (tuple-setp k A)
                (tuple-setp k B)
                (tuple-set-subsetp A B)
                (natural-tuplep k v)
                (tuple-in-set v B)
                (equal (tuple-set->ordinal k A)
                       (tuple-set->ordinal k B))
                (natp k)
		(<= 1 k))
           (exists-partial-tuple-<=-set k A v))
  :hints (("Goal"
	   :use map-lemma-4)
	  ("Goal'"
	   :expand ((TUPLE-SET->ORDINAL K A)
		    (TUPLE-SET->ORDINAL K B)))
	  ("Goal'''"
	   :expand (TUPLE-SET->ORDINAL K NIL))))

(defthm tuple-set-subsetp-with-cdr
  (implies (tuple-set-subsetp A B)
	   (tuple-set-subsetp (cdr A) B)))

(defthm tuple-set-subsetp-idempotent
  (tuple-set-subsetp S S))

(in-theory (disable map-lemma-1))
(in-theory (disable map-lemma-4))

(defthm dickson-map-thm.1
  (implies (and (tuple-setp k S)
		(consp S)
                (natp k)
		(<= 1 k))
	   (o<= (tuple-set->ordinal k S)
		(tuple-set->ordinal k (rest S))))
  :hints (("Goal" :use ((:instance map-lemma-1 (A (rest S)) (B S))))))

(defthm dickson-map-thm
  (implies (and (tuple-setp k S)
		(consp S)
                (natp k)
		(<= 1 k)
		(not (exists-partial-tuple-<=-set
		      k (rest S) (first S))))
	   (o< (tuple-set->ordinal k S)
	       (tuple-set->ordinal k (rest S))))
  :hints (("Goal"
	   :use ((:instance |b <= a & a <= b  =>  a = b|
			    (a (TUPLE-SET->ORDINAL K S))
			    (b (TUPLE-SET->ORDINAL K (CDR S))))
		 (:instance map-lemma-1 (A (rest S)) (B S))
                 (:instance map-lemma-4-alt
                            (A (rest S))
                            (B S)
                            (v (first S)))))))

;(defun old-map (k S)
;  (ctoa (tuple-set->ordinal k S)))

;(in-theory (disable tuple-set->ordinal))

;(defthm dickson-map-thm-alt
;  (implies (and (tuple-setp k S)
;		(consp S)
;                (natp k)
;		(<= 1 k)
;		(not (exists-partial-tuple-<=-set
;		      k (rest S) (first S))))
;	   (e0-ord-< (old-map k S)
;		     (old-map k (rest S)))))

