; Matyas Sustik
; November, 2001

; The following question was posted on the University of Texas
; Computer Science problem web page (located at
; http://www.cs.utexas.edu/users/xli/prob/) numbered problem 13:

; Let f be a function from naturals to naturals.  (Note that naturals
; are non-negative integers.)  It is given that:
;   Property P:: for every n, f^2(n) < f(n + 1) holds.
; Here f^2(n) means applying f twice on n, that is, f(f(n)).
; Prove that f is the identity function.
; Generalization: Prove that f is the identity function given that:
;   Property Q:: for every n exists an i >= 2 such that f^i(n) < f(n + 1).
; (Similarly, f^i(n) means applying f i times on n.)

; For a classical proof of the theorem visit to the above mentioned
; web page.  The article posted at that location contains several
; versions of ACL2 verified proofs about the P and the Q properties.
; Here I include the strongest result only.  I wish to say thanks to
; Peter Manolios who followed upon the first version of the proof
; posted to the ACL2 meeting list.

(in-package "ACL2")

; The following includes help ACL2 with arithmetic:
(include-book "arithmetic/equalities" :dir :system)
(include-book "arithmetic/inequalities" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

; A shorthand for naturals:
(defabbrev np (x)
  (and (integerp x)
       (>= x 0)))

; This form introduces a constrained f function with the
; Q property.  The 'iterated' version is also defined and
; it is called g.  The existence of i in the Q-property
; for a given n is captured by the Q-witness function.
; The type-prescription rules help ACL2 to reason more
; efficiently.
(encapsulate
 (((f *) => *)
  ((Q-witness *) => *))
  (local (defun f (n) (nfix n)))
  (defthm range-f
    (and (integerp (f n))
         (>= (f n) 0))
    :rule-classes :type-prescription)
  (defun g (i n)
    (if (zp (nfix i))
	(nfix n)
      (g (+ -1 (nfix i)) (f n))))  ;tail recursiveness is important
  (local (defun Q-witness (n) (declare (ignore n)) 2))
  (defthm Q-witness-type
    (and (integerp (Q-witness n))
	 (<= 2 (Q-witness n)))
    :rule-classes :type-prescription)
  (defthm Q-property
    (< (g (Q-witness n) n) (f (+ 1 (nfix n))))
    :rule-classes nil))

; This function describes an induction scheme which is
; used in the following theorem.  To admit the function
; we had to provide a measure to prove termination.
(defun ind-hint (x y i)
  (declare (xargs  :measure (if (or (zp x) (zp i))
				0
			      (cons x i))))
  (if (or (zp x) (zp i))
      (list x y i)
    (list (ind-hint (+ -1 x)
		      (+ -1 y)
		      (Q-witness (+ -1 y)))
	  (ind-hint x
		      (f y)
		      (+ -1 i)))))

; This is the main lemma.
(defthm f-i-x->=-x-lemma
  (implies (and (np x)
		(np y)
		(np i)
		(<= 1 i)
		(<= x y))
	   (<= x (g i y)))
  :hints (("goal"
           :induct (ind-hint x y i))
	  ("subgoal *1/2'"
	   :use (:instance Q-property
			   (n (+ -1 y)))))
  :rule-classes nil)

(defthm f-i-x->=-x
  (implies (np i)
           (<= (nfix x) (g i x)))
  :hints (("Goal"
	   :use (:instance f-i-x->=-x-lemma
			   (y x))))
  :rule-classes nil)

(defthm f-lower-bound
  (<= (nfix n) (f n))
  :hints (("Goal"
	   :use (:instance f-i-x->=-x-lemma
			   (x n)
			   (y n)
			   (i 1))))
  :rule-classes nil)

(defthm f-monotonicity-lemma
  (implies (np n)
	   (< (f n) (f (+ 1 n))))
  :hints (("Goal"
	   :use (Q-property
		 (:instance f-i-x->=-x
			    (x (f n))
			    (i (+ -1 (Q-witness n))))))))

(defun nat-ind (x)
  (if (zp x)
      x
    (nat-ind (- x 1))))

(defthm f-monotonicity
  (implies (and (np x)
                (np y)
                (<= x y))
           (<= (f x) (f y)))
  :hints (("goal"
           :induct (nat-ind y))
          ("subgoal *1/2.1"
           :use ((:instance f-monotonicity-lemma (n (- y 1)))))))

(defthm Q-witness-less-than-two
  (and (equal (<= 2 (Q-witness n)) t)
       (equal (< (Q-witness n) 2) nil))
  :hints (("Goal"
	   :use Q-witness-type)))

(defthm g-f-rewrite
  (implies (integerp n)
	   (equal (g i (f n))
		  (g (+ 1 (nfix i)) n)))
  :hints (("Goal"
	   :expand (g (+ 1 (nfix i)) n))))

; We need to disable g, otherwise ACL2 goes into an infinite
; loop when tries to rewite a formula with g in it.
(in-theory (disable g))

(defthm f-upper-bound
  (implies (np n)
	   (<= (f n) n))
  :hints (("Goal"
	   :in-theory (disable f-monotonicity)
	   :use (Q-property
		 (:instance f-monotonicity
			    (x (+ 1 n))
			    (y (f n)))
		 (:instance f-i-x->=-x
			    (x (f (f n)))
			    (i (+ -2 (Q-witness n)))))))
  :rule-classes nil)

; This is the main theorem.
(defthm f-is-id
  (implies (np n)
	   (equal (f n) n))
  :hints (("Goal"
	   :use (f-lower-bound f-upper-bound))))
