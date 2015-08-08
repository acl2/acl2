(in-package "ACL2")

(include-book "boolean")

(deflisttyped s-p b-p)

(defuntyped n-p (n (s-p s)) t
  booleanp nil
  (and (naturalp n)
       (< n (len s))))
;;;
;;; S-LTE and facts
;;;
(defuntyped s-lte ((s-p s1) (s-p s2)) t
  booleanp nil
  (if (and (consp s1) (consp s2))
      (and (b-lte (car s1) (car s2))
	   (s-lte (cdr s1) (cdr s2)))
    (and (equal s1 nil)
	 (equal s2 nil))))

(defthm s-lte-reflexive
  (implies (s-p s)
	   (s-lte s s)))

(defthm s-lte-antisymmetric
  (implies (and (s-p a)
		(s-p b)
		(s-lte a b)
		(s-lte b a))
	   (equal a b))
  :rule-classes nil)

(defthm s-lte-transitive
  (implies (and (s-p a)
		(s-p b)
		(s-lte a b)
		(s-lte b c))
	   (s-lte a c)))

(defthm s-lte-s1-not-x-s2-is-top
  (implies (and (s-p s1)
		(s-p s2)
		(n-p n s1)
		(n-p n s2)
		(not (equal (nth n s1) (nth n s2)))
		(not (equal (nth n s1) 'x))
		(s-lte s1 s2)
		)
	   (equal (nth n s2) 'top)))

(defthm s-lte-implies-s-get-is-b-lte
  (implies (and (s-lte s1 s2))
	   (b-lte (nth n s1) (nth n s2))))

(defthm s-lte-implies-len-equal
  (implies (s-lte s1 s2)
	   (equal (len s1) (len s2)))
  :rule-classes nil)

(defthm s-lte-update-nth
  (implies (and (s-p s1)
		(s-p s2)
		(s-lte s1 s2)
		(b-lte b1 b2)
		)
	   (s-lte (update-nth i b1 s1)
		  (update-nth i b2 s2))))



;;;
;;; S-MAKE
;;;
(defuntyped s-make ((naturalp n) (b-p b)) t
  s-p nil
  (if (positivep n)
      (cons b (s-make (1- n) b))
    nil))

(defthm s-make-len
  (implies (and (naturalp n)
		(b-p b))
	   (equal (len (s-make n b))
		  n)))

(defthm s-make-collapse-cons
  (IMPLIES (POSITIVEP N)
	   (equal (CONS 'X (S-MAKE (+ -1 N) 'X))
		  (S-MAKE N 'X))))

(defthm s-lte-s-make-x-s-len
  (implies (s-p s)
	   (s-lte (s-make (len s) 'x) s)) )

(defthm s-lte-s-make-x-n
  (implies (and (s-p s)
		(naturalp n)
		(equal (len s) n)
		)
	   (s-lte (s-make n 'x) s))  )


(defthm s-lte-when-update-nth-is-b-lte-of-x
  (implies (and (s-p s)
		(naturalp n)
		(naturalp i)
		(equal (len s) n)
		(b-lte b (nth i s))
		(< i n)
		)
	   (s-lte (update-nth i b (s-make n 'x))
		  s))
  :hints (("Goal" :induct (nat-induct n))
	  ("Subgoal *1/2.3"
	   :use ((:instance s-lte-update-nth
			    (s1 (CONS 'X (S-MAKE (+ -1 (LEN S)) 'X)))
			    (s2 s)
			    (b1 'x)
			    (b2 (nth i s))
			    (i i)))
	   )
	  ("Subgoal *1/2"
	   :use ((:instance s-lte-update-nth
			    (s1 (S-MAKE (LEN S) 'X))
			    (s2 s)
			    (b1 B)
			    (b2 (nth i s))
			    (i i)))
	   )
	  )
  )

;;;
;;; S-LUB
;;;
(defuntyped s-lub (s1 s2) t
  s-p nil
  (if (and (s-p s1) (s-p s2))
      (if (consp s1)
	  (if (consp s2)
	      (cons (b-lub (car s1) (car s2))
		    (s-lub (cdr s1) (cdr s2)))
	    s1)
	s2)
    nil))

(defthm s-lub-len
  (implies (and (s-p s1)
		(s-p s2))
	   (equal (len (s-lub s1 s2))
		  (max (len s1) (len s2)))))

(defthm s-lub-commutes
  (equal (s-lub s1 s2) (s-lub s2 s1))
  :rule-classes nil)

(defthm s-lub-s1
  (implies (and (s-p s1)
		(s-p s2)
		(equal (len s1) (len s2)))
	   (s-lte s1 (s-lub s1 s2))))

(defthm s-lub-s2
  (implies (and (s-p s1)
		(s-p s2)
		(equal (len s1) (len s2)))
	   (s-lte s2 (s-lub s1 s2))))

(defthm nth-s-lub-is-b-lub-nths
  (implies (and (s-p s1)
		(s-p s2)

		(n-p n s1)
		(n-p n s2)
		)
	   (equal (nth n (s-lub s1 s2))
		  (b-lub (nth n s1)
			 (nth n s2)))))

(defthm s-lub-s-make-x
  (implies (and (s-p s)
		(naturalp n)
		(equal (len s) n))
	   (equal (s-lub (s-make n 'x) s)
		  s)))

(defthm l-eval-r-lte-aaa-1
  (implies (and (s-lte s1 s2)
		(equal (nth n s1) 'top)
		)
	   (equal (nth n s2) 'top)))

(defthm l-eval-r-lte-aaa-2
  (implies (and (s-p s)
		(naturalp n))
	   (b-p (nth n s)))
  :hints (("Goal" :in-theory (enable b-p))))

(defthm l-eval-r-lte-aaa-3
  (implies (and (s-lte s1 s2)
		(booleanp (nth n s1))
		(not (equal (nth n s2) 'top))
		)
	   (booleanp (nth n s2))))

(defthm l-eval-r-lte-aaa-4
  (implies (and (s-lte s1 s2)
		(booleanp (nth n s1))
		(not (equal (nth n s2) 'top))
		)
	   (equal (nth n s2) (nth n s1))))


(defthm nth-s-lub-7
  (IMPLIES (AND (INTEGERP L3)
              (<= 0 L3)
              (BOOLEANP L5)
              (S-P R3)
              ;(R-P R4)
              (S-P R5)
              ;(R-P R6)
              (EQUAL (NTH L3 R3) 'TOP)
              (NOT (EQUAL (NTH L3 (S-LUB R3 R5)) 'TOP)))
         (EQUAL (NTH L3 (S-LUB R3 R5)) L5)))

(defthm nth-s-lub-8
  (IMPLIES (AND (INTEGERP L3)
              (<= 0 L3)
              (S-P R3)
              (S-P R5)
              (EQUAL (NTH L3 R3) 'TOP))
         (EQUAL (NTH L3 (S-LUB R3 R5)) 'TOP)))


(defthm nth-s-lub--9
  (implies (and (s-p s1)
		(s-p s2)
		(naturalp n)
		(< n (len s1))
		(booleanp (nth n s1))
		(not (equal (nth n (s-lub s1 s2)) 'top))
		)
	   (equal (nth n (s-lub s1 s2))
		  	  (nth n s1))))

(defthm s-lte-s-make-is-s-make
  (implies (and ;(r-p r1)
		(s-lte r1 (s-make (len r1) 'x))
		)
	   (equal (s-make (len r1) 'x) r1)))

(defthm equal-s-make-bottm
  (implies (s-lte s (s-make (len s) 'x))
	   (equal (s-make (len s) 'x) s)))

(defthm equal-s-make-bottm-2
  (implies (and (naturalp m)
		(equal (len s) m)
		(s-lte s (s-make m 'x)))
	   (equal (s-make m 'x) s)))

(defthm s-lub-same
  (implies (s-p s)
	   (equal (s-lub s s) s))
  :hints (("Goal" :in-theory (enable b-p))))

(defthm not-lte-x-boolean-if-top
  (implies (and (naturalp i)
		(booleanp b)
		(equal (nth i s) 'top)
		)
	   (not (s-lte s (update-nth i b (s-make (len s) 'x))))))




(defthm s-lte-x-with-update-implies-equal
 (IMPLIES (AND (n-p i s)
	       ;(S-P s)
	       ;(< i (len s))
	       (S-LTE s
		      (UPDATE-NTH i (NTH i s)
				  (S-MAKE (LEN s) 'X)))

              ;(BOOLEANP (NTH i s))
	      )
         (EQUAL (UPDATE-NTH i (NTH i s)
                            (S-MAKE (LEN s) 'X))
                s)))
(defthm s-lte-smake-len
  (implies (and (s-p s)
		;(equal (len s) m)
		;(naturalp m)
		)
	   (s-lte (s-make (len s) 'x)
		  s)))

(defthm s-lte-s-make-m
  (implies (and (s-p s)
		(equal (len s) m)
		;(naturalp m)
		)
	   (s-lte (s-make m 'x)
		  s)))
(defthm s-lub-s-lte-s-lub
  (implies (and (s-p s)
		(s-p s)
		(s-p s)
		(s-p s)
		(s-lte s1 s3)
		(s-lte s2 s4))
	   (s-lte (s-lub s1 s2)
		  (s-lub s3 s4))))
(defthm not-s-lte-not-s-lte-s-lub-1
  (implies (and (s-p s)
		(s-p s1)
		(s-p s2)
		(equal (len s1) (len s))
		(not (s-lte s1 s)))
	   (not (s-lte (s-lub s1 s2) s))))

(defthm not-s-lte-not-s-lte-s-lub-2
  (implies (and (s-p s)
		(s-p s1)
		(s-p s2)
		(equal (len s2) (len s))
		(not (s-lte s2 s)))
	   (not (s-lte (s-lub s1 s2) s))))
