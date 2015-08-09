(in-package "ACL2")

(include-book "trajectory")
;;;
;;;
;;;
(defuntyped l-p (l) t
  booleanp nil
  (if (equal l t)
      t
    (case-match l
		(('is i b)    (and (naturalp i) (booleanp b)))
		(('and l1 l2) (and (l-p l1) (l-p l2)))
		(('when b l1) (and (booleanp b) (l-p l1)))
		(('next l1)   (l-p l1)))))
;;;
;;;
;;;
(defuntyped l-depth ((l-p l)) t
  naturalp 0
  (if (equal l t)
      1
    (case-match l
		(('is & &)    1)
		(('and l1 l2) (max (l-depth l1) (l-depth l2)))
		(('when & l1) (l-depth l1))
		(('next l1)   (1+ (l-depth l1)))
		(&            0))))

(defthm l-def-l-p-positive
  (implies (l-p l)
	   (< 0 (l-depth l))))

;;;
;;;
;;;

(defuntyped l-maxn ((l-p l)) t
  naturalp 0
  (if (equal l t)
      0
    (case-match l
		(('is n &)    (1+ n))
		(('and l1 l2) (max (l-maxn l1) (l-maxn l2)))
		(('when & l1) (l-maxn l1))
		(('next l1)   (l-maxn l1))
		(&            0))))
;;;
;;;
;;;

(defuntyped l-evalp (l n m) t
  booleanp nil
  (if (and (l-p l) (positivep n) (naturalp m))
      (if (equal l t)
	  t
	(case-match l
		    (('is i &)  (< i m)  )
		    (('and l1 l2) (and	(l-evalp l1 n m)
					(l-evalp l2 n m)))
		    (('when & l1) (and (l-evalp l1 n m)))
		    (('next l1)   (l-evalp l1 (1- n) m))
		    (&            nil)))
    nil))

(defthm l-evalp-larger-m
  (implies (and (l-evalp l n m)
		(naturalp m1)
		(< m m1))
	   (l-evalp l n m1)))
(defthm l-evalp-larger-or-equal-m
  (implies (and (l-evalp l n m)
		(naturalp m1)
		(<= m m1))
	   (l-evalp l n m1)))
(defthm l-evap-n-if-l-evalp-n-minus-1
  (implies (and (positivep n)
		(l-evalp l (1- n) m))
	   (l-evalp l n m)))

(defthm l-evalp-larger-n
  (implies (and (naturalp n)
		(naturalp n1)
		(< n n1)
		(l-evalp l n m)
		)
	   (l-evalp l n1 m))
  :hints (("Goal" :induct (nat-induct n1))))

(defthm l-evalp-larger-or-equal-n
  (implies (and (naturalp n)
		(naturalp n1)
		(<= n n1)
		(l-evalp l n m)
		)
	   (l-evalp l n1 m)))

(defthm l-evalp-larger-n-larger-m
  (implies (and (naturalp n)
		(naturalp n)
		(integerp n1)
		(integerp m1)
		(< n n1)
		(< m m1)
		(l-evalp l n m))
	   (l-evalp l n1 m1))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable
		       l-evalp-larger-n l-evalp-larger-m
		       l-evalp-larger-or-equal-n l-evalp-larger-or-equal-m
		       )
	   :use ((:instance l-evalp-larger-n (m m1) )
		 (:instance l-evalp-larger-m ) ) ) ) )

(defthm l-evalp-larger-or-equal-n-larger-or-equal-m
  (implies (and (naturalp n)
		(naturalp n)
		(integerp n1)
		(integerp m1)
		(<= n n1)
		(<= m m1)
		(l-evalp l n m))
	   (l-evalp l n1 m1))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable  l-evalp-larger-n l-evalp-larger-m
                                L-EVALP-LARGER-OR-EQUAL-M)
	   :use ((:instance l-evalp-larger-n (m m1) )
		 (:instance l-evalp-larger-m ) ) ) ) )

(defthm l-evalp-when-n-ge-l-depth-and-l-maxn
  (implies (and (l-p l)
		(naturalp n)
		(<= (l-depth l) n))
	   (l-evalp l n (l-maxn l))))

(defthm l-evalp-when-n-l-depth-and-l-maxn
  (implies (l-p l)
	   (l-evalp l (l-depth l) (l-maxn l))))
;;;
;;;
;;;

(defuntyped l-eval ((l-p l) (r-p r)) t
  booleanp nil
  (if (consp r)
      (if (equal l t)
	  t
	(case-match l
		    (('is n b)    (if (< n (len (car r)))
				      (b-lte b (nth n (car r)))
				    nil))
		    (('and l1 l2) (and (l-eval l1 r) (l-eval l2 r)))
		    (('when b l1) (implies b (l-eval l1 r)))
		    (('next l1)   (l-eval l1 (cdr r)))))
    nil))

(defthm lemma-1
  (implies (and (l-eval l r1)
		(r-lte r1 r2))
	   (l-eval l r2)))




(defthm l-eval-r-lub-1
  (implies (and (r-p r1)
		(r-p r2)
		(l-eval l r1)
		)
	   (l-eval l (r-lub r1 r2)))
  :hints (("Goal" :expand ((R-LUB (CONS R3 R4) R2))))
  )

(defthm l-eval-r-lub-2
  (implies (and (r-p r1)
		(r-p r2)
		(l-eval l r2)
		)
	   (l-eval l (r-lub r1 r2)))
  :hints (("Goal" :use ((:instance r-lub-commutes (r1 r2) (r2 r1))
			(:instance l-eval-r-lub-1 (r1 r2) (r2 r1)))))
  )

;;;
;;;
;;;

(defuntyped l-defseq ((l-p l) (naturalp n) (naturalp m)) t
  r-p nil
  (if (l-evalp l n m)
      (if (equal n 0)
	  nil
	(if (equal l t)
	    (cons (s-make m 'x) (l-defseq t (1- n) m))
	  (case-match l
		      (('is i b)
		       (cons (update-nth i b (s-make m 'x))
			     (l-defseq t (1- n) m)))
		      (('and l1 l2)
		       (r-lub (l-defseq l1 n m) (l-defseq l2 n m)))
		      (('when b l1)
		       (if b
			   (l-defseq l1 n m)
			 (cons (s-make m 'x) (l-defseq t (1- n) m))))
		      (('next l1)
		       (cons (s-make m 'x)
			     (l-defseq l1 (1- n) m)))
		      (&            nil)))
	)
    nil)
  :measure (+ (acl2-count l) (nfix n))
  )

(defmacro defseq (a)  `(l-defseq ,a (l-depth ,a) (l-maxn ,a)))

(defthm len-l-defseq
  (implies (and (l-evalp l n m))
	   (equal (len (l-defseq l n m)) n)))


(defthm l-defseq-r-nmp
  (implies (and (l-evalp l n m))
	   (r-nmp (l-defseq l n m) n m)))


(defthm l-depth-not-zero
  (IMPLIES (L-P L)
	   (NOT (EQUAL (L-DEPTH L) 0))))


(defthm l-defseq-consp
  (implies (and (l-p l)
		(naturalp n)
		(naturalp m)
		(l-evalp l n m)
		)
	   (consp (l-defseq l n m))))



(defuntyped l-induct ((l-p l)) t
  boolean-listp nil
  (if (equal l t)
      nil
    (case-match l
		(('is & &)    nil)
		(('and l1 l2) (append (l-induct l1) (l-induct l2)))
		(('when b l1) (if b nil (l-induct l1)))
		(('next l1)   (l-induct l1)))
    ))


(defuntyped l-induct-n ((l-p l) (integerp n)) t
  boolean-listp nil
  (if (equal l t)
      nil
    (case-match l
		(('is & &)    nil)
		(('and l1 l2) (append (l-induct-n l1 n) (l-induct-n l2 n)))
		(('when b l1) (if b nil (l-induct-n l1 n)))
		(('next l1)   (l-induct-n l1 (1- n))))
    ))

(defuntyped l-induct-rn ((l-p l) (r-p r) (integerp n)) t
  boolean-listp nil
  (if (consp r)
      (if (equal l t)
	  nil
	(case-match l
		    (('is & &)    nil)
		    (('and l1 l2) (append (l-induct-rn l1 r n)
					  (l-induct-rn l2 r n)))
		    (('when b l1) (if b (l-induct-rn l1 r n) nil))
		    (('next l1)   (l-induct-rn l1 (cdr r) (1- n)))))
    nil))




(defthm l-eval-of-l-defseq-holds-try-1
  (implies (and (l-p l)
		(l-evalp l n m))
	   (l-eval l (l-defseq l n m))))

(defthm l-eval-of-l-defseq-holds
  (implies (l-p l)
	   (l-eval l (l-defseq l (l-depth l) (l-maxn l)))))

(defthm l-eval-of-defseq-holds
  (implies (l-p l)
	   (l-eval l (defseq l))))
;;;
;;;
;;;

(defthm l-defseq-t-is-s-make-x
  (implies (and (naturalp n)
		(naturalp m)
		)

	   (equal (l-defseq t n m)
		  (r-make n (s-make m 'x))))

  :hints (("Goal" :induct (nat-induct n)))

  )


(defthm l-eval-implies-r-lte-l-defseq
  (implies (and (l-p l)
		(r-p r)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m)
		(l-evalp l n m)
		(l-eval l r)
		)
	   (r-lte (l-defseq l n m) r))
   :hints (("Goal"
;	    :induct (l-induct-rn l r n)
	    :do-not '(generalize)
	    )))



(defthm l-defseq-weakest
  (implies (and (l-p l)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m)

		(l-evalp l n m)

		(l-eval l r)


		(r-lte r (l-defseq l n m))


		)
	   (equal (l-defseq l n m) r))
  :hints (("Subgoal *1/4'''"
	   :use ((:instance r-lte-antisymmetric
			    (a (R-LUB (L-DEFSEQ L3 n M)
				      (L-DEFSEQ L5 n M)))
			    (b R)
			    ))
	   ))

  )



(defthm not-r-lte-r-lub-l-defseq-1
 (IMPLIES (AND (L-P L3)
	       (L-P L5)
	       (R-P R)
	       (CONSP R)
	       (NOT (L-EVAL L3 R))
	       (NOT (R-LTE (L-DEFSEQ L3 n M) R))
	       (naturalp n)
	       (INTEGERP M)
	       (<= 0 M)
	       (R-nMP R n M)
	       (L-EVALP L3 n M)
	       (L-EVALP L5 n M)
	       (NOT (EQUAL n 0)))
	  (NOT (R-LTE (R-LUB (L-DEFSEQ L3 n M)
			     (L-DEFSEQ L5 n M))
		      R)))
 :hints (("Goal" :use ((:instance not-r-lte-1-implies-not-r-lte-r-lub
				  (n n)
				  (m m)
				  (r1 (L-DEFSEQ L3 n M))
				  (r2 (L-DEFSEQ L5 n M))
				  (r r)
				  )) ))
 )


(defthm l-eval-2
  (IMPLIES (AND (L-P L3)
		(L-P L5)
		(R-P R)
		(CONSP R)
		(L-EVAL L3 R)
		(NOT (R-LTE (L-DEFSEQ L5 N M) R))
		(INTEGERP M)
		(<= 0 M)
		(R-nMP R n M)
		(L-EVALP L3 N M)
		(L-EVALP L5 N M)
		(NOT (EQUAL N 0))
		(R-LTE (R-LUB (L-DEFSEQ L3 N M)
			      (L-DEFSEQ L5 N M))
		       R))
	   (L-EVAL L5 R))
 :hints (("Goal" :use ((:instance not-r-lte-2-implies-not-r-lte-r-lub
				  (n n)
				  (m m)
				  (r1 (L-DEFSEQ L3 N M))
				  (r2 (L-DEFSEQ L5 N M))
				  (r r)
				  )) ))
 )

(defthm r-lte-l-defseq-implies-l-eval
  (implies (and (l-p l)
		(r-p r)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m)
		(l-evalp l n m)
		(r-lte (l-defseq l n m) r)
		)
	   (l-eval l r))
  :hints (("Goal"
	   :induct (l-induct-rn l r n)
	   :do-not '(generalize fertilize)
	   )
	  ("Subgoal *1/3.4''" :use ((:instance l-eval-2)))
	  ("Subgoal *1/3.1''" :use ((:instance l-eval-2)))
	  ))

(defthm lemma-2-pre
  (implies (and (l-p l)
		(r-p r)
		(naturalp n)
		(naturalp m)
		(r-nmp r n m)
		(l-evalp l n m))
	   (iff (l-eval l r)
		(r-lte (l-defseq l n m) r)))
  :hints (("Goal" :use ((:instance r-lte-l-defseq-implies-l-eval)
			(:instance l-eval-implies-r-lte-l-defseq)))))

(defthm lemma-2
  (implies (and (l-p l)
		(r-p r)
		(r-nmp r (l-depth l) (l-maxn l))
		)
	   (iff (l-eval l r)
		(r-lte (defseq l) r)))
  :hints (("Goal"
	   :use ((:instance lemma-2-pre
			    (n (l-depth l))
			    (m (l-maxn l))))
	   ))
  )
