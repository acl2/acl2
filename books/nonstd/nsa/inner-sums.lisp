;;; This book proves some theorems about nested sums.  A sum
;;; $\sum_{i}{a_i} is handled as a function a(i) that computes the ith
;;; term and a function sum_i that adds up the function a(i).  Nested
;;; sums use an outer sum sum_i, and inner sum sum_i_j, and a function
;;; a(i,j) to compute the ith/jth term.

(in-package "ACL2")

(local (include-book "arithmetic/top" :dir :system))
(include-book "arithmetic/sumlist" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; We start by defining the function binop(i,j) which is used to
;; compute the term a_{i,j} in a nested sum.

(encapsulate
 ((binop (i j) t))

 (local
  (defun binop (i j)
    (+ i j)))

 (defthm binop-type-prescription
   (acl2-numberp (binop i j))
   :rule-classes (:rewrite :type-prescription))
 )

;; We will define some basic functions to compute various nested
;; sums.  Rather than computing the sum directoy, we build up a
;; sequence that has the elements we wish to add in the right order.
;; I.e., rather than returning a(i,1) + a(i,2) + ... + a(i,n), we
;; return the list (a(i,1), a(i,2), ..., a(i,n)).

;; Now, we define a function that "adds up" all the a_{i,j} elements
;; in the ith row.

(defun row-expansion-inner (i j n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (binop i j)
	    (row-expansion-inner i (1+ j) n))
    nil))

;; Using the function above, we can "sum" all the a_{i,j} elements by
;; "adding" each of the m rows.

(defun row-expansion-outer (i m n)
  (declare (xargs :measure (nfix (1+ (- m i)))))
  (if (and (integerp i) (integerp m) (<= 0 i) (<= i m))
      (cons (sumlist (row-expansion-inner i 0 n))
	    (row-expansion-outer (1+ i) m n))
    nil))

;; Similarly, we can "add up" all the a_{i,j} values in the jth column.

(defun col-expansion-inner (i j m)
  (declare (xargs :measure (nfix (1+ (- m i)))))
  (if (and (integerp i) (integerp m) (<= 0 i) (<= i m))
      (cons (binop i j) (col-expansion-inner (1+ i) j m))
    nil))

;; And them "sum" all the a_{i,j} by "adding up" all the columns.

(defun col-expansion-outer (j m n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (sumlist (col-expansion-inner 0 j m))
	    (col-expansion-outer (1+ j) m n))
    nil))

(in-theory (disable (:executable-counterpart row-expansion-inner)
		    (:executable-counterpart row-expansion-outer)
		    (:executable-counterpart col-expansion-inner)
		    (:executable-counterpart col-expansion-outer)))

;; This is just to specify that we want to "induct on n"....

(local
 (defun natural-induction-hint (n)
   (if (zp n)
       0
     (1+ (natural-induction-hint (1- n))))))

;; Now, if we add up all the rows up the (m-1)st row, we get the same
;; result as if we add up all the rows up to the mth row and then
;; subtract the mth row....

(defthm row-expansion-outer-split
  (implies (and (integerp i) (integerp m) (<= 0 i) (<= i m))
	   (equal (sumlist (row-expansion-outer i (1- m) n))
		  (- (sumlist (row-expansion-outer i m n))
		     (sumlist (row-expansion-outer m m n))))))

;; The sum of a column is zero when we start looking at elements
;; beyond the last row....

(defthm col-expansion-inner-out-of-bounds
  (implies (< m i)
	   (equal (col-expansion-inner i j m) nil)))

;; Now, we can see what happens when we add up all the a_{i,j} in
;; column j up to row m-1 -- it's the same as we add up all the
;; a_{i,j} up to row m and then subtract a_{m,j}.

(defthm col-expansion-inner-split
  (implies (and (integerp i) (integerp m) (<= 0 i) (<= i m))
	   (equal (sumlist (col-expansion-inner i j (1- m)))
		  (- (sumlist (col-expansion-inner i j m))
		     (binop m j)))))

;; From the above, we can conclude that if we add up all the columns
;; up to row m-1, it's the same as if we add up all the columns up
;; to row m and then subtract row m.

(defthm col-expansion-outer-split
  (implies (and (integerp m) (<= 0 m))
	   (equal (sumlist (col-expansion-outer j (1- m) n))
		  (- (sumlist (col-expansion-outer j m n))
		     (sumlist (row-expansion-inner m j n))))))

(in-theory (disable row-expansion-outer-split
		    col-expansion-inner-split
		    col-expansion-outer-split))

;; In the proofs to follow, we find many terms expanding empty
;; sequences (i.e., i>m or j>n or i<0, etc).  So, we show that these
;; terms can be ignored:

(defthm row-expansion-outer-negative-m
  (implies (< m 0)
	   (equal (row-expansion-outer i m n) nil)))

(defthm col-expansion-outer-negative-m
  (implies (< m 0)
	   (equal (sumlist (col-expansion-outer j m N)) 0)))

(defthm row-expansion-outer-negative-n
  (implies (< n 0)
	   (equal (sumlist (row-expansion-outer i m n)) 0)))

(defthm col-expansion-outer-negative-n
  (implies (< n 0)
	   (equal (col-expansion-outer j m n) nil)))

(defthm row-expansion-non-integer-m
  (implies (not (integerp m))
	   (equal (row-expansion-outer i m n) nil)))

(defthm col-expansion-outer-non-integer-m
  (implies (not (integerp m))
	   (equal (sumlist (col-expansion-outer j m n)) 0)))

(defthm row-expansion-non-integer-n
  (implies (not (integerp n))
	   (equal (sumlist (row-expansion-outer i m n)) 0)))

(defthm col-expansion-outer-non-integer-n
  (implies (not (integerp n))
	   (equal (col-expansion-outer j m n) nil)))

;; Next we consider the special case when the number of rows or
;; columns is equal to 1 -- i.e., when the largest index is zero (yes,
;; I'm a C++ programmer by day)

(defthm row-expansion-inner-i-j-0
  (equal (row-expansion-inner i j 0)
	 (if (equal j 0)
	     (list (binop i 0))
	   nil))
  :hints (("Goal" :expand (row-expansion-inner i j 0))))

(defthm row-expansion-outer-i-0-0
  (equal (row-expansion-outer i 0 0)
	 (if (and (equal i 0))
	     (list (binop 0 0))
	   nil))
  :hints (("Goal" :expand (row-expansion-outer i 0 0))))

(defthm row-expansion-outer-with-m=0
  (equal (sumlist (row-expansion-outer 0 0 n))
	 (sumlist (row-expansion-inner 0 0 n)))
  :hints (("Goal" :expand (row-expansion-outer 0 0 n))))

(defthm col-expansion-inner-i-j-0
  (equal (col-expansion-inner i j 0)
	 (if (equal i 0)
	     (list (binop 0 j))
	   nil))
  :hints (("Goal" :expand (col-expansion-inner i j 0))))

(defthm col-expansion-outer-j-0-0
  (equal (col-expansion-outer j 0 0)
	 (if (equal j 0)
	     (list (binop 0 0))
	   nil))
  :hints (("Goal" :expand (col-expansion-outer j 0 0))))

(defthm col-expansion-outer-with-m=0
  (equal (col-expansion-outer j 0 n)
	 (row-expansion-inner 0 j n))
  :hints (("Goal" :induct (col-expansion-outer j 0 n))))

;; This culminates to the following result, which happens to be the
;; base case for the proof that the row-sum is equal to the
;; column-sum.  In the case when there's only one row, you can compute
;; the sum by either adding "all" the row sums or by adding all the
;; column "sums".

(defthm ok-to-swap-inner-outer-expansions-base
  (implies (zp m)
	   (equal (sumlist (row-expansion-outer 0 m n))
		  (sumlist (col-expansion-outer 0 m n))))
  :hints (("Goal"
	   :cases ((not (integerp m))
		   (and (integerp m) (equal m 0))
		   (and (integerp m) (not (equal m 0)))))))

;; Another "empty" case:

(defthm row-expansion-outer-i>m
  (implies (> i m)
	   (equal (row-expansion-outer i m n) nil)))

;; The following lemma simply "opens up" some outer row sums.

(defthm row-expansion-outer-m-m-n
  (implies (and (integerp m) (<= 0 m))
	   (equal (sumlist (row-expansion-outer m m n))
		  (sumlist (row-expansion-inner m 0 n))))
  :hints (("Goal" :expand (row-expansion-outer m m n))))

;; And now the first important theorem!  The sum of all the a_{i,j}
;; can be computed either by adding the sum of the m rows or by adding
;; the sum of the n columns.  The results will be equal.

(defthm ok-to-swap-inner-outer-sums
  (equal (sumlist (row-expansion-outer 0 m n))
	 (sumlist (col-expansion-outer 0 m n)))
  :hints (("Goal"
	   :induct (natural-induction-hint m))
	  ("Subgoal *1/2"
	   :use ((:instance row-expansion-outer-split (i 0))
		 (:instance col-expansion-outer-split (j 0))))))

;; Now, we define a lower-triangular row sum.  Basically, instead of
;; adding up all the elements of the ith row, we only add up the
;; elements through the ith column -- a_{i,1} ... a_{i,i}.  So only
;; the values at or below the "diagonal" are non-zero.

(defun row-expansion-outer-lt (i m n)
  (declare (xargs :measure (nfix (1+ (- m i)))))
  (if (and (integerp i) (integerp m) (<= 0 i) (<= i m))
      (cons (sumlist (row-expansion-inner
		      i 0 (if (< i n) i n)))
	    (row-expansion-outer-lt (1+ i) m n))
    nil))


;; We define the same sum, but using column-sums instead.  The idea is
;; to add up the elements of column j but only starting at row j.
;; I.e., we add up a_{j,j}, a_{j+1,j}, ..., a_{m,j}.

(defun col-expansion-outer-lt (j m n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (sumlist (col-expansion-inner j j m))
	    (col-expansion-outer-lt (1+ j) m n))
    nil))

;; Here's a different approach on the same idea.  We define a new
;; b_{i,j} with the property that b_{i,j} = 0 for i<j.

(defun lt-binop (i j)
  (if (< i j)
      0
    (binop i j)))

;; So now, we can define its row-sum as before....

(defun row-expansion-inner-using-lt (i j n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (lt-binop i j)
	    (row-expansion-inner-using-lt i (1+ j) n))
    nil))

(defun row-expansion-outer-using-lt (i m n)
  (declare (xargs :measure (nfix (1+ (- m i)))))
  (if (and (integerp i) (integerp m) (<= 0 i) (<= i m))
      (cons (sumlist (row-expansion-inner-using-lt i 0 n))
	    (row-expansion-outer-using-lt (1+ i) m n))
    nil))

;; ... and also its column sum.

(defun col-expansion-inner-using-lt (i j m)
  (declare (xargs :measure (nfix (1+ (- m i)))))
  (if (and (integerp i) (integerp m) (<= 0 i) (<= i m))
      (cons (lt-binop i j)
	    (col-expansion-inner-using-lt (1+ i) j m))
    nil))

(defun col-expansion-outer-using-lt (j m n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (sumlist (col-expansion-inner-using-lt 0 j m))
	    (col-expansion-outer-using-lt (1+ j) m n))
    nil))

;; From the main theorem above, we can either add the rows or add the
;; columns, and the result won't matter.

(defthm ok-to-swap-inner-outer-sums-using-lt
  (equal (sumlist (row-expansion-outer-using-lt 0 m n))
	 (sumlist (col-expansion-outer-using-lt 0 m n)))
  :hints (("Goal"
	   :by (:functional-instance ok-to-swap-inner-outer-sums
				     (binop lt-binop)
				     (row-expansion-outer row-expansion-outer-using-lt)
				     (row-expansion-inner row-expansion-inner-using-lt)
				     (col-expansion-outer col-expansion-outer-using-lt)
				     (col-expansion-inner col-expansion-inner-using-lt)))))

;; Now suppose we look at a column sum starting at a_{i,j} when i >= j
;; -- it doesn't matter if we use the regular column sum or the
;; triangular sum.

(defthm col-expansion-inner-using-lt-to-binop-large-i
  (implies (and (integerp i) (integerp j) (integerp n)
		(<= 0 j) (<= j i))
	   (equal (col-expansion-inner i j n)
		  (col-expansion-inner-using-lt i j n)))
  :hints (("Goal" :induct (col-expansion-inner-using-lt i j n))))

;; If i<=j then the expansion of the column sum starting at a_{j,j} is
;; the same as the "triangular" expansion starting at a_{i,j}, since
;; the a_{i,j}, a_{i+1,j}, ..., a_{j,j} terms are all ignored by the
;; "triangular" sum.

(defthm col-expansion-inner-using-lt-to-binop
  (implies (and (integerp i) (integerp j) (integerp n)
		(<= 0 i) (<= i j))
	   (equal (sumlist (col-expansion-inner j j n))
		  (sumlist (col-expansion-inner-using-lt i j n))))
  :hints (("Goal" :induct (col-expansion-inner-using-lt i j n))))

;; So in particular, the triangular sum of the entire jth column is
;; equal to the sum of the column starting at a_{j,j}.

(defthm col-expansion-inner-j-j-n
  (implies (and (integerp j) (integerp n) (<= 0 j))
	   (equal (sumlist (col-expansion-inner j j n))
		  (sumlist (col-expansion-inner-using-lt 0 j n))))
  :hints (("Goal"
	   :by (:instance col-expansion-inner-using-lt-to-binop (i 0)))))

;; The triangular sum of the ith row starting from column j is zero if
;; j > i -- since a_{i,j} is ignored for i<j.

(defthm row-expansion-inner-using-lt-to-binop-large-j
  (implies (< i j)
	   (equal (sumlist (row-expansion-inner-using-lt i j m)) 0)))

;; From that, we can conclude that the sum of the ith row up to column
;; i is equal to the "triangular" sum of row i.

(defthm row-expansion-inner-using-lt-to-binop
  (implies (and (integerp i) (integerp n) (< i n))
	   (equal (sumlist (row-expansion-inner i j i))
		  (sumlist (row-expansion-inner-using-lt i j n)))))

;; Some more empty cases!  This time, we look at the sums of the
;; b_{i,j} -- recall that b_{i,j} is zero for i<j.

(defthm col-expansion-outer-lt-non-integerp-n
  (implies (not (integerp n))
	   (equal (col-expansion-outer-lt i m n) nil)))

(defthm col-expansion-outer-using-lt-non-integerp-n
  (implies (not (integerp n))
	   (equal (col-expansion-outer-using-lt i m n) nil)))

(defthm col-expansion-inner-using-lt-to-binop-large-j
  (implies (and (integerp i)
		(<= 0 i)
		(integerp j)
		(<= 0 j)
		(integerp m)
		(<= 0 m)
		(< m j))
	   (equal (sumlist (col-expansion-inner-using-lt i j m)) 0)))

;; What this means is that the triangular column sum of the a_{i,j} is
;; the same as the sum of the b_{i,j}, since b_{i,j} is equal to
;; a_{i,j} if i<=j and 0 otherwise.

(defthm col-expansion-outer-lt-=-col-expansion-outer-using-lt
  (implies (integerp m)
	   (equal (sumlist (col-expansion-outer-lt i m n))
		  (sumlist (col-expansion-outer-using-lt i m n))))
  :hints (("Goal" :induct (col-expansion-outer-using-lt i m n))
	  ("Subgoal *1/1.8"
	   :use ((:instance col-expansion-inner-using-lt-to-binop-large-j
			    (i 0)
			    (j i)
			    (m m)))
	   :in-theory (disable col-expansion-inner-using-lt-to-binop-large-j))
	  ("Subgoal *1/1.5"
	   :use ((:instance col-expansion-inner-using-lt-to-binop
			    (i 1)
			    (j i)
			    (n m)))
	   :in-theory (disable col-expansion-inner-using-lt-to-binop))

	  )
  :rule-classes
  ((:rewrite :corollary (equal (sumlist (col-expansion-outer-lt i m n))
			       (sumlist (col-expansion-outer-using-lt i m n))))))

;; Now, we try the same theorem, but using row sums instead.  First,
;; some boundary conditions.  When we're looking at a row beyond the
;; last row, both terms below are nil, and so they're equal.

(defthm row-expansion-inner-large-i
  (implies (<= n i)
	   (equal (row-expansion-inner i j n)
		  (row-expansion-inner-using-lt i j n))))

;; And since the terms b_{i,j} are zero for i<j, the sum of the ith
;; row can be computed by going up just to column i.

(defthm row-expansion-inner-large-n
  (implies (and (integerp i) (integerp n) (< i n))
	   (equal (sumlist (row-expansion-inner-using-lt i j n))
		  (sumlist (row-expansion-inner-using-lt i j i)))))

;; And so, the row sum of the b_{i,j} is the same as the triangular
;; sum of the a_{i,j}.

(defthm row-expansion-outer-lt-=-row-expansion-outer-using-lt
  (implies (integerp n)
	   (equal (row-expansion-outer-lt i m n)
		  (row-expansion-outer-using-lt i m n))))

;; Therefore, the triangular row sum and triangular column sum compute
;; the same value.

(defthm ok-to-swap-inner-outer-expansions-lt
  (implies (integerp n)
	   (equal (sumlist (row-expansion-outer-lt 0 m n))
		  (sumlist (col-expansion-outer-lt 0 m n)))))

;; Next, let's consider the special case of square "matrices".  I.e.,
;; when we have as many rows as columns.  First, we give the
;; definition of the row and column sums as just a special case of the
;; rectangular case.  Obviously, they compute the same value!

(defun row-expansion-outer-m=n-aux (i n)
  (row-expansion-outer i n n))

(defun col-expansion-outer-m=n-aux (j n)
  (col-expansion-outer j n n))

(defthm ok-to-swap-inner-outer-expansions-m=n-aux
  (equal (sumlist (row-expansion-outer-m=n-aux 0 n))
	 (sumlist (col-expansion-outer-m=n-aux 0 n))))

;; Now, we give a direct definition of the row sum...

(defun row-expansion-outer-m=n (i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (sumlist (row-expansion-inner i 0 n))
	    (row-expansion-outer-m=n (1+ i) n))
    nil))

;; ... as well as the column sum.

(defun col-expansion-outer-m=n (j n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (sumlist (col-expansion-inner 0 j n))
	    (col-expansion-outer-m=n (1+ j) n))
    nil))

;; Clearly, these functions return the same value as the original ones
;; that used the underlying rectangular sums.

(local
 (defthm row-col-expansion-outer-m=n-aux
   (and (equal (row-expansion-outer-m=n i n)
	       (row-expansion-outer-m=n-aux i n))
	(equal (col-expansion-outer-m=n i n)
	       (col-expansion-outer-m=n-aux i n)))))

;; So we can conclude that the row sum is the same as the column sum.

(defthm ok-to-swap-inner-outer-expansions-m=n
  (equal (sumlist (row-expansion-outer-m=n 0 n))
	 (sumlist (col-expansion-outer-m=n 0 n))))

;; Now we do the same step but using triangular sums.  First, we
;; define triangular sums of square matrices using the rectangular
;; definitions.  We show the two triangular sums must be equal to each
;; other.

(defun row-expansion-outer-lt-m=n-aux (i n)
  (row-expansion-outer-lt i n n))

(defun col-expansion-outer-lt-m=n-aux (j n)
  (col-expansion-outer-lt j n n))

(defthm ok-to-swap-inner-outer-expansions-lt-m=n-aux
  (implies (integerp n)
	   (equal (sumlist (row-expansion-outer-lt-m=n-aux 0 n))
		  (sumlist (col-expansion-outer-lt-m=n-aux 0 n)))))

;; Now, we give an explicit definition for the triangular sums.

(defun row-expansion-outer-lt-m=n (i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (sumlist (row-expansion-inner i 0 (if (< i n) i n)))
	    (row-expansion-outer-lt-m=n (1+ i)  n))
    nil))

(defun col-expansion-outer-lt-m=n (j n)
  (declare (xargs :measure (nfix (1+ (- n j)))))
  (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
      (cons (sumlist (col-expansion-inner j j n))
	    (col-expansion-outer-lt-m=n (1+ j) n))
    nil))

(local
 (defthm row-col-expansion-outer-lt-m=n-aux
   (and (equal (row-expansion-outer-lt-m=n i n)
	       (row-expansion-outer-lt-m=n-aux i n))
	(equal (col-expansion-outer-lt-m=n i n)
	       (col-expansion-outer-lt-m=n-aux i n)))))

;; And of course, we conclude that we can sum either rows first or
;; columns first.

(defthm ok-to-swap-inner-outer-expansions-lt-m=n
  (implies (integerp n)
	   (equal (sumlist (row-expansion-outer-lt-m=n 0 n))
		  (sumlist (col-expansion-outer-lt-m=n 0 n)))))

;; Finally, we consider a simple sum of a_0+a_1+...+a_n.  We show that
;; if we multiply each of a_i by a constant k, the sum of adding up
;; the k*a_i terms is the same as k times the sum of the a_i.

;; First, here is the definition of the a_i and k.

(encapsulate
 ((zeroop () t)
  (oneop (i) t))

 (local (defun zeroop () 0))
 (local (defun oneop (i) (fix i)))

 (defthm zeroop-type-prescription
   (acl2-numberp (zeroop))
   :rule-classes (:rewrite :type-prescription))

 (defthm oneop-type-prescription
   (acl2-numberp (oneop i))
   :rule-classes (:rewrite :type-prescription))
)

;; Now here is the sum of the a_i....

(defun expansion-oneop (i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (oneop i)
	    (expansion-oneop (1+ i) n))
    nil))

;; And here is the sum of the k*a_i....

(defun expansion-oneop-times-zeroop (i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (* (oneop i) (zeroop))
	    (expansion-oneop-times-zeroop (1+ i) n))
    nil))

;; And now, sum(k*a_0, k*a_1, ..., k*a_n) = k * sum(a_0, ..., a_n)

(defthm factor-constant-from-expansion
  (equal (sumlist (expansion-oneop-times-zeroop i n))
	 (* (sumlist (expansion-oneop i n)) (zeroop)))
  :hints (("Goal" :induct (expansion-oneop i n))))
