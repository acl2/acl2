(in-package "DM")

(include-book "ring")

;;----------------------------------------------------------------------------------------
;; Matrices of Ring Elements
;;----------------------------------------------------------------------------------------

;; mxn matrix:

(defun rmatp (a m n)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (null a)
    (and (consp a)
	 (rlistnp (car a) n)
	 (rmatp (cdr a) (1- m) n))))

(defthm len-rmatp
  (implies (and (natp m) (rmatp a m n))
	   (equal (len a) m)))

(defthm true-listp-rmatp
  (implies (rmatp a m n)
	   (true-listp a)))

;; ith row of a:

(defun row (i a)
  (nth i a))

(defthm rlistnp-row
  (implies (and (natp m) (natp n) (rmatp a m n)
	        (natp i) (< i m))
           (rlistnp (row i a) n)))

(defthm len-rmat-row
  (implies (and (natp m) (natp n) (rmatp a m n)
	        (natp i) (< i m))
	   (equal (len (nth i a))
		  n)))

;; jth column or a:

(defun col (j a)
  (if (consp a)
      (cons (nth j (car a))
            (col j (cdr a)))
    ()))

(defthm rlistnp-col
  (implies (and (natp m) (natp n) (rmatp a m n)
		(natp j) (< j n))
	   (rlistnp (col j a) m)))

(defthm len-rmat-col
  (implies (and (natp m) (natp n) (rmatp a m n))
	   (equal (len (col j a))
		  m)))

;; The entry of a matrix in row i and column j:

(defun entry (i j mat)
  (nth j (nth i mat)))

(defthmd rp-entry
  (implies (and (natp m) (natp n) (rmatp a m n)
	        (natp i) (< i m) (natp j) (< j n))
           (rp (entry i j a))))

(defthmd nth-row
  (equal (nth j (row i a))
	 (entry i j a)))

(defthmd nth-col
  (equal (nth i (col j a))
         (entry i j a)))

;; Replace kth row of a with r:

(defun replace-row (a k r)
  (if (zp k)
      (cons r (cdr a))
    (cons (car a) (replace-row (cdr a) (1- k) r))))

(defthm nth-replace-row
  (implies (and (natp k) (< k (len a)) (natp j) (< j (len a)))
           (equal (nth j (replace-row a k r))
	          (if (= j k)
		      r
		    (nth j a)))))

(defthm rmatp-replace-row
  (implies (and (rmatp a m n) (natp m) (natp n) (natp k) (< k m) (rlistnp r n))
           (rmatp (replace-row a k r) m n)))

(defthm len-replace-row
  (implies (and (natp k) (< k (len a)))
           (equal (len (replace-row a k r))
                  (len a))))

(defthmd replace-rmat-row-self
  (implies (and (rmatp a m n) (posp m) (posp n)
                (natp i) (< i m))
	   (equal (replace-row a i (row i a))
	          a)))

(defthmd replace-2-rmat-rows
  (implies (and (rmatp a m n) (posp m) (posp n)
                (natp i) (< i m) (natp j) (< j m) (not (= i j))
		(rlistnp x n) (rlistnp y n))
	   (equal (replace-row (replace-row a i x) j y)
	          (replace-row (replace-row a j y) i x))))

;; To show that 2 matrices of the same dimensions are equal, it surrices to show that
;; corresponding entries are equal.  That is, if 2 mxn matrices are not equal, then some
;; pair of corresponding entries are not equal:

(defund entry-diff (a b)
  (let* ((i (nth-diff a b))
	 (j (nth-diff (row i a) (row i b))))
    (cons i j)))

(defthmd rmat-entry-diff-lemma
  (implies (and (posp m) (posp n) (rmatp a m n) (rmatp b m n) (not (equal a b)))
	   (let* ((pair (entry-diff a b))
		  (i (car pair))
		  (j (cdr pair)))
	     (and (natp i) (< i m)
		  (natp j) (< j n)
		  (not (equal (entry i j a) (entry i j b))))))
  :hints (("Goal" :in-theory (enable entry-diff)
	   :use ((:instance nth-diff-diff (x a) (y b))
	         (:instance rlistnp-row (i (nth-diff a b)))
	         (:instance rlistnp-row (i (nth-diff a b))  (a b))
	         (:instance nth-diff-diff (x (row (nth-diff a b) a)) (y (row (nth-diff a b) b)))))))

;; Addition of mxn matrices:

(defun rmat-add (a b)
  (if (consp a)
      (cons (rlist-add (car a) (car b))
	    (rmat-add (cdr a) (cdr b)))
    ()))

(defthm rmatp-rmat-add
  (implies (and (rmatp a m n) (rmatp b m n))
           (rmatp (rmat-add a b) m n)))

(defthmd rmat-add-comm
  (implies (and (rmatp a m n) (rmatp b m n))
           (equal (rmat-add a b)
		  (rmat-add b a)))
  :hints (("Subgoal *1/3" :in-theory (enable rlist-add-comm))))

(defthmd rmat-add-assoc
  (implies (and (rmatp a m n) (rmatp b m n) (rmatp c m n))
           (equal (rmat-add a (rmat-add b c))
		  (rmat-add (rmat-add a b) c)))
  :hints (("Subgoal *1/4" :use ((:instance rlist-add-assoc (x (car a)) (y (car b)) (z (car c)))))))

(defthmd row-rmat-add
  (implies (and (rmatp a m n) (rmatp b m n) (natp m) (natp n) (natp i) (< i m))
           (equal (row i (rmat-add a b))
		  (rlist-add (row i a) (row i b)))))

(defthmd col-rmat-add
  (implies (and (rmatp a m n) (rmatp b m n) (natp m) (natp n) (natp j) (< j n))
           (equal (col j(rmat-add a b))
		  (rlist-add (col j a) (col j b)))))

(defthmd rmat-add-entry
  (implies (and (rmatp a m n) (rmatp b m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (rmat-add a b))
	          (r+ (entry i j a) (entry i j b)))))

;; Multiply each entry of a by c:

(defun rmat-scalar-mul (c a)
  (if (consp a)
      (cons (rlist-scalar-mul c (car a))
	    (rmat-scalar-mul c (cdr a)))
    ()))

(defthmd rmatp-rmat-scalar-mul
  (implies (and (rp c) (rmatp a m n))
	   (rmatp (rmat-scalar-mul c a) m n)))

(defthmd rmat-scalar-mul-assoc
  (implies (and (rp c) (rp d) (rmatp a m n))
	   (equal (rmat-scalar-mul c (rmat-scalar-mul d a))
		  (rmat-scalar-mul (r* c d) a))))

(defthmd rmat-scalar-mul-dist-1
  (implies (and (rp c) (rmatp a m n) (rmatp b m n))
	   (equal (rmat-scalar-mul c (rmat-add a b))
		  (rmat-add (rmat-scalar-mul c a) (rmat-scalar-mul c b)))))
 
(defthmd rmat-scalar-mul-dist-2
  (implies (and (rp c) (rp d) (rmatp a m n))
	   (equal (rmat-scalar-mul (r+ c d) a)
		  (rmat-add (rmat-scalar-mul c a) (rmat-scalar-mul d a)))))

(defthmd row-rmat-scalar-mul
  (implies (and (rp c) (rmatp a m n) (natp m) (natp n) (natp i) (< i m))
	   (equal (row i (rmat-scalar-mul c a))
		  (rlist-scalar-mul c (row i a)))))

(defthmd col-rmat-scalar-mul
  (implies (and (rp c) (rmatp a m n) (natp m) (natp n) (natp j) (< j n))
	   (equal (col j (rmat-scalar-mul c a))
		  (rlist-scalar-mul c (col j a)))))

(defthmd rmat-scalar-mul-entry
  (implies (and (rp c) (rmatp a m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
	   (equal (entry i j (rmat-scalar-mul c a))
		  (r* c (entry i j a)))))

;; Sum of all entries of a:

(defun rmat-sum (a)
  (if (consp a)
      (r+ (rlist-sum (car a))
	  (rmat-sum (cdr a)))
    (r0)))

(in-theory (disable (rmat-sum)))

(defthm rp-rmat-sum
  (implies (rmatp a m n)
           (rp (rmat-sum a))))

;;----------------------------------------------------------------------------------------
;; Transpose of a Matrix
;;----------------------------------------------------------------------------------------

;; The transpose of a matrix is the list of its columns:

(defun transpose-mat-aux (a j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (col j a) (transpose-mat-aux a (1+ j) n))
    ()))

(defund transpose-mat (a)
  (transpose-mat-aux a 0 (len (car a))))

(local-defthmd rmatp-transpose-mat-aux
  (implies (and (natp m) (natp n) (rmatp a m n) (natp j) (< j n))
	   (rmatp (transpose-mat-aux a j n) (- n j) m)))

(defthmd rmatp-transpose
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (rmatp (transpose-mat a) n m))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance rmatp-transpose-mat-aux (j 0))
	                (:instance len-rmat-row (i 0))))))

(local-defun transpose-mat-aux-induct (i j)
  (if (zp i)
      j
    (list (transpose-mat-aux-induct (1- i) (1+ j)))))

(local-defthmd nth-transpose-mat-aux
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i (- n j)))
	   (equal (nth i (transpose-mat-aux a j n))
		  (col (+ j i) a)))
  :hints (("Goal" :induct (transpose-mat-aux-induct i j))
	  ("Subgoal *1/1" :expand ((TRANSPOSE-MAT-AUX A J N)))))

(defthm nth-transpose-rmat
  (implies (and (posp m) (posp n) (rmatp a m n)
                (natp i) (< i n))
	   (equal (nth i (transpose-mat a))
		  (col i a)))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance nth-transpose-mat-aux (n (len (car a))) (j 0))
			(:instance len-rmat-row (i 0))))))

(defthm transpose-rmat-entry
  (implies (and (posp m) (posp n) (rmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a))))

(local-defthmd rmatp-transpose-2
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (rmatp (transpose-mat (transpose-mat a)) m n))
  :hints (("Goal" :in-theory (enable rmatp-transpose))))

(local-defthmd transpose-2-entry
  (implies (and (posp m) (posp n) (rmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry i j (transpose-mat (transpose-mat a)))
		  (entry i j a)))
  :hints (("Goal" :in-theory (e/d (rmatp-transpose) (entry)))))

(defthm transpose-rmat-2
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (transpose-mat (transpose-mat a))
	          a))
  :hints (("Goal" :in-theory (disable entry)
                  :use (rmatp-transpose-2
		        (:instance transpose-2-entry
			            (i (car (entry-diff a (transpose-mat (transpose-mat a)))))
		                    (j (cdr (entry-diff a (transpose-mat (transpose-mat a))))))
		        (:instance rmat-entry-diff-lemma (b (transpose-mat (transpose-mat a))))))))

(defthmd col-transpose-rmat
  (implies (and (posp m) (posp n) (rmatp a m n)
                (natp j) (< j m))
	   (equal (col j (transpose-mat a))
	          (row j a)))
  :hints (("Goal" :use (rmatp-transpose
                        (:instance nth-transpose-rmat (a (transpose-mat a)) (m n) (n m) (i j))))))

;; Replace kth column of a with r:

(defund replace-col (a k r)
  (transpose-mat (replace-row (transpose-mat a) k r)))

(defthm rmatp-replace-col
  (implies (and (rmatp a m n) (posp m) (posp n) (natp k) (< k n) (rlistnp r m))
           (rmatp (replace-col a k r) m n))
  :hints (("Goal" :in-theory (enable replace-col)
	          :use (rmatp-transpose
		        (:instance rmatp-replace-row (a (transpose-mat a)) (m n) (n m))
			(:instance rmatp-transpose (m n) (n m) (a (replace-row (transpose-mat a) k r)))))))

(defthm rmat-col-replace-col
  (implies (and (rmatp a m n) (posp m) (posp n)
		(natp k) (< k n) (natp j) (< j n)
		(rlistnp r m))
           (equal (col j (replace-col a k r))
	          (if (= j k)
		      r
		    (col j a))))
  :hints (("Goal" :in-theory (enable replace-col)
                  :use (rmatp-transpose
		        (:instance rmatp-replace-row (a (transpose-mat a)) (m n) (n m))
			(:instance rmatp-transpose (m n) (n m) (a (replace-row (transpose-mat a) k r)))
			(:instance col-transpose-rmat (a (replace-row (transpose-mat a) k r)) (m n) (n m))
			(:instance nth-replace-row (a (transpose-mat a)))))))

;; An important lemma in the proof of associativity of matrix multiplication:
;; If (rmatp a m n), then (rmat-sum (transpose-mat a)) = (rmat-sum a).
;; This holds trivially if either m = 0 or n = 0:

(local-defthm rmat-sum-0-1
  (implies (and (natp m) (rmatp a m 0))
           (equal (rmat-sum a) (r0)))
  :hints (("Goal" :in-theory (enable rlist-sum))))

(defthm rmat-sum-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (rmatp a m n))
           (equal (rmat-sum a) (r0)))
  :hints (("Goal" :in-theory (enable rlist-sum))))

(local-defthm rmat-sum-transpose-0-1
  (implies (and (natp n) (rmatp a 0 n))
           (equal (col j a) ())))

(local-defthm rmat-sum-transpose-0-2
  (implies (and (natp n) (rmatp a 0 n))
           (equal (rmat-sum (transpose-mat-aux a j n))
	          (r0)))
  :hints (("Goal" :in-theory (enable rlist-sum))))

(defthm rmat-sum-transpose-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (rmatp a m n))
           (equal (rmat-sum (transpose-mat a))
	          (r0)))
  :hints (("Goal" :in-theory (enable transpose-mat))))
		        
;; In the inductive step, we assume that the claim holds when a is replaced by
;; (strip-mat a), which is the result of deleting its first row and first column:

(defun cdrs (l)
  (if (consp l)
      (cons (cdr (car l))
	    (cdrs (cdr l)))
    ()))

(defun cars (l)
  (if (consp l)
      (cons (car (car l))
	    (cars (cdr l)))
    ()))

(defund strip-mat (a)
  (cdrs (cdr a)))

(local-defthmd rmatp-cdr
  (implies (and (posp m) (posp n) (rmatp a m n))
           (rmatp (cdr a) (1- m) n)))

(local-defthmd rmatp-cdrs
  (implies (and (natp m) (posp n) (rmatp a m n))
           (rmatp (cdrs a) m (1- n))))

(defthmd rmatp-strip-mat
  (implies (and (posp m) (posp n) (rmatp a m n))
           (rmatp (strip-mat a) (1- m) (1- n)))
  :hints (("Goal" :in-theory (enable strip-mat)
	   :use (rmatp-cdr (:instance rmatp-cdrs (m (1- m)))))))


(in-theory (enable rlist-sum))

(local-defthmd sum-rmat-strip-mat-1
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum a)
		  (r+ (r+ (entry 0 0 a) (rlist-sum (cdr (row 0 a))))
		      (rmat-sum (cdr a))))))

(local-defthmd sum-rmat-strip-mat-2
  (implies (and (natp m) (posp n) (rmatp a m n))
           (and (rlistnp (cars a) m)
	        (rmatp (cdrs a) m (1- n)))))

(local-defthmd sum-rmat-strip-mat-3
  (IMPLIES (AND (natp m) (posp n) (rmatp a m n))
           (EQUAL (R+ (R+ (CAR (CAR A))
                          (RLIST-SUM (CDR (CAR A))))
                      (R+ (RLIST-SUM (CARS (CDR A)))
                          (RMAT-SUM (CDRS (CDR A)))))
                  (R+ (R+ (CAR (CAR A))
                          (RLIST-SUM (CARS (CDR A))))
                      (R+ (RLIST-SUM (CDR (CAR A)))
                          (RMAT-SUM (CDRS (CDR A)))))))
  :hints (("Goal" :in-theory (enable r+assoc)
                  :use ((:instance sum-rmat-strip-mat-2 (a (cdr a)) (m (1- m)))
		        (:instance r+assoc (x (caar a)) (y (rlist-sum (cdar a))) (z (rlist-sum (cars (cdr a)))))
		        (:instance r+assoc (x (caar a)) (z (rlist-sum (cdar a))) (y (rlist-sum (cars (cdr a)))))
			(:instance r+comm (x (rlist-sum (cdar a))) (y (rlist-sum (cars (cdr a)))))))))

(local-defthmd sum-rmat-strip-mat-4
  (implies (and (natp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum a)
	          (r+ (rlist-sum (cars a))
		      (rmat-sum (cdrs a)))))
  :hints (("Subgoal *1/5" :use (sum-rmat-strip-mat-3))))

(local-defthmd rlist-sum-cars-cdr
  (equal (rlist-sum (cars (cdr a)))
         (rlist-sum (cdr (cars a)))))

(local-defthmd cars-col-0
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (cars a) (col 0 a))))

(local-defthmd sum-rmat-strip-mat-5
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum (cdr a))
	          (r+ (rlist-sum (cdr (col 0 a)))
		      (rmat-sum (strip-mat a)))))
  :hints (("Goal" :in-theory (enable strip-mat)
                  :use (rlist-sum-cars-cdr cars-col-0
		        (:instance sum-rmat-strip-mat-4 (m (1- m)) (a (cdr a)))))))

(local-defthmd sum-rmat-strip-mat-6
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum a)
		  (r+ (r+ (entry 0 0 a) (rlist-sum (cdr (row 0 a))))
		      (r+ (rlist-sum (cdr (col 0 a)))
		          (rmat-sum (strip-mat a))))))
  :hints (("Goal" :use (sum-rmat-strip-mat-1 sum-rmat-strip-mat-5))))

(defthmd sum-rmat-strip-mat
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum a)
		  (r+ (entry 0 0 a)
		      (r+ (r+ (rlist-sum (cdr (row 0 a)))
			      (rlist-sum (cdr (col 0 a))))
			  (rmat-sum (strip-mat a))))))			  
  :hints (("Goal" :in-theory (e/d (sum-rmat-strip-mat-6 r+assoc) (rlistnp-col))
                  :use (rmatp-strip-mat
		        (:instance rlistnp-row (i 0))
		        (:instance rlistnp-col (j 0))
		        (:instance rp-entry (i 0) (j 0))))))

;; Since (row 0 a) = (col 0 (transpose-mat a)) and (col 0 a) = (row 0 (transpose-mat a)), we have
;; the following:

(defthmd sum-rmat-strip-mat-equal
  (implies (and (posp m) (posp n) (rmatp a m n)
                (equal (rmat-sum (strip-mat a)) (rmat-sum (strip-mat (transpose-mat a)))))
	   (equal (rmat-sum (transpose-mat a))
		  (rmat-sum a)))
  :hints (("Goal" :in-theory (e/d (sum-rmat-strip-mat col-transpose-rmat) (rlistnp-col))
                  :use (rmatp-transpose
		        (:instance rlistnp-row (i 0))
		        (:instance rlistnp-col (j 0))
		        (:instance r+comm (x (rlist-sum (cdr (row 0 a)))) (y (rlist-sum (cdr (col 0 a)))))))))

;; If either m = 0 or n = 0, then the hypothesis of sum-rmat-strip-mat-equal holds trivially:

(defthm rmat-sum-strip-mat-0
  (implies (and (posp m) (posp n) (or (= m 1) (= n 1)) (rmatp a m n))
           (and (equal (rmat-sum (strip-mat a)) (r0))
	        (equal (rmat-sum (strip-mat (transpose-mat a))) (r0))))
  :hints (("Goal" :use (rmatp-strip-mat rmatp-transpose
                        (:instance rmatp-strip-mat (a (transpose-mat a)) (m n) (n m))
			(:instance rmat-sum-0 (a (strip-mat a)) (m (1- m)) (n (1- n)))
			(:instance rmat-sum-0 (a (strip-mat (transpose-mat a))) (m (1- n)) (n (1- m)))))))

(local-defthmd nth-cdr
  (implies (and (posp i) (consp l))
	   (equal (nth i l)
		  (nth (1- i) (cdr l)))))

(local-defthmd nth-cdrs
  (implies (and (natp i) (consp l))
	   (equal (nth i (cdrs l))
		  (cdr (nth i l)))))

(defthmd strip-rmat-entry
  (implies (and (posp m) (posp n) (rmatp a m n)
		(natp i) (natp j) (< i (1- m)) (< j (1- n)))
	   (equal (entry i j (strip-mat a))
		  (entry (1+ i) (1+ j) a)))
  :hints (("Goal" :in-theory (enable strip-mat)
	   :use ((:instance nth-cdr (i (1+ i)) (l a))
		 (:instance nth-cdr (i (1+ j)) (l (nth i (cdr a))))
		 (:instance nth-cdrs (l (cdr a)))))))

(local-defthmd rmatp-transpose-strip-rmat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (rmatp a m n))
           (and (rmatp (transpose-mat (strip-mat a)) (1- n) (1- m))
	        (rmatp (strip-mat (transpose-mat a)) (1- n) (1- m))))
  :hints (("Goal" :use (rmatp-transpose rmatp-strip-mat
                        (:instance rmatp-transpose (a (strip-mat a)) (m (1- m)) (n (1- n)))
			(:instance rmatp-strip-mat (a (transpose-mat a)) (m n) (n m))))))

(local-defthmd entry-transpose-strip-rmat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (rmatp a m n)
		(natp i) (natp j) (< i (1- n)) (< j (1- m)))
	   (equal (entry i j (transpose-mat (strip-mat a)))
		  (entry i j (strip-mat (transpose-mat a)))))
  :hints (("Goal" :use (rmatp-transpose rmatp-strip-mat
                        (:instance transpose-rmat-entry (a (strip-mat a)) (m (1- m)) (n (1- n)) (i j) (j i))
			(:instance strip-rmat-entry (i j) (j i))
			(:instance strip-rmat-entry (a (transpose-mat a)) (m n) (n m))
			(:instance transpose-rmat-entry (i (1+ j)) (j (1+ i)))))))

;; In the remaining case, we have the following:

(defthmd transpose-strip-rmat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (rmatp a m n))
	   (equal (transpose-mat (strip-mat a))
		  (strip-mat (transpose-mat a))))
  :hints (("Goal" :use (rmatp-transpose-strip-rmat
                        (:instance rmat-entry-diff-lemma (a (transpose-mat (strip-mat a))) (b (strip-mat (transpose-mat a))) (m (1- n)) (n (1- m)))
			(:instance entry-transpose-strip-rmat
			  (i (car (entry-diff (transpose-mat (strip-mat a)) (strip-mat (transpose-mat a)))))
			  (j (cdr (entry-diff (transpose-mat (strip-mat a)) (strip-mat (transpose-mat a))))))))))

(local-defun sum-rmat-transpose-induct (a m n)
  (if (and (posp m) (posp n))
      (list (sum-rmat-transpose-induct (strip-mat a) (1- m) (1- n)))
    (list a m n)))

;; The result follows by induction:

(defthmd sum-rmat-transpose
  (implies (and (natp m) (natp n) (rmatp a m n))
	   (equal (rmat-sum (transpose-mat a))
		  (rmat-sum a)))
  :hints (("Goal" :induct (sum-rmat-transpose-induct a m n))
          ("Subgoal *1/1" :use (rmatp-strip-mat sum-rmat-strip-mat-equal transpose-strip-rmat rmat-sum-strip-mat-0))))


;;----------------------------------------------------------------------------------------
;; Matrix Multiplication
;;----------------------------------------------------------------------------------------

;; Product of mxn matrix a and nxp matrix b:

(defund rmat* (a b)
  (if (consp a)
      (cons (rdot-list (car a) (transpose-mat b))
            (rmat* (cdr a) b))
    ()))

(defthm rlistnp-rdot-list
  (implies (and (rmatp l m n) (rlistnp x n))
           (rlistnp (rdot-list x l) m)))

(defthm rmatp-rmat*
  (implies (and (rmatp a m n) (rmatp b n p) (posp m) (posp n) (posp p) )
           (rmatp (rmat* a b) m p))
  :hints (("Subgoal *1/7" :expand ((rmat* a b)))
          ("Subgoal *1/6" :expand ((rmat* a b))
	                  :use ((:instance rmatp-transpose (a b) (m n) (n p))))
          ("Subgoal *1/5" :expand ((rmat* a b)))
          ("Subgoal *1/4" :expand ((rmat* a b) (rmat* () b)))))

(defthmd nth-rmat*
  (implies (and (natp m) (rmatp a m n) (natp i) (< i m))
           (equal (nth i (rmat* a b))
	          (rdot-list (nth i a) (transpose-mat b))))
  :hints (("Goal" :in-theory (enable rmat*))))

(defthmd rmat*-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* a b))
	          (rdot (row i a) (col j b))))
  :hints (("Goal" :in-theory (enable nth-rmat*)
	   :use ((:instance rmatp-transpose (a b) (m n) (n p))))))

(local-defthmd rmat*-dist-1-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a1 m n) (rmatp a2 m n) (rmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* (rmat-add a1 a2) b))
		  (entry i j (rmat-add (rmat* a1 b) (rmat* a2 b)))))
  :hints (("Goal" :in-theory (e/d (rmat*-entry rmat-add-entry) (rdot-rlist-add rmatp-rmat* entry))
                  :use ((:instance rmatp-rmat* (a a1))
		        (:instance rmatp-rmat* (a a2))
			(:instance row-rmat-add (a a1) (b a2))
			(:instance rdot-rlist-add (x (nth i a1)) (y (nth i a2)) (z (col j b)))
			(:instance rlistnp-row (a a1))
			(:instance rlistnp-row (a a2))))))

(defthmd rmat*-dist-1
  (implies (and (posp m) (posp n) (posp p) (rmatp a1 m n) (rmatp a2 m n) (rmatp b n p))
	   (equal (rmat* (rmat-add a1 a2) b)
		  (rmat-add (rmat* a1 b) (rmat* a2 b))))
  :hints (("Goal" :in-theory (disable rmatp-rmat-add)
                  :use ((:instance rmat-entry-diff-lemma (a (rmat* (rmat-add a1 a2) b)) (b (rmat-add (rmat* a1 b) (rmat* a2 b))) (n p))
                        (:instance rmat*-dist-1-entry
			  (i (car (entry-diff (rmat* (rmat-add a1 a2) b) (rmat-add (rmat* a1 b) (rmat* a2 b)))))
			  (j (cdr (entry-diff (rmat* (rmat-add a1 a2) b) (rmat-add (rmat* a1 b) (rmat* a2 b))))))
			(:instance rmatp-rmat* (a (rmat-add a1 a2)))
			(:instance rmatp-rmat-add (a (rmat* a1 b)) (b (rmat* a2 b)) (n p))
			(:instance rmatp-rmat-add (a a1) (b a2))))))

(local-defthmd rmat*-dist-2-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b1 n p) (rmatp b2 n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* a (rmat-add b1 b2)))
		  (entry i j (rmat-add (rmat* a b1) (rmat* a b2)))))
  :hints (("Goal" :in-theory (e/d (col-rmat-add rmat*-entry rmat-add-entry) (rdot-rlist-add rmatp-rmat* entry))
                  :use (rlistnp-row
		        (:instance rmatp-rmat* (b b1))
		        (:instance rmatp-rmat* (b b2))
			(:instance col-rmat-add (a b1) (b b2) (m n) (n p))			
			(:instance rdot-rlist-add (z (nth i a)) (x (col j b1)) (y (col j b2)))
			(:instance rdot-comm (x (nth i a)) (y (rlist-add (col j b1) (col j b2))))
			(:instance rdot-comm (x (NTH I A)) (y (col j b1)))
			(:instance rdot-comm (x (nth i a)) (y (col j b2)))
			(:instance rlistnp-col (a b1) (m n) (n p))
			(:instance rlistnp-col (a b2) (m n) (n p))))))
			
(defthmd rmat*-dist-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b1 n p) (rmatp b2 n p))
	   (equal (rmat* a (rmat-add b1 b2))
		  (rmat-add (rmat* a b1) (rmat* a b2))))
  :hints (("Goal" :in-theory (disable rmatp-rmat-add)
                  :use ((:instance rmat-entry-diff-lemma (a (rmat* a (rmat-add b1 b2))) (b (rmat-add (rmat* a b1) (rmat* a b2))) (n p))
                        (:instance rmat*-dist-2-entry
			  (i (car (entry-diff (rmat* a(rmat-add b1 b2)) (rmat-add (rmat* a b1) (rmat* a b2)))))
			  (j (cdr (entry-diff (rmat* a(rmat-add b1 b2)) (rmat-add (rmat* a b1) (rmat* a b2))))))
			(:instance rmatp-rmat* (b (rmat-add b1 b2)))
			(:instance rmatp-rmat-add (a (rmat* a b1)) (b (rmat* a b2)) (n p))
			(:instance rmatp-rmat-add (a b1) (b b2) (m n) (n p))))))

(local-defthmd rmat*-rmat-scalar-mul-1-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* (rmat-scalar-mul c a) b))
		  (entry i j (rmat-scalar-mul c (rmat* a b)))))
  :hints (("Goal" :in-theory (e/d (rmat-scalar-mul-entry rmat*-entry) (rdot-rlist-add rmatp-rmat* entry))  
                  :use (row-rmat-scalar-mul rmatp-rmat*	rmatp-rmat-scalar-mul rlistnp-row
		        (:instance rdot-rlist-scalar-mul (x (nth i a)) (y (col j b)))
			(:instance rlistnp-col (a b) (m n) (n p))
		        (:instance rmatp-rmat-scalar-mul (a (rmat* a b)) (n p))))))

(defthmd rmat*-rmat-scalar-mul-1
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c))
	   (equal (rmat* (rmat-scalar-mul c a) b)
		  (rmat-scalar-mul c (rmat* a b))))
  :hints (("Goal" :use (rmatp-rmat-scalar-mul
                        (:instance rmatp-rmat-scalar-mul (a (rmat* a b)) (n p))
                        (:instance rmatp-rmat* (a (rmat-scalar-mul c a)))
                        (:instance rmat-entry-diff-lemma (a (rmat* (rmat-scalar-mul c a) b)) (b (rmat-scalar-mul c (rmat* a b))) (n p))
                        (:instance rmat*-rmat-scalar-mul-1-entry
			            (i (car (entry-diff (rmat* (rmat-scalar-mul c a) b) (rmat-scalar-mul c (rmat* a b)))))
			            (j (cdr (entry-diff (rmat* (rmat-scalar-mul c a) b) (rmat-scalar-mul c (rmat* a b))))))))))

(local-defthmd rmat*-rmat-scalar-mul-2-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* a (rmat-scalar-mul c b)))
		  (entry i j (rmat-scalar-mul c (rmat* a b)))))
  :hints (("Goal" :in-theory (e/d (rmat-scalar-mul-entry rmat*-entry) (rdot-rlist-add rmatp-rmat* entry))  
                  :use (rmatp-rmat* rlistnp-row
		        (:instance rmatp-rmat-scalar-mul  (a b) (m n) (n p))
		        (:instance col-rmat-scalar-mul (a b) (m n) (n p))
			(:instance rdot-comm (x (nth i a)) (y (COL J (RMAT-SCALAR-MUL C B))))
			(:instance rdot-rlist-scalar-mul (x (col j b)) (y (nth i a)))
			(:instance rlistnp-col (a b) (m n) (n p))
			(:instance rdot-comm (x (nth i a)) (y (col j b)))))))

(defthmd rmat*-rmat-scalar-mul-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c))
	   (equal (rmat* a (rmat-scalar-mul c b))
		  (rmat-scalar-mul c (rmat* a b))))
  :hints (("Goal" :use ((:instance rmatp-rmat-scalar-mul (a b) (m n) (n p))
                        (:instance rmatp-rmat-scalar-mul (a (rmat* a b)) (n p))
                        (:instance rmatp-rmat* (b (rmat-scalar-mul c b)))
                        (:instance rmat-entry-diff-lemma (a (rmat* a (rmat-scalar-mul c b))) (b (rmat-scalar-mul c (rmat* a b))) (n p))
                        (:instance rmat*-rmat-scalar-mul-2-entry
			            (i (car (entry-diff (rmat* a (rmat-scalar-mul c b)) (rmat-scalar-mul c (rmat* a b)))))
			            (j (cdr (entry-diff (rmat* a (rmat-scalar-mul c b)) (rmat-scalar-mul c (rmat* a b))))))))))

(local-defthmd transpose-rmat*-entry-1
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (transpose-mat (rmat* a b)))
	          (rdot (row j a) (col i b))))
  :hints (("Goal" :use (rmatp-rmat*
                        (:instance transpose-rmat-entry (i j) (j i) (a (rmat* a b)) (n p))
                        (:instance rmat*-entry (i j) (j i))))))

(local-defthmd transpose-rmat*-entry-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (rmat* (transpose-mat b) (transpose-mat a)))
	          (rdot (col i b) (row j a))))
  :hints (("Goal" :use (rmatp-rmat* col-transpose-rmat rmatp-transpose
                        (:instance rmatp-transpose (a b) (m n) (n p))
                        (:instance rmat*-entry (a (transpose-mat b)) (b (transpose-mat a)) (m p) (p m))))))

(local-defthmd transpose-rmat*-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (transpose-mat (rmat* a b)))
	          (entry i j (rmat* (transpose-mat b) (transpose-mat a)))))
  :hints (("Goal" :use (transpose-rmat*-entry-1 transpose-rmat*-entry-2
                        (:instance rlistnp-row (i j))
                        (:instance rdot-comm (x (row j a)) (y (col i b)))))))

;; Transpose of a product:

(defthmd transpose-rmat*
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p))
	   (equal (transpose-mat (rmat* a b))
	          (rmat* (transpose-mat b) (transpose-mat a))))
  :hints (("Goal" :use (rmatp-rmat* rmatp-transpose
                        (:instance rmatp-transpose (a b) (m n) (n p))
                        (:instance rmatp-transpose (a (rmat* a b)) (n p))
			(:instance rmatp-rmat* (a (transpose-mat b)) (b (transpose-mat a)) (m p) (p m))
			(:instance rmat-entry-diff-lemma (m p) (n m)
			                            (a (transpose-mat (rmat* a b)))
			                            (b (rmat* (transpose-mat b) (transpose-mat a))))
                        (:instance transpose-rmat*-entry
			            (i (car (entry-diff (transpose-mat (rmat* a b)) (rmat* (transpose-mat b) (transpose-mat a)))))
                                    (j (cdr (entry-diff (transpose-mat (rmat* a b)) (rmat* (transpose-mat b) (transpose-mat a))))))))))

;; The definition of the nxn identity matrix is based on that of an rlist of length n
;; with (r1) at index j and (r0) elsewhere:

(defun runit (i n)
  (if (zp n)
      ()
    (if (zp i)
        (cons (r1) (rlistn0 (1- n)))
      (cons (r0) (runit (1- i) (1- n))))))

(defthm rlistnp-runit
  (rlistnp (runit i n) n))

(defun rdelta (i j)
  (if (= i j) (r1) (r0)))

(local-defun nth-runit-induct (i j n)
  (if (or (zp i) (zp j) (zp n))
      t
    (list (nth-runit-induct (1- i) (1- j) (1- n)))))

(defthm nth-runit
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i n))
           (equal (nth i (runit j n))
	          (rdelta i j)))
  :hints (("Goal" :induct (nth-runit-induct i j n))  
          ("Subgoal *1/1" :expand ((runit j n)))))

;; Dot product of (runit j n) with an rlist of length n:

(defthm rdot-runit
  (implies (and (posp n) (rlistnp x n) (natp j) (< j n))
           (equal (rdot (runit j n) x)
	          (nth j x))))

(defthm rdot-runit-comm
  (implies (and (posp n) (rlistnp x n) (natp j) (< j n))
           (equal (rdot x (runit j n))
	          (nth j x)))
  :hints (("Goal" :use ((:instance rdot-comm (y (runit j n)))))))

;; nxn identity matrix:

(defun id-rmat-aux (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (runit i n) (id-rmat-aux (1+ i) n))
    ()))

(defund id-rmat (n)
  (id-rmat-aux 0 n))

(local-defthmd rmatp-id-rmat-aux
  (implies (and (posp n) (natp j) (<= j n))
           (rmatp (id-rmat-aux j n) (- n j) n)))

(defthm rmatp-id-rmat
  (implies (posp n)
           (rmatp (id-rmat n) n n))
  :hints (("Goal" :in-theory (enable id-rmat)
                  :use ((:instance rmatp-id-rmat-aux (j 0))))))

(local-defthmd nth-id-rmat-aux
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i (- n j)))
	   (equal (nth i (id-rmat-aux j n))
		  (runit (+ j i) n)))
  :hints (("Goal" :induct (transpose-mat-aux-induct i j))
	  ("Subgoal *1/1" :expand ((id-rmat-aux j n)))))

(defthm nth-id-rmat
  (implies (and (posp n) (natp i) (< i n))
	   (equal (nth i (id-rmat n))
		  (runit i n)))
  :hints (("Goal" :in-theory (enable id-rmat)
                  :use ((:instance nth-id-rmat-aux (j 0))))))

(defthmd entry-id-rmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (id-rmat n))
	          (rdelta i j))))

(local-defthmd entry-transpose-id-rmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (transpose-mat (id-rmat n)))
	          (entry i j (id-rmat n))))
  :hints  (("Goal" :use (entry-id-rmat
                         (:instance entry-id-rmat (i j) (j i))
			 (:instance transpose-rmat-entry (a (id-rmat n)) (m n) (i j) (j i))))))

(defthmd transpose-id-rmat
  (implies (natp n)
           (equal (transpose-mat (id-rmat n))
	          (id-rmat n)))
  :hints  (("Goal" :use (rmatp-id-rmat
                         (:instance rmatp-transpose (a (id-rmat n)) (m n))
                         (:instance rmat-entry-diff-lemma (m n) (a (id-rmat n)) (b (transpose-mat (id-rmat n))))
			 (:instance entry-transpose-id-rmat (i (car (entry-diff (id-rmat n) (transpose-mat (id-rmat n)))))
			                                   (j (cdr (entry-diff (id-rmat n) (transpose-mat (id-rmat n))))))))))

(defthm col-id-rmat
  (implies (and (natp n) (natp j) (< j n))
           (equal (col j (id-rmat n))
	          (runit j n)))
  :hints (("Goal" :use (transpose-id-rmat
                        (:instance nth-transpose-rmat (m n) (a (id-rmat n)) (i j))))))

;; (id-rmat n) is a right identity:

(local-defthmd entry-rmat*-id-rmat-right
  (implies (and (posp m) (posp n) (rmatp a m n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (rmat* a (id-rmat n)))
	          (entry i j a)))
  :hints (("Goal" :use (rlistnp-row
                        (:instance rmat*-entry (p n) (b (id-rmat n)))
                        (:instance rdot-comm (x (runit j n)) (y (nth i a)))))))

(defthmd id-rmat-right
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (rmat* a (id-rmat n))
	          a))
  :hints (("Goal" :use ((:instance rmatp-rmat* (b (id-rmat n)) (p n))
			(:instance entry-rmat*-id-rmat-right (i (car (entry-diff a (rmat* a (id-rmat n)))))
			                                    (j (cdr (entry-diff a (rmat* a (id-rmat n))))))
                        (:instance rmat-entry-diff-lemma (b (rmat* a (id-rmat n))))))))

;; (id-rmat n) is a left identity:

(local-defthmd entry-rmat*-id-rmat-left
  (implies (and (posp m) (posp n) (rmatp a m n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (rmat* (id-rmat m) a))
	          (entry i j a)))
  :hints (("Goal" :use (rlistnp-row nth-col
                        (:instance rmat*-entry (n m) (p n) (a (id-rmat m)) (b a))))))

(defthmd id-rmat-left
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (rmat* (id-rmat m) a)
	          a))
  :hints (("Goal" :use ((:instance rmatp-rmat* (a (id-rmat m)) (b a) (n m) (p n))
			(:instance entry-rmat*-id-rmat-left (i (car (entry-diff a (rmat* (id-rmat m) a))))
			                                   (j (cdr (entry-diff a (rmat* (id-rmat m) a)))))
                        (:instance rmat-entry-diff-lemma (b (rmat* (id-rmat m) a)))))))
							   
;; Associativity:

;; Let a, b, and c be matrices of dimensions mxn, nxp, and pxq, respectively.  Then
;; (rmat* a (rmat* b c)) and (rmat* (rmat* a b) c)) are both mxp matrices.  Our
;; objective is to prove that they are equal.  Let 0 <= i < m and 0 <= j < q.  It will
;; surrice to show that

;;    (entry i j (rmat* a (rmat* b c))) = (entry i j (rmat* (rmat* a b) c)).

;; Applying rmat*-entry and expanding rdot, we rind that both sides of this equation
;; are sums of n*p 3-way products.

;; We shall construct an nxp matrix of 3-way products, (rmat12 a b c i j), such that

;;    (entry i j (rmat* a (rmat* b c))) = (rmat-sum (rmat12 a b c i j))

;; and a pxn matrix of 3-way products, (rmat21 a b c), such that

;;    (entry i j (rmat* (rmat* a b) c)) = (rmat-sum (rmat21 a b c i j)).

;; We shall show that (rmat21 a b c i j) = (transpose-mat (rmat12 a b c i j)) and apply
;; rmat-sum-transpose to conclude that

;;    (entry i j (rmat* a (rmat* b c))) = (entry i j (rmat* (rmat* a b) c)).

;; The entry on the left is the dot product of a row of a and a column of (rmat* b c),
;; and each entry of this column is a dot product of a row of b and a column of c.
;; This leads to the definition of the nxp matrix of 3-way products, (rmat12 a b c i j):

(defun rlist-mul-list (x l)
  (if (consp l)
      (cons (rlist-mul x (car l))
	    (rlist-mul-list x (cdr l)))
    ()))

(defun rlist-scalar-mul-list (x l)
  (if (consp l)
      (cons (rlist-scalar-mul (car x) (car l))
            (rlist-scalar-mul-list (cdr x) (cdr l)))
    ()))

(defund rmat12 (a b c i j)
  (rlist-scalar-mul-list (row i a)
	   	         (rlist-mul-list (col j c) b)))

(local-defun rlist-sum-list (l)
  (if (consp l)
      (cons (rlist-sum (car l))
            (rlist-sum-list (cdr l)))
    ()))

(local-defthm rlist-sum-rlist-scalar-mul
  (implies (and (rp x) (rlistnp l n))
           (equal (rlist-sum (rlist-scalar-mul x l))
	          (r* x (rlist-sum l)))))

(local-defthmd rmat-sum-rlist-scalar-mul-list
  (implies (and (rlistnp x n) (rmatp l n p))
           (equal (rmat-sum (rlist-scalar-mul-list x l))
                  (rdot x (rlist-sum-list l)))))

(local-defthm rmatp-rlist-mul-list
  (implies (and (rmatp a m n) (rlistnp x n))
           (rmatp (rlist-mul-list x a) m n)))

(local-defthm rmatp-rlist-scalar-mul-list
  (implies (and (rmatp a m n) (rlistnp x m))
           (rmatp (rlist-scalar-mul-list x a) m n)))

(defthmd rmatp-rmat12
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (rmatp (rmat12 a b c i j) n p))
  :hints (("Goal" :in-theory (e/d (rmat12) (rlistnp-col))
                  :use (rlistnp-row
		        (:instance rlistnp-col (a c) (m p) (n q))))))

;; We derive the following expression for each entry of this matrix:

(local-defthmd nth-rlist-scalar-mul-list
  (equal (nth r (rlist-scalar-mul-list x l))
         (rlist-scalar-mul (nth r x) (nth r l))))

(local-defthmd nth-rlist-mul-list
  (implies (and (natp r) (< r (len l)))
           (equal (nth r (rlist-mul-list x l))
	          (rlist-mul x (nth r l)))))

(local-defthmd nth-rlist-scalar-mul-2
  (implies (and (natp s) (< s (len x)))
	   (equal (nth s (rlist-scalar-mul c x))
		  (r* c (nth s x)))))

(local-defthmd nth-rlist-mul
  (implies (and (natp s) (< s (len x)) (< s (len y)))
           (equal (nth s (rlist-mul x y))
	          (r* (nth s x) (nth s y)))))

(local-defthmd rmat12-entry-1
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (rmat12 a b c i j)))
	          (nth s (rlist-scalar-mul (entry i r a) (nth r (rlist-mul-list (col j c) b))))))
  :hints (("Goal" :in-theory (enable rmat12 nth-rlist-scalar-mul-list))))

(local-defthmd rmat12-entry-2
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (rmat12 a b c i j)))
	          (nth s (rlist-scalar-mul (entry i r a) (rlist-mul (col j c) (nth r b))))))
  :hints (("Goal" :in-theory (enable rmat12-entry-1 nth-rlist-mul-list))))

(local-defthmd rmat12-entry-3
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (rmat12 a b c i j)))
	          (r* (entry i r a) (nth s (rlist-mul (col j c) (nth r b))))))
  :hints (("Goal" :in-theory (e/d (rmat12-entry-2) (rlistnp-col rlistnp-rlist-mul))
                  :use ((:instance nth-rlist-scalar-mul-2 (c (entry i r a)) (x (rlist-mul (col j c) (nth r b))))
		        (:instance rlistnp-rlist-mul (n p) (x (col j c)) (y (nth r b)))
			(:instance rlistnp-row (a b) (i r) (m n) (n p))
			(:instance rlistnp-col (a c) (m p) (n q))))))

(local-defthmd rmat12-entry-4
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (rmat12 a b c i j)))
	          (r* (entry i r a) (r* (entry s j c) (entry r s b)))))
  :hints (("Goal" :in-theory (e/d (rmat12-entry-3 nth-col) (rlistnp-col))
                  :use ((:instance nth-rlist-mul (x (col j c)) (y (nth r b)))
			(:instance rlistnp-row (a b) (i r) (m n) (n p))
			(:instance rlistnp-col (a c) (m p) (n q))))))

(local-defthmd rmat12-entry-5
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (rmat12 a b c i j)))
	          (r* (entry i r a) (r* (entry r s b) (entry s j c)))))
  :hints (("Goal" :in-theory (enable rmat12-entry-4)
                  :use ((:instance rp-entry (a b) (m n) (n p) (i r) (j s))
			(:instance rp-entry (a c) (m p) (n q) (i s))
			(:instance r*comm (x (entry r s b)) (y (entry s j c)))))))

(defthmd rmat12-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (entry r s (rmat12 a b c i j))
	          (r* (r* (entry i r a) (entry r s b)) (entry s j c))))
  :hints (("Goal" :in-theory (enable rmat12-entry-5 r*assoc)
                  :use ((:instance rp-entry (j r))
			(:instance rp-entry (a b) (m n) (n p) (i r) (j s))
			(:instance rp-entry (a c) (m p) (n q) (i s))))))

;; The sum of these entries:

(local-defthm rmat-sum-rmat12-rdot
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat12 a b c i j))
	          (rdot (row i a)
		        (rlist-sum-list (rlist-mul-list (col j c) b)))))
  :hints (("Goal" :in-theory (enable rmat12)
                  :use (rlistnp-row
		        (:instance rmat-sum-rlist-scalar-mul-list (x (row i a)) (l (rlist-mul-list (col j c) b)))))))	          

(local-defthm rlist-sum-rlist-mul
  (implies (and (rlistnp x n) (rlistnp y n))
           (equal (rlist-sum (rlist-mul x y))
	          (rdot x y))))

(local-defthm rlist-sum-list-rlist-mul-list-col
  (implies (and (posp p) (posp q) (rmatp b n p) (rmatp c p q) (natp j) (< j q))
           (equal (rlist-sum-list (rlist-mul-list (col j c) b))
	          (col j (rmat* b c))))
  :hints (("Subgoal *1/3" :in-theory (disable rlistnp-col)
                          :expand ((rmat* b c))
                          :use ((:instance rmatp-transpose (a c) (m p) (n q))
			        (:instance rlistnp-row (a b) (m n) (n p) (i 0))
			        (:instance rlistnp-col (a c) (m p) (n q))
				(:instance rdot-comm (n p) (x (col j c)) (y (car b)))))
          ("Subgoal *1/1" :expand ((rmat* () c)))))

(local-defthm rmat-sum-rmat12-rdot-row-col
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat12 a b c i j))
	          (rdot (row i a) (col j (rmat* b c))))))

(defthm rmat-sum-rmat12
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat12 a b c i j))
	          (entry i j (rmat* a (rmat* b c)))))
  :hints (("Goal" :use ((:instance rmat*-entry (b (rmat* b c)) (p q))))))

;; The matrix (rmat21 a b c i j) similarly relates to (entry i j (rmat* (rmat* a b) c):

(defund rmat21 (a b c i j)
  (rlist-scalar-mul-list (col j c)
		         (rlist-mul-list (row i a) (transpose-mat b))))

(defthmd rmatp-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (rmatp (rmat21 a b c i j) p n))
  :hints (("Goal" :in-theory (e/d (rmat21) (rlistnp-col))
                  :use (rlistnp-row
		        (:instance rmatp-transpose (a b) (m n) (n p))
		        (:instance rlistnp-col (a c) (m p) (n q))))))

(local-defthmd rmat21-entry-1
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (nth s (rlist-scalar-mul (entry r j c) (nth r (rlist-mul-list (row i a) (transpose-mat b)))))))
  :hints (("Goal" :in-theory (enable rmat21 nth-col nth-rlist-scalar-mul-list))))

(local-defthmd rmat21-entry-2
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (nth s (rlist-scalar-mul (entry r j c) (rlist-mul (row i a) (col r b))))))
  :hints (("Goal" :in-theory (enable rmat21-entry-1 nth-rlist-mul-list)
                  :use ((:instance rmatp-transpose (a b) (m n) (n p))))))

(local-defthmd rmat21-entry-3
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (r* (entry r j c) (nth s (rlist-mul (row i a) (col r b))))))
  :hints (("Goal" :in-theory (e/d (rmat21-entry-2) (rlistnp-col rlistnp-rlist-mul))
                  :use (rlistnp-row
		        (:instance nth-rlist-scalar-mul-2 (c (entry r j c)) (x (rlist-mul (row i a) (col r b))))
		        (:instance rlistnp-rlist-mul (x (row i a)) (y (col r b)))
			(:instance rlistnp-col (a b) (j r) (m n) (n p))))))

(local-defthmd rmat21-entry-4
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (r* (entry r j c) (r* (entry i s a) (entry s r b)))))
  :hints (("Goal" :in-theory (e/d (rmat21-entry-3 nth-col) (rlistnp-col))
                  :use (rlistnp-row
		        (:instance nth-rlist-mul (x (row i a)) (y (col r b)))
			(:instance rlistnp-col (a b) (j r) (m n) (n p))))))

(local-defthmd rmat21-entry-5
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (r* (r* (entry i s a) (entry s r b)) (entry r j c))))
  :hints (("Goal" :in-theory (e/d (rmat21-entry-4 rp-entry) (entry))
                  :use ((:instance r*comm (x (r* (entry i s a) (entry s r b))) (y (entry r j c)))))))

(local-defthmd rmat21-entry-6
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (rmat21 a b c i j)))
	          (r* (entry i s a) (r* (entry s r b) (entry r j c)))))
  :hints (("Goal" :in-theory (e/d (rmat21-entry-5 rp-entry) (entry))
                  :use ((:instance r*assoc (x (entry i s a)) (y (entry s r b)) (z (entry r j c)))))))

(defthmd rmat21-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (rmat21 a b c i j))
	          (r* (entry i s a) (r* (entry s r b) (entry r j c)))))
  :hints (("Goal" :in-theory (enable rmat21-entry-6))))


(local-defthm rmat-sum-rmat21-1
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat21 a b c i j))
	          (rdot (col j c)
		        (rlist-sum-list (rlist-mul-list (row i a) (transpose-mat b))))))
  :hints (("Goal" :in-theory (e/d (rmat21) (rlistnp-col))
                  :use (rlistnp-row
		        (:instance rlistnp-col (a c) (m p) (n q))
		        (:instance rmatp-transpose (a b) (m n) (n p))
		        (:instance rmat-sum-rlist-scalar-mul-list (n p) (p n) (x (col j c)) (l (rlist-mul-list (row i a) (transpose-mat b))))))))

(local (include-book "std/lists/nthcdr" :dir :system))

(local-defthmd null-nthcdr-len
  (implies (true-listp l)
           (null (nthcdr (len l) l))))

(local-defthmd null-nthcdr-nth-rmat*
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (natp i) (< i m))
           (null (nthcdr p (nth i (rmat* a b)))))
  :hints (("Goal" :use (rmatp-rmat*
                        (:instance rlistnp-row (a (rmat* a b)) (n p))
			(:instance null-nthcdr-len (l (nth i (rmat* a b))))))))

(local-defthmd nthcdr-cons
  (implies (and (natp j) (< j (len l)))
           (equal (nthcdr j l)
	          (cons (nth j l) (nthcdr (1+ j) l)))))

(local-defthmd nthcdr-cons-rdot
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (natp i) (< i m) (natp j) (< j p))
           (equal (cons (rdot (nth i a) (col j b))
                        (cdr (nthcdr j (nth i (rmat* a b)))))
                  (nthcdr j (nth i (rmat* a b)))))
  :hints (("Goal" :use (rmatp-rmat* rmat*-entry
                        (:instance rlistnp-row (a (rmat* a b)) (n p))
			(:instance nthcdr-cons (l (nth i (rmat* a b))))))))

(local-defthm rmat-sum-rmat21-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (natp i) (< i m) (natp j) (<= j p))
           (equal (rlist-sum-list (rlist-mul-list (row i a) (transpose-mat-aux b j p)))
	          (nthcdr j (row i (rmat* a b)))))
  :hints (("Goal" :induct (transpose-mat-aux b j p))
          ("Subgoal *1/2" :use (null-nthcdr-nth-rmat*))
          ("Subgoal *1/1" :in-theory (disable rlistnp-col)
	                  :use (rlistnp-row nthcdr-cons-rdot
			        (:instance rlistnp-col (a b) (m n) (n p))))))

(local-defthm rmat-sum-rmat21-3
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (natp i) (< i m))
           (equal (rlist-sum-list (rlist-mul-list (row i a) (transpose-mat b)))
	          (row i (rmat* a b))))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance rmat-sum-rmat21-2 (j 0))
		        (:instance rlistnp-row (a b) (m n) (n p) (i 0))))))
			        
(local-defthm rmat-sum-rmat21-4
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat21 a b c i j))
	          (rdot (col j c) (row i (rmat* a b)))))
  :hints (("Goal" :use (rmat-sum-rmat21-1 rmat-sum-rmat21-3))))

(defthm rmat-sum-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat21 a b c i j))
	          (entry i j (rmat* (rmat* a b) c))))
  :hints (("Goal" :in-theory (disable rlistnp-col)
                  :use (rmatp-rmat*
                        (:instance rmat*-entry (a (rmat* a b)) (b c) (n p) (p q))
                        (:instance rdot-comm (n p) (x (row i (rmat* a b))) (y (col j c)))
			(:instance rlistnp-row (a (rmat* a b)) (n p))
			(:instance rlistnp-col (a c) (m p) (n q))))))

;; Combine rmat21-entry and rmat12-entry:

(defthmd rmat12-rmat21-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (rmat21 a b c i j))
	          (entry s r (rmat12 a b c i j))))
  :hints (("Goal" :in-theory (e/d (r*assoc rp-entry rmat21-entry rmat12-entry) (entry)))))

;; Apply transpose-rmat-entry:

(local-defthmd rmat12-transpose-rmat21-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (rmat21 a b c i j))
	          (entry r s (transpose-mat (rmat12 a b c i j)))))
  :hints (("Goal" :in-theory (e/d (rmat12-rmat21-entry) (entry))
                  :use (rmatp-rmat12))))

(defthmd rmat12-transpose-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (transpose-mat (rmat12 a b c i j))
	          (rmat21 a b c i j)))	          
  :hints (("Goal" :use (rmatp-rmat12 rmatp-rmat21
                        (:instance rmat-entry-diff-lemma (a (rmat21 a b c i j)) (b (transpose-mat (rmat12 a b c i j))) (m p))
                        (:instance rmatp-transpose (a (rmat12 a b c i j)) (m n) (n p))
			(:instance rmat12-transpose-rmat21-entry
			            (r (car (entry-diff (rmat21 a b c i j) (transpose-mat (rmat12 a b c i j)))))
				    (s (cdr (entry-diff (rmat21 a b c i j) (transpose-mat (rmat12 a b c i j))))))))))

;; By sum-rmat-transpose, (entry i j (rmat* a (rmat* b c))) = (entry i j (rmat* (rmat* a b) c)),
;; and the result follows:

(local-defthmd rmat-sum-rmat12-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat12 a b c i j))
	          (rmat-sum (rmat21 a b c i j))))          
  :hints (("Goal" :use (rmat12-transpose-rmat21 rmatp-rmat12
                        (:instance sum-rmat-transpose (a (rmat12 a b c i j)) (m n) (n p))))))

(local-defthmd rmat*-assoc-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (entry i j (rmat* a (rmat* b c)))
	          (entry i j (rmat* (rmat* a b) c))))
  :hints (("Goal" :use (rmat12-transpose-rmat21 rmatp-rmat12
                        (:instance sum-rmat-transpose (a (rmat12 a b c i j)) (m n) (n p))))))

(defthmd rmat*-assoc
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q))
           (equal (rmat* a (rmat* b c))
	          (rmat* (rmat* a b) c)))
  :hints (("Goal" :use (rmatp-rmat*
                        (:instance rmatp-rmat* (a b) (b c) (m n) (n p) (p q))
                        (:instance rmatp-rmat* (b (rmat* b c)) (p q))
                        (:instance rmatp-rmat* (a (rmat* a b)) (b c) (n p) (p q))
			(:instance rmat-entry-diff-lemma (a (rmat* a (rmat* b c))) (b (rmat* (rmat* a b) c)) (n q))
			(:instance rmat*-assoc-entry (i (car (entry-diff (rmat* a (rmat* b c)) (rmat* (rmat* a b) c))))
			                             (j (cdr (entry-diff (rmat* a (rmat* b c)) (rmat* (rmat* a b) c)))))))))
