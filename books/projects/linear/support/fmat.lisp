(in-package "DM")

(include-book "field")

;;----------------------------------------------------------------------------------------
;; Matrices of Field Elements
;;----------------------------------------------------------------------------------------

;; mxn matrix:

(defun fmatp (a m n)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (null a)
    (and (consp a)
	 (flistnp (car a) n)
	 (fmatp (cdr a) (1- m) n))))

(defthm len-fmatp
  (implies (and (natp m) (fmatp a m n))
	   (equal (len a) m)))

(defthm true-listp-fmatp
  (implies (fmatp a m n)
	   (true-listp a)))

;; ith row of a:

(defun row (i a)
  (nth i a))

(defthm flistnp-row
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m))
           (flistnp (row i a) n)))

(defthm len-fmat-row
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m))
	   (equal (len (nth i a))
		  n)))

;; jth column or a:

(defun col (j a)
  (if (consp a)
      (cons (nth j (car a))
            (col j (cdr a)))
    ()))

(defthm flistnp-col
  (implies (and (natp m) (natp n) (fmatp a m n)
		(natp j) (< j n))
	   (flistnp (col j a) m)))

(defthm len-col
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (equal (len (col j a))
		  m)))

;; The entry of a matrix in row i and column j:

(defun entry (i j mat)
  (nth j (nth i mat)))

(defthmd fp-entry
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m) (natp j) (< j n))
           (fp (entry i j a))))

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

(defthm fmatp-replace-row
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) (flistnp r n))
           (fmatp (replace-row a k r) m n)))

(defthm len-replace-row
  (implies (and (natp k) (< k (len a)))
           (equal (len (replace-row a k r))
                  (len a))))

(defthmd replace-fmat-row-self
  (implies (and (fmatp a m n) (posp m) (posp n)
                (natp i) (< i m))
	   (equal (replace-row a i (row i a))
	          a)))

(defthmd replace-2-fmat-rows
  (implies (and (fmatp a m n) (posp m) (posp n)
                (natp i) (< i m) (natp j) (< j m) (not (= i j))
		(flistnp x n) (flistnp y n))
	   (equal (replace-row (replace-row a i x) j y)
	          (replace-row (replace-row a j y) i x))))

;; To show that 2 matrices of the same dimensions are equal, it surrices to show that
;; corresponding entries are equal.  That is, if 2 mxn matrices are not equal, then some
;; pair of corresponding entries are not equal:

(defund entry-diff (a b)
  (let* ((i (nth-diff a b))
	 (j (nth-diff (row i a) (row i b))))
    (cons i j)))

(defthmd fmat-entry-diff-lemma
  (implies (and (posp m) (posp n) (fmatp a m n) (fmatp b m n) (not (equal a b)))
	   (let* ((pair (entry-diff a b))
		  (i (car pair))
		  (j (cdr pair)))
	     (and (natp i) (< i m)
		  (natp j) (< j n)
		  (not (equal (entry i j a) (entry i j b))))))
  :hints (("Goal" :in-theory (enable entry-diff)
	   :use ((:instance nth-diff-diff (x a) (y b))
	         (:instance flistnp-row (i (nth-diff a b)))
	         (:instance flistnp-row (i (nth-diff a b))  (a b))
	         (:instance nth-diff-diff (x (row (nth-diff a b) a)) (y (row (nth-diff a b) b)))))))

;; Addition of mxn matrices:

(defun fmat-add (a b)
  (if (consp a)
      (cons (flist-add (car a) (car b))
	    (fmat-add (cdr a) (cdr b)))
    ()))

(defthm fmatp-fmat-add
  (implies (and (fmatp a m n) (fmatp b m n))
           (fmatp (fmat-add a b) m n)))

(defthmd fmat-add-comm
  (implies (and (fmatp a m n) (fmatp b m n))
           (equal (fmat-add a b)
		  (fmat-add b a)))
  :hints (("Subgoal *1/3" :in-theory (enable flist-add-comm))))

(defthmd fmat-add-assoc
  (implies (and (fmatp a m n) (fmatp b m n) (fmatp c m n))
           (equal (fmat-add a (fmat-add b c))
		  (fmat-add (fmat-add a b) c)))
  :hints (("Subgoal *1/4" :use ((:instance flist-add-assoc (x (car a)) (y (car b)) (z (car c)))))))

(defthmd row-fmat-add
  (implies (and (fmatp a m n) (fmatp b m n) (natp m) (natp n) (natp i) (< i m))
           (equal (row i (fmat-add a b))
		  (flist-add (row i a) (row i b)))))

(defthmd col-fmat-add
  (implies (and (fmatp a m n) (fmatp b m n) (natp m) (natp n) (natp j) (< j n))
           (equal (col j(fmat-add a b))
		  (flist-add (col j a) (col j b)))))

(defthmd fmat-add-entry
  (implies (and (fmatp a m n) (fmatp b m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (fmat-add a b))
	          (f+ (entry i j a) (entry i j b)))))

;; Multiply each entry of a by c:

(defun fmat-scalar-mul (c a)
  (if (consp a)
      (cons (flist-scalar-mul c (car a))
	    (fmat-scalar-mul c (cdr a)))
    ()))

(defthmd fmatp-fmat-scalar-mul
  (implies (and (fp c) (fmatp a m n))
	   (fmatp (fmat-scalar-mul c a) m n)))

(defthmd fmat-scalar-mul-assoc
  (implies (and (fp c) (fp d) (fmatp a m n))
	   (equal (fmat-scalar-mul c (fmat-scalar-mul d a))
		  (fmat-scalar-mul (f* c d) a))))

(defthmd fmat-scalar-mul-dist-1
  (implies (and (fp c) (fmatp a m n) (fmatp b m n))
	   (equal (fmat-scalar-mul c (fmat-add a b))
		  (fmat-add (fmat-scalar-mul c a) (fmat-scalar-mul c b)))))
 
(defthmd fmat-scalar-mul-dist-2
  (implies (and (fp c) (fp d) (fmatp a m n))
	   (equal (fmat-scalar-mul (f+ c d) a)
		  (fmat-add (fmat-scalar-mul c a) (fmat-scalar-mul d a)))))

(defthmd row-fmat-scalar-mul
  (implies (and (fp c) (fmatp a m n) (natp m) (natp n) (natp i) (< i m))
	   (equal (row i (fmat-scalar-mul c a))
		  (flist-scalar-mul c (row i a)))))

(defthmd col-fmat-scalar-mul
  (implies (and (fp c) (fmatp a m n) (natp m) (natp n) (natp j) (< j n))
	   (equal (col j (fmat-scalar-mul c a))
		  (flist-scalar-mul c (col j a)))))

(defthmd fmat-scalar-mul-entry
  (implies (and (fp c) (fmatp a m n) (natp m) (natp n) (natp i) (< i m) (natp j) (< j n))
	   (equal (entry i j (fmat-scalar-mul c a))
		  (f* c (entry i j a)))))

;; Sum of all entries of a:

(defun fmat-sum (a)
  (if (consp a)
      (f+ (flist-sum (car a))
	  (fmat-sum (cdr a)))
    (f0)))

(in-theory (disable (fmat-sum)))

(defthm fp-fmat-sum
  (implies (fmatp a m n)
           (fp (fmat-sum a))))

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

(local-defthmd fmatp-transpose-mat-aux
  (implies (and (natp m) (natp n) (fmatp a m n) (natp j) (< j n))
	   (fmatp (transpose-mat-aux a j n) (- n j) m)))

(defthmd fmatp-transpose
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (fmatp (transpose-mat a) n m))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance fmatp-transpose-mat-aux (j 0))
	                (:instance len-fmat-row (i 0))))))

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

(defthm nth-transpose-fmat
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp i) (< i n))
	   (equal (nth i (transpose-mat a))
		  (col i a)))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance nth-transpose-mat-aux (n (len (car a))) (j 0))
			(:instance len-fmat-row (i 0))))))

(defthm transpose-fmat-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a))))

(local-defthmd fmatp-transpose-2
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (fmatp (transpose-mat (transpose-mat a)) m n))
  :hints (("Goal" :in-theory (enable fmatp-transpose))))

(local-defthmd transpose-2-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry i j (transpose-mat (transpose-mat a)))
		  (entry i j a)))
  :hints (("Goal" :in-theory (e/d (fmatp-transpose) (entry)))))

(defthm transpose-fmat-2
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (transpose-mat (transpose-mat a))
	          a))
  :hints (("Goal" :in-theory (disable entry)
                  :use (fmatp-transpose-2
		        (:instance transpose-2-entry
			            (i (car (entry-diff a (transpose-mat (transpose-mat a)))))
		                    (j (cdr (entry-diff a (transpose-mat (transpose-mat a))))))
		        (:instance fmat-entry-diff-lemma (b (transpose-mat (transpose-mat a))))))))

(defthmd col-transpose-fmat
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp j) (< j m))
	   (equal (col j (transpose-mat a))
	          (row j a)))
  :hints (("Goal" :use (fmatp-transpose
                        (:instance nth-transpose-fmat (a (transpose-mat a)) (m n) (n m) (i j))))))

;; Replace kth column of a with r:

(defund replace-col (a k r)
  (transpose-mat (replace-row (transpose-mat a) k r)))

(defthm fmatp-replace-col
  (implies (and (fmatp a m n) (posp m) (posp n) (natp k) (< k n) (flistnp r m))
           (fmatp (replace-col a k r) m n))
  :hints (("Goal" :in-theory (enable replace-col)
	          :use (fmatp-transpose
		        (:instance fmatp-replace-row (a (transpose-mat a)) (m n) (n m))
			(:instance fmatp-transpose (m n) (n m) (a (replace-row (transpose-mat a) k r)))))))

(defthm fmat-col-replace-col
  (implies (and (fmatp a m n) (posp m) (posp n)
		(natp k) (< k n) (natp j) (< j n)
		(flistnp r m))
           (equal (col j (replace-col a k r))
	          (if (= j k)
		      r
		    (col j a))))
  :hints (("Goal" :in-theory (enable replace-col)
                  :use (fmatp-transpose
		        (:instance fmatp-replace-row (a (transpose-mat a)) (m n) (n m))
			(:instance fmatp-transpose (m n) (n m) (a (replace-row (transpose-mat a) k r)))
			(:instance col-transpose-fmat (a (replace-row (transpose-mat a) k r)) (m n) (n m))
			(:instance nth-replace-row (a (transpose-mat a)))))))

;; An important lemma in the proof of associativity of matrix multiplication:
;; If (fmatp a m n), then (fmat-sum (transpose-mat a)) = (fmat-sum a).
;; This holds trivially if either m = 0 or n = 0:

(local-defthm fmat-sum-0-1
  (implies (and (natp m) (fmatp a m 0))
           (equal (fmat-sum a) (f0)))
  :hints (("Goal" :in-theory (enable flist-sum))))

(defthm fmat-sum-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum a) (f0)))
  :hints (("Goal" :in-theory (enable flist-sum))))

(local-defthm fmat-sum-transpose-0-1
  (implies (and (natp n) (fmatp a 0 n))
           (equal (col j a) ())))

(local-defthm fmat-sum-transpose-0-2
  (implies (and (natp n) (fmatp a 0 n))
           (equal (fmat-sum (transpose-mat-aux a j n))
	          (f0)))
  :hints (("Goal" :in-theory (enable flist-sum))))

(defthm fmat-sum-transpose-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum (transpose-mat a))
	          (f0)))
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

(local-defthmd fmatp-cdr
  (implies (and (posp m) (posp n) (fmatp a m n))
           (fmatp (cdr a) (1- m) n)))

(local-defthmd fmatp-cdrs
  (implies (and (natp m) (posp n) (fmatp a m n))
           (fmatp (cdrs a) m (1- n))))

(defthmd fmatp-strip-mat
  (implies (and (posp m) (posp n) (fmatp a m n))
           (fmatp (strip-mat a) (1- m) (1- n)))
  :hints (("Goal" :in-theory (enable strip-mat)
	   :use (fmatp-cdr (:instance fmatp-cdrs (m (1- m)))))))


(in-theory (enable flist-sum))

(local-defthmd sum-fmat-strip-mat-1
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
		  (f+ (f+ (entry 0 0 a) (flist-sum (cdr (row 0 a))))
		      (fmat-sum (cdr a))))))

(local-defthmd sum-fmat-strip-mat-2
  (implies (and (natp m) (posp n) (fmatp a m n))
           (and (flistnp (cars a) m)
	        (fmatp (cdrs a) m (1- n)))))

(local-defthmd sum-fmat-strip-mat-3
  (IMPLIES (AND (natp m) (posp n) (fmatp a m n))
           (EQUAL (F+ (F+ (CAR (CAR A))
                          (FLIST-SUM (CDR (CAR A))))
                      (F+ (FLIST-SUM (CARS (CDR A)))
                          (FMAT-SUM (CDRS (CDR A)))))
                  (F+ (F+ (CAR (CAR A))
                          (FLIST-SUM (CARS (CDR A))))
                      (F+ (FLIST-SUM (CDR (CAR A)))
                          (FMAT-SUM (CDRS (CDR A)))))))
  :hints (("Goal" :in-theory (enable f+assoc)
                  :use ((:instance sum-fmat-strip-mat-2 (a (cdr a)) (m (1- m)))
		        (:instance f+assoc (x (caar a)) (y (flist-sum (cdar a))) (z (flist-sum (cars (cdr a)))))
		        (:instance f+assoc (x (caar a)) (z (flist-sum (cdar a))) (y (flist-sum (cars (cdr a)))))
			(:instance f+comm (x (flist-sum (cdar a))) (y (flist-sum (cars (cdr a)))))))))

(local-defthmd sum-fmat-strip-mat-4
  (implies (and (natp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
	          (f+ (flist-sum (cars a))
		      (fmat-sum (cdrs a)))))
  :hints (("Subgoal *1/5" :use (sum-fmat-strip-mat-3))))

(local-defthmd flist-sum-cars-cdr
  (equal (flist-sum (cars (cdr a)))
         (flist-sum (cdr (cars a)))))

(local-defthmd cars-col-0
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (cars a) (col 0 a))))

(local-defthmd sum-fmat-strip-mat-5
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum (cdr a))
	          (f+ (flist-sum (cdr (col 0 a)))
		      (fmat-sum (strip-mat a)))))
  :hints (("Goal" :in-theory (enable strip-mat)
                  :use (flist-sum-cars-cdr cars-col-0
		        (:instance sum-fmat-strip-mat-4 (m (1- m)) (a (cdr a)))))))

(local-defthmd sum-fmat-strip-mat-6
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
		  (f+ (f+ (entry 0 0 a) (flist-sum (cdr (row 0 a))))
		      (f+ (flist-sum (cdr (col 0 a)))
		          (fmat-sum (strip-mat a))))))
  :hints (("Goal" :use (sum-fmat-strip-mat-1 sum-fmat-strip-mat-5))))

(defthmd sum-fmat-strip-mat
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
		  (f+ (entry 0 0 a)
		      (f+ (f+ (flist-sum (cdr (row 0 a)))
			      (flist-sum (cdr (col 0 a))))
			  (fmat-sum (strip-mat a))))))			  
  :hints (("Goal" :in-theory (e/d (sum-fmat-strip-mat-6 f+assoc) (flistnp-col))
                  :use (fmatp-strip-mat
		        (:instance flistnp-row (i 0))
		        (:instance flistnp-col (j 0))
		        (:instance fp-entry (i 0) (j 0))))))

;; Since (row 0 a) = (col 0 (transpose-mat a)) and (col 0 a) = (row 0 (transpose-mat a)), we have
;; the rollowing:

(defthmd sum-fmat-strip-mat-equal
  (implies (and (posp m) (posp n) (fmatp a m n)
                (equal (fmat-sum (strip-mat a)) (fmat-sum (strip-mat (transpose-mat a)))))
	   (equal (fmat-sum (transpose-mat a))
		  (fmat-sum a)))
  :hints (("Goal" :in-theory (e/d (sum-fmat-strip-mat col-transpose-fmat) (flistnp-col))
                  :use (fmatp-transpose
		        (:instance flistnp-row (i 0))
		        (:instance flistnp-col (j 0))
		        (:instance f+comm (x (flist-sum (cdr (row 0 a)))) (y (flist-sum (cdr (col 0 a)))))))))

;; If either m = 0 or n = 0, then the hypothesis of sum-fmat-strip-mat-equal holds trivially:

(defthm fmat-sum-strip-mat-0
  (implies (and (posp m) (posp n) (or (= m 1) (= n 1)) (fmatp a m n))
           (and (equal (fmat-sum (strip-mat a)) (f0))
	        (equal (fmat-sum (strip-mat (transpose-mat a))) (f0))))
  :hints (("Goal" :use (fmatp-strip-mat fmatp-transpose
                        (:instance fmatp-strip-mat (a (transpose-mat a)) (m n) (n m))
			(:instance fmat-sum-0 (a (strip-mat a)) (m (1- m)) (n (1- n)))
			(:instance fmat-sum-0 (a (strip-mat (transpose-mat a))) (m (1- n)) (n (1- m)))))))

(local-defthmd nth-cdr
  (implies (and (posp i) (consp l))
	   (equal (nth i l)
		  (nth (1- i) (cdr l)))))

(local-defthmd nth-cdrs
  (implies (and (natp i) (consp l))
	   (equal (nth i (cdrs l))
		  (cdr (nth i l)))))

(defthmd strip-fmat-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp i) (natp j) (< i (1- m)) (< j (1- n)))
	   (equal (entry i j (strip-mat a))
		  (entry (1+ i) (1+ j) a)))
  :hints (("Goal" :in-theory (enable strip-mat)
	   :use ((:instance nth-cdr (i (1+ i)) (l a))
		 (:instance nth-cdr (i (1+ j)) (l (nth i (cdr a))))
		 (:instance nth-cdrs (l (cdr a)))))))

(local-defthmd fmatp-transpose-strip-mat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (fmatp a m n))
           (and (fmatp (transpose-mat (strip-mat a)) (1- n) (1- m))
	        (fmatp (strip-mat (transpose-mat a)) (1- n) (1- m))))
  :hints (("Goal" :use (fmatp-transpose fmatp-strip-mat
                        (:instance fmatp-transpose (a (strip-mat a)) (m (1- m)) (n (1- n)))
			(:instance fmatp-strip-mat (a (transpose-mat a)) (m n) (n m))))))

(local-defthmd entry-transpose-strip-mat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (fmatp a m n)
		(natp i) (natp j) (< i (1- n)) (< j (1- m)))
	   (equal (entry i j (transpose-mat (strip-mat a)))
		  (entry i j (strip-mat (transpose-mat a)))))
  :hints (("Goal" :use (fmatp-transpose fmatp-strip-mat
                        (:instance transpose-fmat-entry (a (strip-mat a)) (m (1- m)) (n (1- n)) (i j) (j i))
			(:instance strip-fmat-entry (i j) (j i))
			(:instance strip-fmat-entry (a (transpose-mat a)) (m n) (n m))
			(:instance transpose-fmat-entry (i (1+ j)) (j (1+ i)))))))

;; In the remaining case, we have the rollowing:

(defthmd transpose-strip-mat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (fmatp a m n))
	   (equal (transpose-mat (strip-mat a))
		  (strip-mat (transpose-mat a))))
  :hints (("Goal" :use (fmatp-transpose-strip-mat
                        (:instance fmat-entry-diff-lemma (a (transpose-mat (strip-mat a))) (b (strip-mat (transpose-mat a))) (m (1- n)) (n (1- m)))
			(:instance entry-transpose-strip-mat
			  (i (car (entry-diff (transpose-mat (strip-mat a)) (strip-mat (transpose-mat a)))))
			  (j (cdr (entry-diff (transpose-mat (strip-mat a)) (strip-mat (transpose-mat a))))))))))

(local-defun sum-fmat-transpose-induct (a m n)
  (if (and (posp m) (posp n))
      (list (sum-fmat-transpose-induct (strip-mat a) (1- m) (1- n)))
    (list a m n)))

;; The result rollows by induction:

(defthmd sum-fmat-transpose
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (equal (fmat-sum (transpose-mat a))
		  (fmat-sum a)))
  :hints (("Goal" :induct (sum-fmat-transpose-induct a m n))
          ("Subgoal *1/1" :use (fmatp-strip-mat sum-fmat-strip-mat-equal transpose-strip-mat fmat-sum-strip-mat-0))))


;;----------------------------------------------------------------------------------------
;; Matrix Multiplication
;;----------------------------------------------------------------------------------------

;; Dot product of 2 lists of rield elements of the same length:

(defun fdot (x y)
  (if (consp x)
      (f+ (f* (car x) (car y))
          (fdot (cdr x) (cdr y)))
    (f0)))

(in-theory (disable (fdot)))

(defthm fp-fdot
  (implies (and (flistnp x n) (flistnp y n))
           (fp (fdot x y)))
  :hints (("Goal" :in-theory (disable (fdot)))))

(defthm fdot-flistn0
  (implies (and (natp n) (flistnp x n))
           (equal (fdot (flistn0 n) x)
	          (f0)))
  :hints (("Goal" :in-theory (disable (fdot)))))

(defthmd fdot-comm
  (implies (and (flistnp x n) (flistnp y n))
           (equal (fdot x y) (fdot y x)))
  :hints (("Subgoal *1/1" :use ((:instance f*comm (x (car x)) (y (car y)))))
          ("Subgoal *1/3" :use ((:instance f*comm (x (car x)) (y (car y)))))))

(defthmd fdot-flist-add
  (implies (and (flistnp x n) (flistnp y n) (flistnp z n))
	   (equal (fdot (flist-add x y) z)
		  (f+ (fdot x z) (fdot y z))))
  :hints (("Subgoal *1/4" :use ((:instance f+assoc (x (F* (CAR X) (CAR Z)))
					           (y (FDOT (CDR X) (CDR Z)))
					           (z (F+ (F* (CAR Y) (CAR Z)) (FDOT (CDR Y) (CDR Z)))))
				(:instance f+assoc (x (FDOT (CDR X) (CDR Z)))
					           (y (F* (CAR Y) (CAR Z)))
						   (z (FDOT (CDR Y) (CDR Z))))
				(:instance f+comm (x (F* (CAR Y) (CAR Z)))
				                  (y (FDOT (CDR X) (CDR Z))))
				(:instance f+assoc (x (F* (CAR Y) (CAR Z)))
				                   (y (FDOT (CDR X) (CDR Z)))
						   (z (FDOT (CDR Y) (CDR Z))))
				(:instance f+assoc (x (F* (CAR X) (CAR Z)))
				                   (y (F* (CAR Y) (CAR Z)))
						   (z (FDOT (FLIST-ADD (CDR X) (CDR Y)) (CDR Z))))))))

(defthmd fdot-flist-add-comm
  (implies (and (flistnp x n) (flistnp y n) (flistnp z n))
	   (equal (fdot z (flist-add x y))
		  (f+ (fdot z x) (fdot z y))))
  :hints (("Goal" :use (fdot-flist-add
                        (:instance fdot-comm (y z))
			(:instance fdot-comm (x z))
			(:instance fdot-comm (x z) (y (flist-add x y)))))))
					   
(defthmd fdot-flist-scalar-mul
  (implies (and (flistnp x n) (flistnp y n) (fp c))
	   (equal (fdot (flist-scalar-mul c x) y)
		  (f* c (fdot x y))))
  :hints (("Goal" :in-theory (enable f*assoc))))

;; List of dot products of an flist x with the elements of a list of flists l:

(defun fdot-list (x l)
  (if (consp l)
      (cons (fdot x (car l))
            (fdot-list x (cdr l)))
    ()))

(defthm flistnp-fdot-list
  (implies (and (fmatp l m n) (flistnp x n))
           (flistnp (fdot-list x l) m)))

(defthm nth-fdot-list
  (implies (and (natp j) (< j (len l)))
           (equal (nth j (fdot-list x l))
	          (fdot x (nth j l)))))

;; Product of mxn matrix a and nxp matrix b:

(defund fmat* (a b)
  (if (consp a)
      (cons (fdot-list (car a) (transpose-mat b))
            (fmat* (cdr a) b))
    ()))

(defthm fmatp-fmat*
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (posp n) (posp p) )
           (fmatp (fmat* a b) m p))
  :hints (("Subgoal *1/7" :expand ((fmat* a b)))
          ("Subgoal *1/6" :expand ((fmat* a b))
	                  :use ((:instance fmatp-transpose (a b) (m n) (n p))))
          ("Subgoal *1/5" :expand ((fmat* a b)))
          ("Subgoal *1/4" :expand ((fmat* a b) (fmat* () b)))))

(defthmd nth-fmat*
  (implies (and (natp m) (fmatp a m n) (natp i) (< i m))
           (equal (nth i (fmat* a b))
	          (fdot-list (nth i a) (transpose-mat b))))
  :hints (("Goal" :in-theory (enable fmat*))))

(defthmd fmat*-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* a b))
	          (fdot (row i a) (col j b))))
  :hints (("Goal" :in-theory (enable nth-fmat*)
	   :use ((:instance fmatp-transpose (a b) (m n) (n p))))))

(local-defthmd fmat*-dist-1-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a1 m n) (fmatp a2 m n) (fmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* (fmat-add a1 a2) b))
		  (entry i j (fmat-add (fmat* a1 b) (fmat* a2 b)))))
  :hints (("Goal" :in-theory (e/d (fmat*-entry fmat-add-entry) (fdot-flist-add fmatp-fmat* entry))
                  :use ((:instance fmatp-fmat* (a a1))
		        (:instance fmatp-fmat* (a a2))
			(:instance row-fmat-add (a a1) (b a2))
			(:instance fdot-flist-add (x (nth i a1)) (y (nth i a2)) (z (col j b)))
			(:instance flistnp-row (a a1))
			(:instance flistnp-row (a a2))))))

(defthmd fmat*-dist-1
  (implies (and (posp m) (posp n) (posp p) (fmatp a1 m n) (fmatp a2 m n) (fmatp b n p))
	   (equal (fmat* (fmat-add a1 a2) b)
		  (fmat-add (fmat* a1 b) (fmat* a2 b))))
  :hints (("Goal" :in-theory (disable fmatp-fmat-add)
                  :use ((:instance fmat-entry-diff-lemma (a (fmat* (fmat-add a1 a2) b)) (b (fmat-add (fmat* a1 b) (fmat* a2 b))) (n p))
                        (:instance fmat*-dist-1-entry
			  (i (car (entry-diff (fmat* (fmat-add a1 a2) b) (fmat-add (fmat* a1 b) (fmat* a2 b)))))
			  (j (cdr (entry-diff (fmat* (fmat-add a1 a2) b) (fmat-add (fmat* a1 b) (fmat* a2 b))))))
			(:instance fmatp-fmat* (a (fmat-add a1 a2)))
			(:instance fmatp-fmat-add (a (fmat* a1 b)) (b (fmat* a2 b)) (n p))
			(:instance fmatp-fmat-add (a a1) (b a2))))))

(local-defthmd fmat*-dist-2-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b1 n p) (fmatp b2 n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* a (fmat-add b1 b2)))
		  (entry i j (fmat-add (fmat* a b1) (fmat* a b2)))))
  :hints (("Goal" :in-theory (e/d (col-fmat-add fmat*-entry fmat-add-entry) (fdot-flist-add fmatp-fmat* entry))
                  :use (flistnp-row
		        (:instance fmatp-fmat* (b b1))
		        (:instance fmatp-fmat* (b b2))
			(:instance col-fmat-add (a b1) (b b2) (m n) (n p))			
			(:instance fdot-flist-add (z (nth i a)) (x (col j b1)) (y (col j b2)))
			(:instance fdot-comm (x (nth i a)) (y (flist-add (col j b1) (col j b2))))
			(:instance fdot-comm (x (NTH I A)) (y (col j b1)))
			(:instance fdot-comm (x (nth i a)) (y (col j b2)))
			(:instance flistnp-col (a b1) (m n) (n p))
			(:instance flistnp-col (a b2) (m n) (n p))))))
			
(defthmd fmat*-dist-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b1 n p) (fmatp b2 n p))
	   (equal (fmat* a (fmat-add b1 b2))
		  (fmat-add (fmat* a b1) (fmat* a b2))))
  :hints (("Goal" :in-theory (disable fmatp-fmat-add)
                  :use ((:instance fmat-entry-diff-lemma (a (fmat* a (fmat-add b1 b2))) (b (fmat-add (fmat* a b1) (fmat* a b2))) (n p))
                        (:instance fmat*-dist-2-entry
			  (i (car (entry-diff (fmat* a(fmat-add b1 b2)) (fmat-add (fmat* a b1) (fmat* a b2)))))
			  (j (cdr (entry-diff (fmat* a(fmat-add b1 b2)) (fmat-add (fmat* a b1) (fmat* a b2))))))
			(:instance fmatp-fmat* (b (fmat-add b1 b2)))
			(:instance fmatp-fmat-add (a (fmat* a b1)) (b (fmat* a b2)) (n p))
			(:instance fmatp-fmat-add (a b1) (b b2) (m n) (n p))))))

(local-defthmd fmat*-fmat-scalar-mul-1-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* (fmat-scalar-mul c a) b))
		  (entry i j (fmat-scalar-mul c (fmat* a b)))))
  :hints (("Goal" :in-theory (e/d (fmat-scalar-mul-entry fmat*-entry) (fdot-flist-add fmatp-fmat* entry))  
                  :use (row-fmat-scalar-mul fmatp-fmat*	fmatp-fmat-scalar-mul flistnp-row
		        (:instance fdot-flist-scalar-mul (x (nth i a)) (y (col j b)))
			(:instance flistnp-col (a b) (m n) (n p))
		        (:instance fmatp-fmat-scalar-mul (a (fmat* a b)) (n p))))))

(defthmd fmat*-fmat-scalar-mul-1
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c))
	   (equal (fmat* (fmat-scalar-mul c a) b)
		  (fmat-scalar-mul c (fmat* a b))))
  :hints (("Goal" :use (fmatp-fmat-scalar-mul
                        (:instance fmatp-fmat-scalar-mul (a (fmat* a b)) (n p))
                        (:instance fmatp-fmat* (a (fmat-scalar-mul c a)))
                        (:instance fmat-entry-diff-lemma (a (fmat* (fmat-scalar-mul c a) b)) (b (fmat-scalar-mul c (fmat* a b))) (n p))
                        (:instance fmat*-fmat-scalar-mul-1-entry
			            (i (car (entry-diff (fmat* (fmat-scalar-mul c a) b) (fmat-scalar-mul c (fmat* a b)))))
			            (j (cdr (entry-diff (fmat* (fmat-scalar-mul c a) b) (fmat-scalar-mul c (fmat* a b))))))))))

(local-defthmd fmat*-fmat-scalar-mul-2-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* a (fmat-scalar-mul c b)))
		  (entry i j (fmat-scalar-mul c (fmat* a b)))))
  :hints (("Goal" :in-theory (e/d (fmat-scalar-mul-entry fmat*-entry) (fdot-flist-add fmatp-fmat* entry))  
                  :use (fmatp-fmat* flistnp-row
		        (:instance fmatp-fmat-scalar-mul  (a b) (m n) (n p))
		        (:instance col-fmat-scalar-mul (a b) (m n) (n p))
			(:instance fdot-comm (x (nth i a)) (y (COL J (FMAT-SCALAR-MUL C B))))
			(:instance fdot-flist-scalar-mul (x (col j b)) (y (nth i a)))
			(:instance flistnp-col (a b) (m n) (n p))
			(:instance fdot-comm (x (nth i a)) (y (col j b)))))))

(defthmd fmat*-fmat-scalar-mul-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c))
	   (equal (fmat* a (fmat-scalar-mul c b))
		  (fmat-scalar-mul c (fmat* a b))))
  :hints (("Goal" :use ((:instance fmatp-fmat-scalar-mul (a b) (m n) (n p))
                        (:instance fmatp-fmat-scalar-mul (a (fmat* a b)) (n p))
                        (:instance fmatp-fmat* (b (fmat-scalar-mul c b)))
                        (:instance fmat-entry-diff-lemma (a (fmat* a (fmat-scalar-mul c b))) (b (fmat-scalar-mul c (fmat* a b))) (n p))
                        (:instance fmat*-fmat-scalar-mul-2-entry
			            (i (car (entry-diff (fmat* a (fmat-scalar-mul c b)) (fmat-scalar-mul c (fmat* a b)))))
			            (j (cdr (entry-diff (fmat* a (fmat-scalar-mul c b)) (fmat-scalar-mul c (fmat* a b))))))))))

(local-defthmd transpose-fmat*-entry-1
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (transpose-mat (fmat* a b)))
	          (fdot (row j a) (col i b))))
  :hints (("Goal" :use (fmatp-fmat*
                        (:instance transpose-fmat-entry (i j) (j i) (a (fmat* a b)) (n p))
                        (:instance fmat*-entry (i j) (j i))))))

(local-defthmd transpose-fmat*-entry-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (fmat* (transpose-mat b) (transpose-mat a)))
	          (fdot (col i b) (row j a))))
  :hints (("Goal" :use (fmatp-fmat* col-transpose-fmat fmatp-transpose
                        (:instance fmatp-transpose (a b) (m n) (n p))
                        (:instance fmat*-entry (a (transpose-mat b)) (b (transpose-mat a)) (m p) (p m))))))

(local-defthmd transpose-fmat*-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i p) (natp j) (< j m))
	   (equal (entry i j (transpose-mat (fmat* a b)))
	          (entry i j (fmat* (transpose-mat b) (transpose-mat a)))))
  :hints (("Goal" :use (transpose-fmat*-entry-1 transpose-fmat*-entry-2
                        (:instance flistnp-row (i j))
                        (:instance fdot-comm (x (row j a)) (y (col i b)))))))

;; Transpose of a product:

(defthmd transpose-fmat*
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p))
	   (equal (transpose-mat (fmat* a b))
	          (fmat* (transpose-mat b) (transpose-mat a))))
  :hints (("Goal" :use (fmatp-fmat* fmatp-transpose
                        (:instance fmatp-transpose (a b) (m n) (n p))
                        (:instance fmatp-transpose (a (fmat* a b)) (n p))
			(:instance fmatp-fmat* (a (transpose-mat b)) (b (transpose-mat a)) (m p) (p m))
			(:instance fmat-entry-diff-lemma (m p) (n m)
			                            (a (transpose-mat (fmat* a b)))
			                            (b (fmat* (transpose-mat b) (transpose-mat a))))
                        (:instance transpose-fmat*-entry
			            (i (car (entry-diff (transpose-mat (fmat* a b)) (fmat* (transpose-mat b) (transpose-mat a)))))
                                    (j (cdr (entry-diff (transpose-mat (fmat* a b)) (fmat* (transpose-mat b) (transpose-mat a))))))))))

;; The definition of the nxn identity matrix is based on that of an flist of length n
;; with (f1) at index j and (f0) elsewhere:

(defun funit (j n)
  (if (zp n)
      ()
    (if (zp j)
        (cons (f1) (flistn0 (1- n)))
      (cons (f0) (funit (1- j) (1- n))))))

(defthm flistnp-funit
  (flistnp (funit j n) n))

(defun fdelta (i j)
  (if (= i j) (f1) (f0)))

(local-defun nth-funit-induct (i j n)
  (if (or (zp i) (zp j) (zp n))
      t
    (list (nth-funit-induct (1- i) (1- j) (1- n)))))

(defthm nth-funit
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i n))
           (equal (nth i (funit j n))
	          (fdelta i j)))
  :hints (("Goal" :induct (nth-funit-induct i j n))  
          ("Subgoal *1/1" :expand ((funit j n)))))

;; Dot product of (funit j n) with an flist of length n:

(defthm fdot-funit
  (implies (and (posp n) (flistnp x n) (natp j) (< j n))
           (equal (fdot (funit j n) x)
	          (nth j x))))

(defthm fdot-funit-comm
  (implies (and (posp n) (flistnp x n) (natp j) (< j n))
           (equal (fdot x (funit j n))
	          (nth j x)))
  :hints (("Goal" :use ((:instance fdot-comm (y (funit j n)))))))

;; nxn identity matrix:

(defun id-fmat-aux (j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (funit j n) (id-fmat-aux (1+ j) n))
    ()))

(defund id-fmat (n)
  (id-fmat-aux 0 n))

(local-defthmd fmatp-id-fmat-aux
  (implies (and (posp n) (natp j) (<= j n))
           (fmatp (id-fmat-aux j n) (- n j) n)))

(defthm fmatp-id-fmat
  (implies (posp n)
           (fmatp (id-fmat n) n n))
  :hints (("Goal" :in-theory (enable id-fmat)
                  :use ((:instance fmatp-id-fmat-aux (j 0))))))

(local-defthmd nth-id-fmat-aux
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i (- n j)))
	   (equal (nth i (id-fmat-aux j n))
		  (funit (+ j i) n)))
  :hints (("Goal" :induct (transpose-mat-aux-induct i j))
	  ("Subgoal *1/1" :expand ((id-fmat-aux j n)))))

(defthm nth-id-fmat
  (implies (and (posp n) (natp i) (< i n))
	   (equal (nth i (id-fmat n))
		  (funit i n)))
  :hints (("Goal" :in-theory (enable id-fmat)
                  :use ((:instance nth-id-fmat-aux (j 0))))))

(defthmd entry-id-fmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (id-fmat n))
	          (fdelta i j))))

(local-defthmd entry-transpose-id-fmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (transpose-mat (id-fmat n)))
	          (entry i j (id-fmat n))))
  :hints  (("Goal" :use (entry-id-fmat
                         (:instance entry-id-fmat (i j) (j i))
			 (:instance transpose-fmat-entry (a (id-fmat n)) (m n) (i j) (j i))))))

(defthmd transpose-id-fmat
  (implies (natp n)
           (equal (transpose-mat (id-fmat n))
	          (id-fmat n)))
  :hints  (("Goal" :use (fmatp-id-fmat
                         (:instance fmatp-transpose (a (id-fmat n)) (m n))
                         (:instance fmat-entry-diff-lemma (m n) (a (id-fmat n)) (b (transpose-mat (id-fmat n))))
			 (:instance entry-transpose-id-fmat (i (car (entry-diff (id-fmat n) (transpose-mat (id-fmat n)))))
			                                   (j (cdr (entry-diff (id-fmat n) (transpose-mat (id-fmat n))))))))))

(defthm col-id-fmat
  (implies (and (natp n) (natp j) (< j n))
           (equal (col j (id-fmat n))
	          (funit j n)))
  :hints (("Goal" :use (transpose-id-fmat
                        (:instance nth-transpose-fmat (m n) (a (id-fmat n)) (i j))))))

;; (id-fmat n) is a right identity:

(local-defthmd entry-fmat*-id-fmat-right
  (implies (and (posp m) (posp n) (fmatp a m n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (fmat* a (id-fmat n)))
	          (entry i j a)))
  :hints (("Goal" :use (flistnp-row
                        (:instance fmat*-entry (p n) (b (id-fmat n)))
                        (:instance fdot-comm (x (funit j n)) (y (nth i a)))))))

(defthmd id-fmat-right
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* a (id-fmat n))
	          a))
  :hints (("Goal" :use ((:instance fmatp-fmat* (b (id-fmat n)) (p n))
			(:instance entry-fmat*-id-fmat-right (i (car (entry-diff a (fmat* a (id-fmat n)))))
			                                    (j (cdr (entry-diff a (fmat* a (id-fmat n))))))
                        (:instance fmat-entry-diff-lemma (b (fmat* a (id-fmat n))))))))

;; (id-fmat n) is a left identity:

(local-defthmd entry-fmat*-id-fmat-left
  (implies (and (posp m) (posp n) (fmatp a m n) (natp i) (< i m) (natp j) (< j n))
           (equal (entry i j (fmat* (id-fmat m) a))
	          (entry i j a)))
  :hints (("Goal" :use (flistnp-row nth-col
                        (:instance fmat*-entry (n m) (p n) (a (id-fmat m)) (b a))))))

(defthmd id-fmat-left
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* (id-fmat m) a)
	          a))
  :hints (("Goal" :use ((:instance fmatp-fmat* (a (id-fmat m)) (b a) (n m) (p n))
			(:instance entry-fmat*-id-fmat-left (i (car (entry-diff a (fmat* (id-fmat m) a))))
			                                   (j (cdr (entry-diff a (fmat* (id-fmat m) a)))))
                        (:instance fmat-entry-diff-lemma (b (fmat* (id-fmat m) a)))))))
							   
;; Associativity:

;; Let a, b, and c be matrices of dimensions mxn, nxp, and pxq, respectively.  Then
;; (fmat* a (fmat* b c)) and (fmat* (fmat* a b) c)) are both mxp matrices.  Our
;; objective is to prove that they are equal.  Let 0 <= i < m and 0 <= j < q.  It will
;; surrice to show that

;;    (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)).

;; Applying fmat*-entry and expanding fdot, we find that both sides of this equation
;; are sums of n*p 3-way products.

;; We shall construct an nxp matrix of 3-way products, (fmat12 a b c i j), such that

;;    (entry i j (fmat* a (fmat* b c))) = (fmat-sum (fmat12 a b c i j))

;; and a pxn matrix of 3-way products, (fmat21 a b c), such that

;;    (entry i j (fmat* (fmat* a b) c)) = (fmat-sum (fmat21 a b c i j)).

;; We shall show that (fmat21 a b c i j) = (transpose-mat (fmat12 a b c i j)) and apply
;; fmat-sum-transpose to conclude that

;;    (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)).

;; The entry on the left is the dot product of a row of a and a column of (fmat* b c),
;; and each entry of this column is a dot product of a row of b and a column of c.
;; This leads to the definition of the nxp matrix of 3-way products, (fmat12 a b c i j):

(defun flist-mul-list (x l)
  (if (consp l)
      (cons (flist-mul x (car l))
	    (flist-mul-list x (cdr l)))
    ()))

(defun flist-scalar-mul-list (x l)
  (if (consp l)
      (cons (flist-scalar-mul (car x) (car l))
            (flist-scalar-mul-list (cdr x) (cdr l)))
    ()))

(defund fmat12 (a b c i j)
  (flist-scalar-mul-list (row i a)
	   	         (flist-mul-list (col j c) b)))

(local-defun flist-sum-list (l)
  (if (consp l)
      (cons (flist-sum (car l))
            (flist-sum-list (cdr l)))
    ()))

(local-defthm flist-sum-flist-scalar-mul
  (implies (and (fp x) (flistnp l n))
           (equal (flist-sum (flist-scalar-mul x l))
	          (f* x (flist-sum l)))))

(local-defthmd fmat-sum-flist-scalar-mul-list
  (implies (and (flistnp x n) (fmatp l n p))
           (equal (fmat-sum (flist-scalar-mul-list x l))
                  (fdot x (flist-sum-list l)))))

(local-defthm fmatp-flist-mul-list
  (implies (and (fmatp a m n) (flistnp x n))
           (fmatp (flist-mul-list x a) m n)))

(local-defthm fmatp-flist-scalar-mul-list
  (implies (and (fmatp a m n) (flistnp x m))
           (fmatp (flist-scalar-mul-list x a) m n)))

(defthmd fmatp-fmat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (fmat12 a b c i j) n p))
  :hints (("Goal" :in-theory (e/d (fmat12) (flistnp-col))
                  :use (flistnp-row
		        (:instance flistnp-col (a c) (m p) (n q))))))

;; We derive the rollowing expression for each entry of this matrix:

(local-defthmd nth-flist-scalar-mul-list
  (equal (nth r (flist-scalar-mul-list x l))
         (flist-scalar-mul (nth r x) (nth r l))))

(local-defthmd nth-flist-mul-list
  (implies (and (natp r) (< r (len l)))
           (equal (nth r (flist-mul-list x l))
	          (flist-mul x (nth r l)))))

(local-defthmd nth-flist-scalar-mul-2
  (implies (and (natp s) (< s (len x)))
	   (equal (nth s (flist-scalar-mul c x))
		  (f* c (nth s x)))))

(local-defthmd nth-flist-mul
  (implies (and (natp s) (< s (len x)) (< s (len y)))
           (equal (nth s (flist-mul x y))
	          (f* (nth s x) (nth s y)))))

(local-defthmd fmat12-entry-1
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (fmat12 a b c i j)))
	          (nth s (flist-scalar-mul (entry i r a) (nth r (flist-mul-list (col j c) b))))))
  :hints (("Goal" :in-theory (enable fmat12 nth-flist-scalar-mul-list))))

(local-defthmd fmat12-entry-2
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (fmat12 a b c i j)))
	          (nth s (flist-scalar-mul (entry i r a) (flist-mul (col j c) (nth r b))))))
  :hints (("Goal" :in-theory (enable fmat12-entry-1 nth-flist-mul-list))))

(local-defthmd fmat12-entry-3
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (fmat12 a b c i j)))
	          (f* (entry i r a) (nth s (flist-mul (col j c) (nth r b))))))
  :hints (("Goal" :in-theory (e/d (fmat12-entry-2) (flistnp-col flistnp-flist-mul))
                  :use ((:instance nth-flist-scalar-mul-2 (c (entry i r a)) (x (flist-mul (col j c) (nth r b))))
		        (:instance flistnp-flist-mul (n p) (x (col j c)) (y (nth r b)))
			(:instance flistnp-row (a b) (i r) (m n) (n p))
			(:instance flistnp-col (a c) (m p) (n q))))))

(local-defthmd fmat12-entry-4
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (fmat12 a b c i j)))
	          (f* (entry i r a) (f* (entry s j c) (entry r s b)))))
  :hints (("Goal" :in-theory (e/d (fmat12-entry-3 nth-col) (flistnp-col))
                  :use ((:instance nth-flist-mul (x (col j c)) (y (nth r b)))
			(:instance flistnp-row (a b) (i r) (m n) (n p))
			(:instance flistnp-col (a c) (m p) (n q))))))

(local-defthmd fmat12-entry-5
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (nth s (nth r (fmat12 a b c i j)))
	          (f* (entry i r a) (f* (entry r s b) (entry s j c)))))
  :hints (("Goal" :in-theory (enable fmat12-entry-4)
                  :use ((:instance fp-entry (a b) (m n) (n p) (i r) (j s))
			(:instance fp-entry (a c) (m p) (n q) (i s))
			(:instance f*comm (x (entry r s b)) (y (entry s j c)))))))

(defthmd fmat12-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (entry r s (fmat12 a b c i j))
	          (f* (f* (entry i r a) (entry r s b)) (entry s j c))))
  :hints (("Goal" :in-theory (enable fmat12-entry-5 f*assoc)
                  :use ((:instance fp-entry (j r))
			(:instance fp-entry (a b) (m n) (n p) (i r) (j s))
			(:instance fp-entry (a c) (m p) (n q) (i s))))))

;; The sum of these entries:

(local-defthm fmat-sum-fmat12-fdot
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat12 a b c i j))
	          (fdot (row i a)
		        (flist-sum-list (flist-mul-list (col j c) b)))))
  :hints (("Goal" :in-theory (enable fmat12)
                  :use (flistnp-row
		        (:instance fmat-sum-flist-scalar-mul-list (x (row i a)) (l (flist-mul-list (col j c) b)))))))	          

(local-defthm flist-sum-flist-mul
  (implies (and (flistnp x n) (flistnp y n))
           (equal (flist-sum (flist-mul x y))
	          (fdot x y))))

(local-defthm flist-sum-list-flist-mul-list-col
  (implies (and (posp p) (posp q) (fmatp b n p) (fmatp c p q) (natp j) (< j q))
           (equal (flist-sum-list (flist-mul-list (col j c) b))
	          (col j (fmat* b c))))
  :hints (("Subgoal *1/3" :in-theory (disable flistnp-col)
                          :expand ((fmat* b c))
                          :use ((:instance fmatp-transpose (a c) (m p) (n q))
			        (:instance flistnp-row (a b) (m n) (n p) (i 0))
			        (:instance flistnp-col (a c) (m p) (n q))
				(:instance fdot-comm (n p) (x (col j c)) (y (car b)))))
          ("Subgoal *1/1" :expand ((fmat* () c)))))

(local-defthm fmat-sum-fmat12-fdot-row-col
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat12 a b c i j))
	          (fdot (row i a) (col j (fmat* b c))))))

(defthm fmat-sum-fmat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat12 a b c i j))
	          (entry i j (fmat* a (fmat* b c)))))
  :hints (("Goal" :use ((:instance fmat*-entry (b (fmat* b c)) (p q))))))

;; The matrix (fmat21 a b c i j) similarly relates to (entry i j (fmat* (fmat* a b) c):

(defund fmat21 (a b c i j)
  (flist-scalar-mul-list (col j c)
		         (flist-mul-list (row i a) (transpose-mat b))))

(defthmd fmatp-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (fmat21 a b c i j) p n))
  :hints (("Goal" :in-theory (e/d (fmat21) (flistnp-col))
                  :use (flistnp-row
		        (:instance fmatp-transpose (a b) (m n) (n p))
		        (:instance flistnp-col (a c) (m p) (n q))))))

(local-defthmd fmat21-entry-1
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (nth s (flist-scalar-mul (entry r j c) (nth r (flist-mul-list (row i a) (transpose-mat b)))))))
  :hints (("Goal" :in-theory (enable fmat21 nth-col nth-flist-scalar-mul-list))))

(local-defthmd fmat21-entry-2
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (nth s (flist-scalar-mul (entry r j c) (flist-mul (row i a) (col r b))))))
  :hints (("Goal" :in-theory (enable fmat21-entry-1 nth-flist-mul-list)
                  :use ((:instance fmatp-transpose (a b) (m n) (n p))))))

(local-defthmd fmat21-entry-3
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (f* (entry r j c) (nth s (flist-mul (row i a) (col r b))))))
  :hints (("Goal" :in-theory (e/d (fmat21-entry-2) (flistnp-col flistnp-flist-mul))
                  :use (flistnp-row
		        (:instance nth-flist-scalar-mul-2 (c (entry r j c)) (x (flist-mul (row i a) (col r b))))
		        (:instance flistnp-flist-mul (x (row i a)) (y (col r b)))
			(:instance flistnp-col (a b) (j r) (m n) (n p))))))

(local-defthmd fmat21-entry-4
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (f* (entry r j c) (f* (entry i s a) (entry s r b)))))
  :hints (("Goal" :in-theory (e/d (fmat21-entry-3 nth-col) (flistnp-col))
                  :use (flistnp-row
		        (:instance nth-flist-mul (x (row i a)) (y (col r b)))
			(:instance flistnp-col (a b) (j r) (m n) (n p))))))

(local-defthmd fmat21-entry-5
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (f* (f* (entry i s a) (entry s r b)) (entry r j c))))
  :hints (("Goal" :in-theory (e/d (fmat21-entry-4 fp-entry) (entry))
                  :use ((:instance f*comm (x (f* (entry i s a) (entry s r b))) (y (entry r j c)))))))

(local-defthmd fmat21-entry-6
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (nth s (nth r (fmat21 a b c i j)))
	          (f* (entry i s a) (f* (entry s r b) (entry r j c)))))
  :hints (("Goal" :in-theory (e/d (fmat21-entry-5 fp-entry) (entry))
                  :use ((:instance f*assoc (x (entry i s a)) (y (entry s r b)) (z (entry r j c)))))))

(defthmd fmat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (fmat21 a b c i j))
	          (f* (entry i s a) (f* (entry s r b) (entry r j c)))))
  :hints (("Goal" :in-theory (enable fmat21-entry-6))))


(local-defthm fmat-sum-fmat21-1
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat21 a b c i j))
	          (fdot (col j c)
		        (flist-sum-list (flist-mul-list (row i a) (transpose-mat b))))))
  :hints (("Goal" :in-theory (e/d (fmat21) (flistnp-col))
                  :use (flistnp-row
		        (:instance flistnp-col (a c) (m p) (n q))
		        (:instance fmatp-transpose (a b) (m n) (n p))
		        (:instance fmat-sum-flist-scalar-mul-list (n p) (p n) (x (col j c)) (l (flist-mul-list (row i a) (transpose-mat b))))))))

(local (include-book "std/lists/nthcdr" :dir :system))

(local-defthmd null-nthcdr-len
  (implies (true-listp l)
           (null (nthcdr (len l) l))))

(local-defthmd null-nthcdr-nth-fmat*
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (natp i) (< i m))
           (null (nthcdr p (nth i (fmat* a b)))))
  :hints (("Goal" :use (fmatp-fmat*
                        (:instance flistnp-row (a (fmat* a b)) (n p))
			(:instance null-nthcdr-len (l (nth i (fmat* a b))))))))

(local-defthmd nthcdr-cons
  (implies (and (natp j) (< j (len l)))
           (equal (nthcdr j l)
	          (cons (nth j l) (nthcdr (1+ j) l)))))

(local-defthmd nthcdr-cons-fdot
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (natp i) (< i m) (natp j) (< j p))
           (equal (cons (fdot (nth i a) (col j b))
                        (cdr (nthcdr j (nth i (fmat* a b)))))
                  (nthcdr j (nth i (fmat* a b)))))
  :hints (("Goal" :use (fmatp-fmat* fmat*-entry
                        (:instance flistnp-row (a (fmat* a b)) (n p))
			(:instance nthcdr-cons (l (nth i (fmat* a b))))))))

(local-defthm fmat-sum-fmat21-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (natp i) (< i m) (natp j) (<= j p))
           (equal (flist-sum-list (flist-mul-list (row i a) (transpose-mat-aux b j p)))
	          (nthcdr j (row i (fmat* a b)))))
  :hints (("Goal" :induct (transpose-mat-aux b j p))
          ("Subgoal *1/2" :use (null-nthcdr-nth-fmat*))
          ("Subgoal *1/1" :in-theory (disable flistnp-col)
	                  :use (flistnp-row nthcdr-cons-fdot
			        (:instance flistnp-col (a b) (m n) (n p))))))

(local-defthm fmat-sum-fmat21-3
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (natp i) (< i m))
           (equal (flist-sum-list (flist-mul-list (row i a) (transpose-mat b)))
	          (row i (fmat* a b))))
  :hints (("Goal" :in-theory (enable transpose-mat)
                  :use ((:instance fmat-sum-fmat21-2 (j 0))
		        (:instance flistnp-row (a b) (m n) (n p) (i 0))))))
			        
(local-defthm fmat-sum-fmat21-4
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat21 a b c i j))
	          (fdot (col j c) (row i (fmat* a b)))))
  :hints (("Goal" :use (fmat-sum-fmat21-1 fmat-sum-fmat21-3))))

(defthm fmat-sum-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat21 a b c i j))
	          (entry i j (fmat* (fmat* a b) c))))
  :hints (("Goal" :in-theory (disable flistnp-col)
                  :use (fmatp-fmat*
                        (:instance fmat*-entry (a (fmat* a b)) (b c) (n p) (p q))
                        (:instance fdot-comm (n p) (x (row i (fmat* a b))) (y (col j c)))
			(:instance flistnp-row (a (fmat* a b)) (n p))
			(:instance flistnp-col (a c) (m p) (n q))))))

;; Combine fmat21-entry and fmat12-entry:

(defthmd fmat12-fmat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (fmat21 a b c i j))
	          (entry s r (fmat12 a b c i j))))
  :hints (("Goal" :in-theory (e/d (f*assoc fp-entry fmat21-entry fmat12-entry) (entry)))))

;; Apply transpose-fmat-entry:

(local-defthmd fmat12-transpose-fmat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (fmat21 a b c i j))
	          (entry r s (transpose-mat (fmat12 a b c i j)))))
  :hints (("Goal" :in-theory (e/d (fmat12-fmat21-entry) (entry))
                  :use (fmatp-fmat12))))

(defthmd fmat12-transpose-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (transpose-mat (fmat12 a b c i j))
	          (fmat21 a b c i j)))	          
  :hints (("Goal" :use (fmatp-fmat12 fmatp-fmat21
                        (:instance fmat-entry-diff-lemma (a (fmat21 a b c i j)) (b (transpose-mat (fmat12 a b c i j))) (m p))
                        (:instance fmatp-transpose (a (fmat12 a b c i j)) (m n) (n p))
			(:instance fmat12-transpose-fmat21-entry
			            (r (car (entry-diff (fmat21 a b c i j) (transpose-mat (fmat12 a b c i j)))))
				    (s (cdr (entry-diff (fmat21 a b c i j) (transpose-mat (fmat12 a b c i j))))))))))

;; By sum-fmat-transpose, (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)),
;; and the result rollows:

(local-defthmd fmat-sum-fmat12-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat12 a b c i j))
	          (fmat-sum (fmat21 a b c i j))))          
  :hints (("Goal" :use (fmat12-transpose-fmat21 fmatp-fmat12
                        (:instance sum-fmat-transpose (a (fmat12 a b c i j)) (m n) (n p))))))

(local-defthmd fmat*-assoc-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (entry i j (fmat* a (fmat* b c)))
	          (entry i j (fmat* (fmat* a b) c))))
  :hints (("Goal" :use (fmat12-transpose-fmat21 fmatp-fmat12
                        (:instance sum-fmat-transpose (a (fmat12 a b c i j)) (m n) (n p))))))

(defthmd fmat*-assoc
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q))
           (equal (fmat* a (fmat* b c))
	          (fmat* (fmat* a b) c)))
  :hints (("Goal" :use (fmatp-fmat*
                        (:instance fmatp-fmat* (a b) (b c) (m n) (n p) (p q))
                        (:instance fmatp-fmat* (b (fmat* b c)) (p q))
                        (:instance fmatp-fmat* (a (fmat* a b)) (b c) (n p) (p q))
			(:instance fmat-entry-diff-lemma (a (fmat* a (fmat* b c))) (b (fmat* (fmat* a b) c)) (n q))
			(:instance fmat*-assoc-entry (i (car (entry-diff (fmat* a (fmat* b c)) (fmat* (fmat* a b) c))))
			                             (j (cdr (entry-diff (fmat* a (fmat* b c)) (fmat* (fmat* a b) c)))))))))
