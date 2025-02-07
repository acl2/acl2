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

;;----------------------------------------------------------------------------------------
;; Row Reduction
;;----------------------------------------------------------------------------------------

;; We begin by defining the notion of a row-echelon matrix a of m rows.

;; Find the index of the first nonzero entry of a nonzero row r:

(defun first-nonzero (r)
  (if (consp r)
      (if (= (car r) (f0))
          (1+ (first-nonzero (cdr r)))
	0)	
    ()))

(defthmd first-nonzero-nonzero
  (implies (and (flistnp x n) (not (flist0p x)))
           (let ((i (first-nonzero x)))
	     (and (natp i)
	          (< i n)
		  (fp (nth i x))
		  (not (= (nth i x) (f0)))))))

(defthmd first-nonzero-first
  (implies (and (flistnp x n) (not (flist0p x))
                (natp i) (< i (first-nonzero x)))
           (equal (nth i x) (f0))))

;; Let a be a matrix with m rows and let k <= m.  Starting with row k, find the row
;; with nonzero entry of least index, or return NIL if all rows are 0.

(defun row-with-nonzero-at-least-index (a m k)
  (if (and (natp k) (natp m) (< k m))
      (let ((i (row-with-nonzero-at-least-index a (1- m) k)))
	(if (or (flist0p (nth (1- m) a))
	        (and i (<= (first-nonzero (nth i a)) (first-nonzero (nth (1- m) a)))))
	    i
	  (1- m)))
    ()))

(local-defun check-nil (a k m)
  (if (and (natp k) (natp m) (< k m))
      (and (flist0p (nth (1- m) a))
           (check-nil a k (1- m)))
    t))

(local-defthmd check-nil-flist0p
  (implies (and (natp k) (natp m) (<= k m) (check-nil a k m)
                (natp i) (<= k i) (< i m))
	   (flist0p (nth i a))))

(local-defun check-non-nil (a i k m)
  (if (and (natp k) (natp m) (< k m))
      (and (or (flist0p (nth (1- m) a))
	       (<= (first-nonzero (nth i a))
		   (first-nonzero (nth (1- m) a))))
	   (check-non-nil a i k (1- m)))
    t))

(local-defthmd check-non-nil-bound
  (implies (and (natp k) (natp m) (< k m) (check-non-nil a i k m)
                (natp j) (<= k j) (< j m))
	   (or (flist0p (nth j a))
               (<= (first-nonzero (nth i a))
	           (first-nonzero (nth j a))))))

(local-defthmd check-nil-non-nil
  (implies (and (natp k) (natp m) (<= k m) (check-nil a k m))
	   (check-non-nil a i k m)))

(local-defthm natp-first-nonzero
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp i) (< i m) (not (flist0p (nth i a))))
	   (natp (first-nonzero (nth i a))))
  :hints (("Goal" :use (flistnp-row
                        (:instance first-nonzero-nonzero (x (nth i a))))))
  :rule-classes (:rewrite :type-prescription))

(local-defthmd check-non-nil-<
  (implies (and (fmatp a p q) (natp p) (natp q)
                (natp k) (natp m) (<= k m) (< m p)
		(natp i) (< i p) (natp j) (< j p)
		(check-non-nil a i k m)
		(not (flist0p (nth i a))) (not (flist0p (nth j a)))
		(< (first-nonzero (nth j a)) (first-nonzero (nth i a))))
	   (check-non-nil a j k m)))

(local-defthmd row-with-nonzero-at-least-index-1
  (let ((i (row-with-nonzero-at-least-index a m k)))
    (implies (and (fmatp a p q) (natp p) (natp q)
                  (natp m) (<= m p) (natp k) (< k m))
	     (if (null i)
	         (check-nil a k m)
               (and (natp i) (<= k i) (< i m) (not (flist0p (nth i a)))
	            (check-non-nil a i k m)))))
  :hints (("Subgoal *1/2" :use ((:instance check-nil-non-nil (i (1- m)) (m (1- m)))
                                (:instance check-non-nil-< (m (1- m))
				                           (i (row-with-nonzero-at-least-index a (+ -1 m) k))
							   (j (1- m)))))))

(defthmd row-with-nonzero-at-least-index-nil
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m)
                (null (row-with-nonzero-at-least-index a m k))
		(natp j) (<= k j) (< j m))
	   (flist0p (nth j a)))
  :hints (("Goal" :use ((:instance row-with-nonzero-at-least-index-1 (p m) (q n))
                        (:instance check-nil-flist0p (i j))))))

(defthmd row-with-nonzero-at-least-index-non-nil
  (let ((i (row-with-nonzero-at-least-index a m k)))
    (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) i)
             (and (natp i) (<= k i) (< i m) (not (flist0p (nth i a)))
		  (implies (and (natp j) (<= k j) (< j m))
	                   (or (flist0p (nth j a))
                               (<= (first-nonzero (nth i a))
		                   (first-nonzero (nth j a))))))))
  :hints (("Goal" :use ((:instance check-non-nil-bound (i (row-with-nonzero-at-least-index a m k)))
                        (:instance row-with-nonzero-at-least-index-1 (p m) (q n))))))

;; Let a be a matrix with m rows.  Check that the jth entry of row k of a is (f1) and that
;;  the jth entry of every other row of a is (f0):

(defun column-clear-p (a k j m)
  (if (zp m)
      t
    (and (= (nth j (nth (1- m) a))
	    (if (= (1- m) k) (f1) (f0)))
	 (column-clear-p a k j (1- m)))))

(defthmd column-clear-p-entry
  (implies (and (column-clear-p a k j m)
                (natp m) (natp i) (< i m))
	   (equal (nth j (nth i a))
	          (if (= i k) (f1) (f0)))))

;; If (column-clear-p a k j m) = NIL, then there is a counterexample to column-clear-p-entry:

(local-defun column-clear-p-cex (a k j m)
  (if (zp m)
      ()
    (if (and (not (= (1- m) k))
             (not (= (nth j (nth (1- m) a)) (f0))))
	(1- m)
      (column-clear-p-cex a k j (1- m)))))

(local-defthmd column-clear-p-cex-lemma
  (implies (and (natp m)
                (not (column-clear-p a k j m))
                (= (nth j (nth k a)) (f1)))
	   (let ((i (column-clear-p-cex a k j m)))
             (and (natp i)
	          (< i m)
		  (not (= i k))
		  (not (= (nth j (nth i a)) (f0)))))))	   

;; Check that a is in row-echelon form.
;; The auxiliary function checks that the requirements are satisfied for
;; the first k rows of a:

(defun row-echelon-p-aux (a m k)
  (if (zp k)
      t
    (and (row-echelon-p-aux a m (1- k))
         (let ((i (row-with-nonzero-at-least-index a m (1- k))))
           (or (null i)
               (and (= i (1- k))
                    (column-clear-p a i (first-nonzero (nth i a)) m)))))))

(local-defthm row-echelon-p-aux-<=
  (implies (and (natp k) (natp r) (<= r k) (row-echelon-p-aux a m k))
           (row-echelon-p-aux a m r)))

(local-defthmd row-echelon-p-aux-first-nonzerop-f1
  (let* ((i (row-with-nonzero-at-least-index a m (1- k)))
         (j (first-nonzero (nth i a))))
    (implies (and (fmatp a m n) (natp m) (natp n)
                  (posp k) (<= k m) (row-echelon-p-aux a m k)
		  i)
             (and (= i (1- k))
	          (not (flist0p (nth i a)))
	          (equal (nth j (nth i a)) (f1)))))
  :hints (("Goal" :use ((:instance row-with-nonzero-at-least-index-nil (k (1- k)) (j (1- k)))
                        (:instance row-with-nonzero-at-least-index-non-nil (k (1- k)))
			(:instance column-clear-p-entry (k (1- k)) (i (1- k)) (j (first-nonzero (nth (1- k) a))))
			(:instance flistnp-row (i (1- k)))))))

(local-defthmd row-echelon-p-aux-first-nonzero-min
  (implies (and (fmatp a m n) (natp m) (natp n)
                (posp k) (<= k m) (row-echelon-p-aux a m k)
		(posp q) (<= k q) (< q m))
	   (or (flist0p (nth q a))
               (< (first-nonzero (nth (1- k) a))
                  (first-nonzero (nth q a)))))
  :hints (("Goal" :use ((:instance row-with-nonzero-at-least-index-nil (j q) (k (1- k)))
                        (:instance row-with-nonzero-at-least-index-non-nil (j q) (k (1- k)))
			(:instance column-clear-p-entry (k (1- k)) (i q) (j (first-nonzero (nth (1- k) a))))
			(:instance first-nonzero-nonzero (x (nth q a)))
			(:instance flistnp-row (i q))))))

(defund row-echelon-p (a)
  (row-echelon-p-aux a (len a) (len a)))

;; Next, we define a process that converts a matrix to row-echelon form by applying
;; a sequence of "elementary row operations".

;; 3 types of elementary row operations:

;; (1) Multiply row k by c:

(defund ero1 (a c k)
  (replace-row a k (flist-scalar-mul c (nth k a))))

(defthm fmatp-ero1
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) (fp c))
           (fmatp (ero1 a c k) m n))
  :hints (("Goal" :in-theory (enable ero1))))

(defthmd nth-ero1
  (implies (and (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero1 a c k))
	          (if (= i k)
		      (flist-scalar-mul c (nth k a))
		    (nth i a))))
  :hints (("Goal" :in-theory (enable ero1 nth-replace-row))))

;; (2) Add multiple of row j to row k:

(defund ero2 (a c j k)
  (replace-row a k (flist-add (flist-scalar-mul c (nth j a)) (nth k a))))

(defthm fmatp-ero2
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j m) (natp k) (< k m) (fp c))
           (fmatp (ero2 a c j k) m n))
  :hints (("Goal" :in-theory (enable ero2)
                  :use ((:instance flistnp-row (i k))
			(:instance flistnp-row (i j))))))

(defthmd nth-ero2
  (implies (and (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero2 a c j k))
	          (if (= i k)
		      (flist-add (flist-scalar-mul c (nth j a)) (nth k a))
		    (nth i a))))
  :hints (("Goal" :in-theory (enable ero2 nth-replace-row))))

;; (3) Interchange rows j and k:

(defund ero3 (a j k)
  (replace-row (replace-row a k (nth j a)) j (nth k a)))

(defthm fmatp-ero3
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j m) (natp k) (< k m))
           (fmatp (ero3 a j k) m n))
  :hints (("Goal" :in-theory (enable ero3)
                  :use ((:instance flistnp-row (i k))
			(:instance flistnp-row (i j))))))

(defthmd nth-ero3
  (implies (and (natp j) (< j (len a)) (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero3 a j k))
	          (if (= i k)
		      (nth j a)
		    (if (= i j)
		        (nth k a)
		      (nth i a)))))
  :hints (("Goal" :in-theory (enable ero3 nth-replace-row))))

;; Let r be the kth row of a.  Assume that the leading nonzero entry of r is a 1
;; in column j.  Clear the jth entry of every other row of a by adding the appropriate
;; multiple of r:

(defun clear-column (a k j m)
  (if (zp m)
      a
    (if (= (1- m) k)
	(clear-column a k j (1- m))
      (clear-column (ero2 a (f- (nth j (nth (1- m) a))) k (1- m))
		    k j (1- m)))))

(local-defthmd nth-clear-column-1
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j n) (natp k) (< k m) (natp i) (< i m) (natp m0) (<= m0 m))
           (equal (nth i (clear-column a k j m0))
	          (if (or (= i k) (>= i m0))
		      (nth i a)
		    (flist-add (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)) (nth i a)))))
  :hints (("Goal" :in-theory (enable nth-ero2))
          ("Subgoal *1/3" :use ((:instance fmatp-ero2 (c (F- (NTH J (NTH (+ -1 M0) A)))) (j k) (k i))	  
	                        (:instance fp-entry (i (1- m0)))))))

(local-defthmd nth-clear-column
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j n) (natp k) (< k m) (natp i) (< i m))
           (equal (nth i (clear-column a k j m))
	          (if (= i k)
		      (nth i a)
		    (flist-add (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)) (nth i a)))))
  :hints (("Goal" :use ((:instance nth-clear-column-1 (m0 m))))))

(local-defthm fmatp-clear-column-1
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j n) (natp k) (< k m) (natp m0) (<= m0 m))
           (fmatp (clear-column a k j m0) m n))
  :hints (("Goal" :in-theory (enable nth-clear-column))
          ("Subgoal *1/6" :use ((:instance fp-entry (i (1- m0)))))))

(defthm fmatp-clear-column
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j n) (natp k) (< k m))
           (fmatp (clear-column a k j m) m n))
  :hints (("Goal" :use ((:instance fmatp-clear-column-1 (m0 m))))))

(local-defthmd first-nonzero-flist-add-1
  (implies (and (flistnp x n) (flistnp y n)
                (>= (first-nonzero x) (first-nonzero y)))
           (>= (first-nonzero (flist-add x y))
	       (first-nonzero y))))

(local-defthmd first-nonzero-scalar-mul
  (implies (and (fp c) (flistnp x n))
           (>= (first-nonzero (flist-scalar-mul c x))
	       (first-nonzero x))))

(local-defthmd first-nonzero-clear-column-1
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp i) (< i m) (natp j) (< j n)
		(natp r) (or (flist0p (nth i a)) (> (first-nonzero (nth i a)) r))
		(> (first-nonzero (nth k a)) r))
	   (> (first-nonzero (nth i (clear-column a k j m))) r))
  :hints (("Goal" :in-theory (e/d (nth-clear-column) (flist-add-flist0p))
                  :use (fp-entry flistnp-row
		        (:instance flist-add-flist0p (x (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)))
		                                     (y (nth i a)))
		        (:instance first-nonzero-flist-add-1 (x (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)))
		                                             (y (nth i a)))
			(:instance first-nonzero-flist-add-1 (y (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)))
		                                             (x (nth i a)))
			(:instance first-nonzero-scalar-mul (c (f- (nth j (nth i a)))) (x (nth k a)))
			(:instance flistnp-row (i k))
			(:instance flist-add-comm (x (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)))
		                                  (y (nth i a)))))))

(local-defthmd first-nonzero-flist-add-2
  (implies (and (flistnp x n) (flistnp y n)
                (natp j) (< j n) (> (first-nonzero x) j)) 
           (equal (nth j (flist-add x y))
	          (nth j y))))

(local-defthmd first-nonzero-clear-column-2
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp i) (< i k)
		(natp j) (< j n) (natp r) (< r n)
		(> (first-nonzero (nth k a)) r))
	   (equal (nth r (nth i (clear-column a k j m)))
	          (nth r (nth i a))))
  :hints (("Goal" :in-theory (enable nth-clear-column)
                  :use (flistnp-row
		        (:instance first-nonzero-flist-add-2 (x (flist-scalar-mul (f- (nth j (nth i a))) (nth k a)))
		                                             (y (nth i a))
							     (j r))
			(:instance first-nonzero-scalar-mul (c (f- (nth j (nth i a)))) (x (nth k a)))
			(:instance flistnp-row (i k))))))

(local-defthmd first-nonzero-flist-add-3
  (implies (and (flistnp x n) (flistnp y n)
                (or (flist0p x)
		    (> (first-nonzero x) (first-nonzero y))))
           (equal (first-nonzero (flist-add x y))
	          (first-nonzero y))))

(local-defthmd first-nonzero-clear-column-3
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp j) (< j n)
		(natp i) (< i m)
		(or (flist0p (nth k a))
		    (< (first-nonzero (nth i a)) (first-nonzero (nth k a)))))
	   (equal (first-nonzero (nth i (clear-column a k j m)))
	          (first-nonzero (nth i a))))
  :hints (("Goal" :in-theory (enable nth-clear-column)
                  :use (flistnp-row
		        (:instance flistnp-row (i k))
			(:instance first-nonzero-scalar-mul (c (f- (nth j (nth i a)))) (x (nth k a)))
			(:instance first-nonzero-flist-add-3 (x (FLIST-SCALAR-MUL (F- (NTH J (NTH I A))) (NTH K A)))
		                                             (y (nth i a)))))))

(local-defthmd first-nonzero-clear-column-4
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp j) (< j n)
		(= (nth j (nth k a)) (f1))
		(natp i) (< i m))
	   (equal (nth j (nth i (clear-column a k j m)))
	          (if (= i k) (f1) (f0))))
  :hints (("Goal" :in-theory (e/d (nth-clear-column) (flistnp-flist-scalar-mul))
                  :use (flistnp-row
		        (:instance flistnp-row (i k))
			(:instance flistnp-flist-scalar-mul (c (F- (NTH J (NTH I A)))) (x (NTH K A)))))))

(defthmd column-clear-p-clear-column
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp j) (< j n)
		(= (nth j (nth k a)) (f1)))
	   (column-clear-p (clear-column a k j m) k j m))
  :hints (("Goal" :use ((:instance column-clear-p-cex-lemma (a (clear-column a k j m)))
                        (:instance first-nonzero-clear-column-4 (i k))
                        (:instance first-nonzero-clear-column-4 (i (column-clear-p-cex (clear-column a k j m) k j m)))))))


;; Assume (row-echelon-p-aux a m k), where k < m and that i = (row-with-nonzero-at-least-index a m k)
;; is non-NIL.  Let j = (first-nonzero (nth i a).  The following function performs the next step
;; of the reduction, producing a matrix a' satisfying (row-echelon-p-aux a m (1+ k)):

(defun row-reduce-step (a m k i j)
  (clear-column (ero3 (ero1 a (f/ (nth j (nth i a))) i)
		      i k)
		k j m))

;; The following auxiliary function completes the conversion of a to row-echelon form under the
;; assumption (row-echelon-p-aux a m k), where 0 <= k <= m:

(defun row-reduce-aux (a m k)
  (declare (xargs :measure (nfix (- m k))))
  (let ((i (row-with-nonzero-at-least-index a m k)))
    (if (and (natp k) (natp m) (< k m) i)
        (row-reduce-aux (row-reduce-step a m k i (first-nonzero (nth i a)))
			m (1+ k))
      a)))

;; Convert a to row-echelon form:

(defund row-reduce (a)
  (row-reduce-aux a (len a) 0))

(local-defthmd first-nonzero-flist-scalar-mul-equal-1
  (implies (and (flistnp x n) (fp c) (not (= c (f0)))
                (not (flist0p x)))
	   (and (not (flist0p (flist-scalar-mul c x)))
	        (equal (first-nonzero (flist-scalar-mul c x))
		       (first-nonzero x))))
  :hints (("Subgoal *1/1" :use ((:instance f*f0 (x c) (y (car x)))))))

(local-defthmd first-nonzero-flist-scalar-mul-equal-2
  (implies (and (flistnp x n) (not (flist0p x)))
	   (let ((c (nth (first-nonzero x) x)))
	     (and (fp c)
	          (not (equal c (f0)))
		  (fp (f/ c))
		  (not (equal (f/ c) (f0)))
		  (equal (nth (first-nonzero x) (flist-scalar-mul (f/ c) x))
		         (f1))))))

(local-defthmd first-nonzero-flist-scalar-mul-equal
  (implies (and (flistnp x n) 
                (not (flist0p x)))
	   (let* ((c (f/ (nth (first-nonzero x) x)))
	          (y (flist-scalar-mul c x)))
	     (and (fp c)
	          (not (flist0p y))
	          (equal (first-nonzero y)
		         (first-nonzero x))
	  	  (equal (nth (first-nonzero y) y)
		         (f1)))))
  :hints (("Goal" :use (first-nonzero-flist-scalar-mul-equal-2
                        (:instance first-nonzero-flist-scalar-mul-equal-1 (c (f/ (nth (first-nonzero x) x))))))))

(local-defun i$ (a m k)
  (row-with-nonzero-at-least-index a m k))

(local-defun j$ (a m k)
  (first-nonzero (nth (i$ a m k) a)))

(local-defun c$ (a m k)
  (f/ (nth (j$ a m k) (nth (i$ a m k) a))))
  
(local-defun a1$ (a m k)
  (ero1 a (c$ a m k) (i$ a m k)))

(local-defun a2$ (a m k)
  (ero3 (a1$ a m k) (i$ a m k) k))

(local-defun a3$ (a m k)
  (clear-column (a2$ a m k) k (j$ a m k) m))

(local-defthmd reduce-step-6
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k))
           (and (>= (i$ a m k) k)
	        (< (i$ a m k) m)
		(fp (nth (j$ a m k) (nth (i$ a m k) a)))
		(not (= (nth (j$ a m k) (nth (i$ a m k) a)) (f0)))
	        (fp (f/ (nth (j$ a m k) (nth (i$ a m k) a))))
	        (not (= (f/ (nth (j$ a m k) (nth (i$ a m k) a))) (f0)))
		(fmatp (a1$ a m k) m n)
		(fmatp (a2$ a m k) m n)))
  :hints (("Goal" :use (row-with-nonzero-at-least-index-non-nil
		        (:instance first-nonzero-nonzero (x (nth (i$ a m k) a)))
			(:instance f/f0 (x (nth (j$ a m k) (nth (i$ a m k) a))))
			(:instance flistnp-row (i (i$ a m k)))
			(:instance first-nonzero-flist-scalar-mul-equal (x (nth (i$ a m k) a)))
			(:instance fmatp-ero1 (c (c$ a m k))
					      (k (i$ a m k)))))))

(local-defthmd reduce-step-10
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k))
	   (and (natp (i$ a m k)) (<= k (i$ a m k)) (< (i$ a m k) m) (not (flist0p (nth (i$ a m k) (a1$ a m k))))
	        (equal (first-nonzero (nth (i$ a m k) (a1$ a m k))) (j$ a m k))
		(equal (nth (j$ a m k) (nth (i$ a m k) (a1$ a m k))) (f1))
	        (implies (and (natp j) (<= k j) (< j m))
		         (or (flist0p (nth j (a1$ a m k)))
                             (<= (first-nonzero (nth (i$ a m k) (a1$ a m k)))
		                 (first-nonzero (nth j (a1$ a m k))))))))
  :hints (("Goal" :in-theory (enable nth-ero1)
                  :use (reduce-step-6 row-with-nonzero-at-least-index-non-nil
			(:instance first-nonzero-flist-scalar-mul-equal (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))))))

(local-defthmd reduce-step-11
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k))
	   (and (not (flist0p (nth k (a2$ a m k))))
	        (equal (first-nonzero (nth k (a2$ a m k))) (j$ a m k))
		(equal (nth (j$ a m k) (nth k (a2$ a m k))) (f1))
	        (implies (and (natp j) (< k j) (< j m))
		         (or (flist0p (nth j (a2$ a m k)))
                             (<= (first-nonzero (nth k (a2$ a m k)))
		                 (first-nonzero (nth j (a2$ a m k))))))))
  :hints (("Goal" :in-theory (e/d (nth-ero3) (a1$ fmatp-ero1 fmatp-ero3))
                  :use (reduce-step-6 reduce-step-10
		        (:instance reduce-step-10 (j k))
			(:instance first-nonzero-flist-scalar-mul-equal (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))))))

(local-defthmd reduce-step-1
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k)
                (posp r) (<= r k)
	        (natp q) (<= r q) (< q m))
	   (or (flist0p (nth q a))
	       (> (first-nonzero (nth q a))
	          (first-nonzero (nth (1- r) a)))))
  :hints (("Goal" :use ((:instance row-echelon-p-aux-first-nonzero-min (k r))))))

(local-defthmd reduce-step-2
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
                (posp r) (<= r k))
	   (and (natp (first-nonzero (nth (1- r) a)))
	        (< (first-nonzero (nth (1- r) a)) n)
	        (column-clear-p a (1- r) (first-nonzero (nth (1- r) a)) m)))
  :hints (("Goal" :use (row-with-nonzero-at-least-index-non-nil
                        (:instance row-with-nonzero-at-least-index-non-nil (k (1- r)))
                        (:instance row-with-nonzero-at-least-index-nil (k (1- r)) (j (i$ a m k)))
			(:instance first-nonzero-nonzero (x (nth (1- r) a)))
			(:instance flistnp-row (i (1- r)))
                        (:instance row-echelon-p-aux (k r))))))

(local-defthmd reduce-step-3
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
                (posp r) (<= r k)
		(natp q) (< q m))
           (equal (nth (first-nonzero (nth (1- r) a))
	               (nth q a))
	          (if (= q (1- r)) (f1) (f0))))
  :hints (("Goal" :use (reduce-step-2
			(:instance column-clear-p-entry (i q) (k (1- r)) (j (first-nonzero (nth (1- r) a))))))))

(local-defthmd reduce-step-4
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k)
                (posp r) (<= r k) (row-echelon-p-aux a m k)
	        (natp q) (<= r q) (< q m))
	     (or (flist0p (nth q (a1$ a m k)))
	         (> (first-nonzero (nth q (a1$ a m k)))
	            (first-nonzero (nth (1- r) (a1$ a m k))))))
  :hints (("Goal" :use (reduce-step-1 row-with-nonzero-at-least-index-non-nil
                        (:instance first-nonzero-flist-scalar-mul-equal (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))
			(:instance flistnp-row (i q))
			(:instance nth-ero1 (c (c$ a m k))
					    (k (i$ a m k))
					    (i q))
			(:instance nth-ero1 (c (c$ a m k))
					    (k (i$ a m k))
					    (i (1- r)))))))

(local-defthmd reduce-step-5
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k)
		(posp r) (<= r k) (row-echelon-p-aux a m k))
	   (and (natp (first-nonzero (nth (1- r) (a1$ a m k))))
	        (< (first-nonzero (nth (1- r) (a1$ a m k))) n)
		(implies (and (natp q) (< q r))
	                 (equal (nth (first-nonzero (nth (1- r) (a1$ a m k)))
	                             (nth q (a1$ a m k)))
	                        (if (= q (1- r)) (f1) (f0))))))
  :hints (("Goal" :use (reduce-step-2 reduce-step-3 row-with-nonzero-at-least-index-non-nil
                        (:instance first-nonzero-flist-scalar-mul-equal (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))
			(:instance flistnp-row (i q))
			(:instance nth-ero1 (c (c$ a m k)) (k (i$ a m k)) (i q))
			(:instance nth-ero1 (c (c$ a m k))
					    (k (i$ a m k))
					    (i (1- r)))))))

(local-defthmd reduce-step-7
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k)
		(natp q) (<= r q) (< q m))
	   (or (flist0p (nth q (a2$ a m k)))
	       (> (first-nonzero (nth q (a2$ a m k)))
	          (first-nonzero (nth (1- r) (a2$ a m k))))))
  :hints (("Goal" :in-theory (disable fmatp-ero1)
                  :use (reduce-step-4 reduce-step-6
                        (:instance reduce-step-4 (q k))
                        (:instance reduce-step-4 (q (i$ a m k)))
			(:instance nth-ero3 (a (a1$ a m k)) (i q) (j (i$ a m k)))
			(:instance nth-ero3 (a (a1$ a m k)) (i (1- r)) (j (i$ a m k)))))))

(local-defthmd reduce-step-8
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (and (natp (first-nonzero (nth (1- r) (a2$ a m k))))
	        (< (first-nonzero (nth (1- r) (a2$ a m k))) n)
		(implies (and (natp q) (< q r))
	                 (equal (nth (first-nonzero (nth (1- r) (a2$ a m k)))
	                             (nth q (a2$ a m k)))
	                        (if (= q (1- r)) (f1) (f0))))))
  :hints (("Goal" :in-theory (disable fmatp-ero1)
                  :use (reduce-step-5 reduce-step-6
                        (:instance reduce-step-5 (q k))
                        (:instance reduce-step-5 (q (i$ a m k)))
			(:instance nth-ero3 (a (a1$ a m k)) (i q) (j (i$ a m k)))
			(:instance nth-ero3 (a (a1$ a m k)) (i (1- r)) (j (i$ a m k)))))))

(local-defthmd reduce-step-9
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (equal (first-nonzero (nth (1- r) (a3$ a m k)))
	          (first-nonzero (nth (1- r) (a2$ a m k)))))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-6 row-with-nonzero-at-least-index-non-nil
		        (:instance reduce-step-7 (q k))
		        (:instance first-nonzero-clear-column-3 (a (a2$ a m k)) (i (1- r)) (j (j$ a m k)))
			(:instance flistnp-row (i (i$ a m k)))
			(:instance first-nonzero-nonzero (x (nth (i$ a m k) a)))))))

(local-defthmd reduce-step-12
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k)
		(natp q) (<= r q) (< q m))
	   (or (flist0p (nth q (a3$ a m k)))
	       (> (first-nonzero (nth q (a3$ a m k)))
	          (first-nonzero (nth (1- r) (a3$ a m k))))))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-6 reduce-step-7 reduce-step-8
		        reduce-step-11 row-with-nonzero-at-least-index-non-nil
		        (:instance reduce-step-7 (q k))
		        (:instance first-nonzero-clear-column-3 (a (a2$ a m k)) (i (1- r)) (j (j$ a m k)))
			(:instance first-nonzero-nonzero (x (nth (i$ a m k) a)))
			(:instance first-nonzero-nonzero (x (nth (1- r) (a2$ a m k))))
			(:instance flistnp-row (i (i$ a m k)))
                        (:instance first-nonzero-clear-column-1 (a (a2$ a m k))
			                                        (j (j$ a m k))
			                                        (i q)
								(r (first-nonzero (nth (1- r) (a2$ a m k)))))))))

(local-defthmd reduce-step-13
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k)
		(natp q) (< q r))
	   (equal (nth (first-nonzero (nth (1- r) (a2$ a m k)))
	               (nth q (a3$ a m k)))
		  (nth (first-nonzero (nth (1- r) (a2$ a m k)))
	               (nth q (a2$ a m k)))))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-6 reduce-step-8 reduce-step-11 reduce-step-12		      
		        row-with-nonzero-at-least-index-non-nil
		        (:instance reduce-step-7 (q k))
			(:instance first-nonzero-nonzero (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))
			(:instance flistnp-row (i (1- r)) (a (a2$ a m k)))
                        (:instance first-nonzero-clear-column-2 (a (a2$ a m k))
			                                        (j (j$ a m k))
			                                        (i q)
								(r (first-nonzero (nth (1- r) (a2$ a m k)))))))))

(local-defthmd reduce-step-14
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (and (natp (first-nonzero (nth (1- r) (a3$ a m k))))
	        (< (first-nonzero (nth (1- r) (a3$ a m k))) n)
		(implies (and (natp q) (< q r))
	                 (equal (nth (first-nonzero (nth (1- r) (a3$ a m k)))
	                             (nth q (a3$ a m k)))
	                        (if (= q (1- r)) (f1) (f0))))))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-8 reduce-step-9 reduce-step-13))))

(local-defthmd reduce-step-15
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k))
	   (and (natp (j$ a m k))
	        (< (j$ a m k) n)))
  :hints (("Goal" :use (row-with-nonzero-at-least-index-non-nil
                        (:instance first-nonzero-nonzero (x (nth (i$ a m k) a)))
			(:instance flistnp-row (i (i$ a m k)))))))

(local-defthm fmatp-a3
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k))
	   (fmatp (a3$ a m k) m n))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-6 reduce-step-15))))

(local-defthmd reduce-step-16
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k)
		(natp q) (<= r q) (< q m))
	   (equal (nth (first-nonzero (nth (1- r) (a3$ a m k)))
	               (nth q (a3$ a m k)))
	          (f0)))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (reduce-step-6 reduce-step-12 reduce-step-14
		        (:instance flistnp-row (i q) (a (a3$ a m k)))
			(:instance first-nonzero-first (i (first-nonzero (nth (1- r) (a3$ a m k)))) (x (nth q (a3$ a m k))))))))

(local-defthmd reduce-step-17
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (and (natp (first-nonzero (nth (1- r) (a3$ a m k))))
	        (< (first-nonzero (nth (1- r) (a3$ a m k))) n)
		(implies (and (natp q) (< q m))
	                 (equal (nth (first-nonzero (nth (1- r) (a3$ a m k)))
	                             (nth q (a3$ a m k)))
	                        (if (= q (1- r)) (f1) (f0))))))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (reduce-step-6 reduce-step-12 reduce-step-14 reduce-step-16))))

(local-defthmd reduce-step-18
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (and (natp (first-nonzero (nth (1- r) (a3$ a m k))))
	        (< (first-nonzero (nth (1- r) (a3$ a m k))) n)
		(column-clear-p (a3$ a m k) (1- r) (first-nonzero (nth (1- r) (a3$ a m k))) m)))
  :hints (("Goal" :in-theory (disable a3$)
                  :use ((:instance reduce-step-17 (q (1- r)))
		        (:instance reduce-step-17 (q (column-clear-p-cex (a3$ a m k) (1- r) (first-nonzero (nth (1- r) (a3$ a m k))) m)))
		        (:instance column-clear-p-cex-lemma (a (a3$ a m k)) (k (1- r)) (j (first-nonzero (nth (1- r) (a3$ a m k)))))))))

(local-defthmd reduce-step-19
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (not (flist0p (nth (1- r) (a3$ a m k)))))
  :hints (("Goal" :in-theory (disable a3$)
                  :use ((:instance reduce-step-17 (q (1- r)))
		        (:instance flistnp-row (a (a3$ a m k)) (i (1- r)))
		        (:instance nth-flist0p (x (nth (1- r) (a3$ a m k))) (i (first-nonzero (nth (1- r) (a3$ a m k)))))))))

(local-defthmd reduce-step-20
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k) (row-with-nonzero-at-least-index (a3$ a m k) m (1- r)))
	   (equal (row-with-nonzero-at-least-index (a3$ a m k) m (1- r))
	          (1- r)))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (reduce-step-19
		        (:instance row-with-nonzero-at-least-index-non-nil (a (a3$ a m k)) (k (1- r)) (j (1- r)))
		        (:instance row-with-nonzero-at-least-index-nil (a (a3$ a m k)) (k (1- r)) (j (1- r)))
			(:instance reduce-step-12 (q (row-with-nonzero-at-least-index (a3$ a m k) m (1- r))))
			(:instance reduce-step-17 (q (1- r)))
		        (:instance reduce-step-17 (q (row-with-nonzero-at-least-index (a3$ a m k) m (1- r))))))))

(local-defthmd reduce-step-21
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k) (row-echelon-p-aux (a3$ a m k) m (1- r)))
 	   (row-echelon-p-aux (a3$ a m k) m r))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (reduce-step-18 reduce-step-20))))

(local-defthmd reduce-step-22
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(posp r) (<= r k))
	   (row-echelon-p-aux (a3$ a m k) m r))
  :hints (("Goal" :in-theory (disable a3$))
          ("Subgoal *1/3" :use (reduce-step-21))
          ("Subgoal *1/5" :use (reduce-step-21))))

(local-defthmd reduce-step-23
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k))
	   (row-echelon-p-aux (a3$ a m k) m k))
  :hints (("Goal" :use ((:instance reduce-step-22 (r k))))))

(local-defthmd reduce-step-24
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(natp j) (<= k j) (< j m))
           (or (flist0p (nth j (a3$ a m k)))
               (>= (first-nonzero (nth j (a3$ a m k)))
		   (j$ a  m k))))
  :hints (("Goal" :in-theory (disable natp-first-nonzero a2$)
                  :use (reduce-step-6 reduce-step-11 reduce-step-15 fmatp-a3
		        (:instance natp-first-nonzero (a (a3$ a m k)) (i j))
		        (:instance first-nonzero-clear-column-1 (a (a2$ a m k)) (j (j$ a m k)) (i j) (r (1- (j$ a m k))))))))

(local-defthmd reduce-step-25
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k))
           (column-clear-p (a3$ a m k) k (j$ a m k) m))
  :hints (("Goal" :in-theory (disable natp-first-nonzero a2$)
                  :use (reduce-step-15 reduce-step-6 reduce-step-11
                        (:instance column-clear-p-clear-column (a (a2$ a m k)) (j (j$ a m k)))))))
  
(local-defthmd reduce-step-26
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(natp j) (< k j) (< j m))
           (or (flist0p (nth j (a3$ a m k)))
               (> (first-nonzero (nth j (a3$ a m k)))
		  (j$ a  m k))))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (reduce-step-24 reduce-step-25 fmatp-a3
		        (:instance first-nonzero-nonzero (x (nth j (a3$ a m k))))
			(:instance flistnp-row (a (a3$ a m k)) (i j))
		        (:instance column-clear-p-entry (a (a3$ a m k)) (j (j$ a m k)) (i j))))))

(local-defthmd reduce-step-27
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(row-with-nonzero-at-least-index (a3$ a m k) m k))
           (equal (row-with-nonzero-at-least-index (a3$ a m k) m k)
	          k))
  :hints (("Goal" :in-theory (disable nth-flist0p a3$)
                  :use (fmatp-a3 reduce-step-15 reduce-step-25
		        (:instance nth-flist0p (x (nth k (a3$ a m k))) (i (j$ a m k)))
		        (:instance column-clear-p-entry (a (a3$ a m k)) (i k) (j (j$ a m k)))
		        (:instance row-with-nonzero-at-least-index-non-nil (a (a3$ a m k)) (j k))
		        (:instance first-nonzero-first (x (nth k (a3$ a m k))) (i (j$ a m k)))
			(:instance flistnp-row (i k) (a (a3$ a m k)))
		        (:instance reduce-step-26 (j (row-with-nonzero-at-least-index (a3$ a m k) m k)))))))

(local-defthmd reduce-step-28
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k)
		(row-with-nonzero-at-least-index (a3$ a m k) m k))
           (equal (first-nonzero (nth k (a3$ a m k)))
	          (j$ a m k)))
  :hints (("Goal" :in-theory (disable nth-flist0p a3$)
                  :use (fmatp-a3 reduce-step-15 reduce-step-25
		        (:instance reduce-step-24 (j k))
		        (:instance nth-flist0p (x (nth k (a3$ a m k))) (i (j$ a m k)))
		        (:instance column-clear-p-entry (a (a3$ a m k)) (i k) (j (j$ a m k)))
		        (:instance row-with-nonzero-at-least-index-non-nil (a (a3$ a m k)) (j k))
		        (:instance first-nonzero-first (x (nth k (a3$ a m k))) (i (j$ a m k)))
			(:instance flistnp-row (i k) (a (a3$ a m k)))
		        (:instance reduce-step-26 (j (row-with-nonzero-at-least-index (a3$ a m k) m k)))))))

(local-defthmd reduce-step-29
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k) (i$ a m k))
           (row-echelon-p-aux (a3$ a m k) m (1+ k)))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (fmatp-a3 reduce-step-23 reduce-step-25 reduce-step-27 reduce-step-28))))

(local-defthmd row-echelon-p-aux-row-reduce-step
  (implies (and (fmatp a m n) (natp m) (natp n) 
                (natp k) (< k m) (row-echelon-p-aux a m k)
	        (i$ a m k))		
	   (row-echelon-p-aux (row-reduce-step a m k (i$ a m k) (j$ a m k)) m (1+ k)))
  :hints (("Goal" :use (reduce-step-29))))

(local-defthmd fmatp-row-reduce-step
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (i$ a m k))
	   (fmatp (row-reduce-step a m k (i$ a m k) (j$ a m k)) m n))
  :hints (("Goal" :use (fmatp-a3))))

(in-theory (disable row-reduce-step))

(defthmd fmatp-row-reduce-aux
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (<= k m))
	   (fmatp (row-reduce-aux a m k) m n))
  :hints (("Goal" :induct (row-reduce-aux a m k))
          ("Subgoal *1/1" :use (fmatp-row-reduce-step))))

(local-defthmd row-with-nonzero-at-least-index->
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (<= k m) (row-echelon-p-aux a m k)
		(not (row-with-nonzero-at-least-index a m k))
		(natp j) (<= k j) (< j m))
	   (not (row-with-nonzero-at-least-index a m j)))
  :hints (("Goal" :use ((:instance row-with-nonzero-at-least-index-nil (j (row-with-nonzero-at-least-index a m j)))
                        (:instance row-with-nonzero-at-least-index-non-nil (k j))))))

(local-defun row-echelon-p-induct (j k)
  (if (and (natp j) (natp k) (< k j))
      (list (row-echelon-p-induct (1- j) k))
    (list j k)))

(local-defthmd row-echelon-p-induction
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (<= k m) (row-echelon-p-aux a m k)
		(not (row-with-nonzero-at-least-index a m k))
		(natp j) (<= k j) (<= j m))
	   (row-echelon-p-aux a m j))
  :hints (("Goal" :induct (row-echelon-p-induct j k))
          ("Subgoal *1/1" :use ((:instance row-with-nonzero-at-least-index-> (j (1- j)))))))

(defthmd row-echelon-p-aux-row-reduce-aux
  (implies (and (natp m) (natp n) (fmatp a m n)
		(natp k) (<= k m) (row-echelon-p-aux a m k))
	   (row-echelon-p-aux (row-reduce-aux a m k) m m))
  :hints (("Goal" :induct (row-reduce-aux a m k))
          ("Subgoal *1/1" :use (fmatp-row-reduce-step row-echelon-p-aux-row-reduce-step))
          ("Subgoal *1/2" :use ((:instance row-echelon-p-induction (j m))))))

(defthmd row-echelon-p-row-reduce
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (row-echelon-p (row-reduce a)))
  :hints (("Goal" :in-theory (enable row-echelon-p row-reduce)
                  :use ((:instance row-echelon-p-aux-row-reduce-aux (k 0))
                        (:instance fmatp-row-reduce-aux (k 0))))))

(defthmd fmatp-row-reduce
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (fmatp (row-reduce a) m n))
  :hints (("Goal" :in-theory (enable row-reduce)
                  :use ((:instance fmatp-row-reduce-aux (k 0))))))


;;-------------------------------------------------------------------------------------------------------

(local-defthmd row-echelon-p-row-echelon-p-aux
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a) (natp k) (<= k m))
            (row-echelon-p-aux a m k))
  :hints (("Goal" :in-theory (enable row-echelon-p)
                  :use (fmatp-row-reduce
                        (:instance row-echelon-p-aux-<= (k m) (r k))))))

(local-defthmd row-echelon-p-aux-first-nonzero
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) (row-echelon-p-aux a m (1+ k)))
           (if (i$ a m k)
	       (and (not (flist0p (nth k a)))
	            (column-clear-p a k (j$ a m k) m)
	            (implies (and (natp i) (> i k) (< i m))
		             (or (flist0p (nth i a))
			         (> (first-nonzero (nth i a))
				    (j$ a m k)))))
	     (implies (and (natp i) (<= k i) (< i m))
	              (flist0p (nth i a)))))
  :hints (("Goal" :use (row-with-nonzero-at-least-index-non-nil
                        (:instance row-echelon-p-aux-first-nonzero-min (k (1+ k)) (q i))
			(:instance row-with-nonzero-at-least-index-nil (j i))))))

(defthmd flist0p-row
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (flist0p (nth k a))
                (natp i) (< k i) (< i m))
           (flist0p (nth i a)))
  :hints (("Goal" :use (row-echelon-p-aux-first-nonzero
                        (:instance row-echelon-p-row-echelon-p-aux (k (1+ k)))))))

(defthmd first-nonzero-row-bound
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (not (flist0p (nth k a))))
	   (and (natp (first-nonzero (nth k a)))
	        (< (first-nonzero (nth k a)) n)))
  :hints (("Goal" :use ((:instance first-nonzero-nonzero (x (nth k a)))
                        (:instance flistnp-row (i k))))))

(defthmd not-flist0p-row
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (not (flist0p (nth k a)))
                (natp i) (< k i) (< i m) (not (flist0p (nth i a))))
           (< (first-nonzero (nth k a))
	      (first-nonzero (nth i a))))
  :hints (("Goal" :use (row-echelon-p-aux-first-nonzero
                        (:instance row-echelon-p-row-echelon-p-aux (k (1+ k)))))))

(defthmd nth-first-nonzero
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (not (flist0p (nth k a)))
                (natp i) (< i m))
	   (equal (nth (first-nonzero (nth k a))
	               (nth i a))
		  (fdelta i k)))
  :hints (("Goal" :use (row-echelon-p-aux-first-nonzero
                        (:instance row-echelon-p-aux-first-nonzero (i k))
                        (:instance row-echelon-p-row-echelon-p-aux (k (1+ k)))
                        (:instance column-clear-p-entry (j (j$ a m k)))))))


;;-------------------------------------------------------------------------------------------------------

(local-defthm rrrr-1
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (i$ a m k) k))
  :hints (("Goal" :use ((:instance row-echelon-p-row-echelon-p-aux (k (1+ k)))))))

(local-defthm rrrr-2
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (not (flist0p (nth k a))))
  :hints (("Goal" :use (row-echelon-p-aux-first-nonzero
                        (:instance row-echelon-p-row-echelon-p-aux (k (1+ k)))))))

(local-defthm rrrr-3
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (c$ a m k) (f1)))
  :hints (("Goal" :use ((:instance nth-first-nonzero (i k))))))

(local-defthm flist-scalar-mul-f1
  (implies (flistnp x n)
           (equal (flist-scalar-mul (f1) x)
	          x)))
		  
(local-defthm rrrr-4
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k)
		(natp i) (< i m))
	   (equal (nth i (a1$ a m k))
	          (nth i a)))
  :hints (("Goal" :in-theory (enable nth-ero1)
                  :use (flistnp-row))))

(local-defthm rrrr-5
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (a1$ a m k)
	          a))
  :hints (("Goal" :in-theory (disable a1$)
                  :use (reduce-step-6
                        (:instance fmat-entry-diff-lemma (b (a1$ a m k)))))))

(local-defthm rrrr-6
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k)
		(natp i) (< i m))
	   (equal (nth i (a2$ a m k))
	          (nth i a)))
  :hints (("Goal" :in-theory (enable nth-ero3)
                  :use (flistnp-row))))

(local-defthm rrrr-7
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (a2$ a m k)
	          a))
  :hints (("Goal" :in-theory (disable a2$)
                  :use (reduce-step-6
                        (:instance fmat-entry-diff-lemma (b (a2$ a m k)))))))

(local-defthm rrrr-8
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k)
		(natp i) (< i m))
	   (equal (nth i (a3$ a m k))
	          (nth i a)))
  :hints (("Goal" :in-theory (enable nth-first-nonzero nth-clear-column)
                  :use (first-nonzero-row-bound flistnp-row
		        (:instance flistnp-row (i k))))))

(local-defthmd rrrr-9
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (a3$ a m k)
	          a))
  :hints (("Goal" :in-theory (disable a3$)
                  :use (fmatp-a3
                        (:instance fmat-entry-diff-lemma (b (a3$ a m k)))))))

(local-defthm rrrr-10
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (row-reduce-step a m k (i$ a m k) (j$ a m k))
	          (a3$ a m k)))
  :hints (("Goal" :use (rrrr-1) :in-theory (e/d (row-reduce-step) (rrrr-1 rrrr-3 rrrr-5 rrrr-7)))))

(local-defthm rrrr-11
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k m) (i$ a m k))
	   (equal (row-reduce-step a m k (i$ a m k) (j$ a m k))
	          a))
  :hints (("Goal" :use (rrrr-9 rrrr-10))))

(local-defun rrrr-induct (m k)
  (declare (xargs :measure (nfix (- m k))))
  (if (and (natp m) (natp k) (< k m))
      (list (rrrr-induct m (1+ k)))
    ()))

(local-defthmd rrrr-12
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (<= k m))
           (equal (row-reduce-aux a m k)
	          a))
  :hints (("Goal" :induct (rrrr-induct m k))
          ("subgoal *1/1" :expand ((row-reduce-aux a m k))
	                  :use (rrrr-11))))

;; If a is already in row-echelon form, then (row-reduce a) = a:

(defthmd row-reduce-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp a m n) (row-echelon-p a))
	   (equal (row-reduce a) a))
  :hints (("Goal" :in-theory (enable row-reduce)
                  :use ((:instance rrrr-12 (k 0))))))



;;-------------------------------------------------------------------------------------------------------

;; The number of nonzero rows of a:

(defun num-nonzero-rows (a)
  (if (consp a)
      (if (flist0p (car a))
          0
	(1+ (num-nonzero-rows (cdr a))))
    0))

(local-defthmd num-nonzero-rows<=len
  (<= (num-nonzero-rows a)
      (len a)))

(defthmd num-nonzero-rows<=m
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (num-nonzero-rows a)
               m))
  :hints (("Goal" :use (num-nonzero-rows<=len))))

(local-defthmd num-nonzero-rows-nonzero-1
  (implies (and (natp i) (< i (num-nonzero-rows a)))
	   (not (flist0p (nth i a)))))

(local-defthmd num-nonzero-rows-nonzero-2
  (implies (and (natp i) (<= (num-nonzero-rows a) (len a)))
	   (flist0p (nth (num-nonzero-rows a) a))))

(defthmd num-nonzero-rows-nonzero
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp i) (< i m))
	   (iff (flist0p (nth i a))
	        (>= i (num-nonzero-rows a))))
  :hints (("Goal" :use (num-nonzero-rows-nonzero-1 num-nonzero-rows-nonzero-2 num-nonzero-rows<=m
                        (:instance flist0p-row (k (num-nonzero-rows a)))))))

;; The row rank of a is the number of nonzero rows of (row-reduce a):

(defun row-rank (a)
  (num-nonzero-rows (row-reduce a)))

(defthmd row-rank-row-reduce
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (row-rank (row-reduce a))
		  (row-rank a)))
  :hints (("Goal" :in-theory (enable row-rank)
	   :use (row-echelon-p-row-reduce fmatp-row-reduce
					  (:instance row-reduce-row-echelon-p (a (row-reduce a)))))))

;; Obviously, the number of nonzero rows of an mxn matrix cannot exceed m:

(defthmd row-rank<=m
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (row-rank a)
               m))
  :hints (("Goal" :use (fmatp-row-reduce row-echelon-p-row-reduce
                        (:instance num-nonzero-rows<=m (a (row-reduce a)))))))

;; We shall also show that the row rank of an mxn matrix cannot exceed n.
;; To this end, we examine the list of indices of the leading 1s of the 
;; nonzero rows of a row-echelon matrix a:

(defun lead-inds (a)
  (if (and (consp a) (not (flist0p (car a))))
      (cons (first-nonzero (car a))
	    (lead-inds (cdr a)))
    ()))

(defthmd len-lead-inds-num-nonzero-rows
  (equal (len (lead-inds a))
         (num-nonzero-rows a)))

(defthmd len-lead-inds-bound
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (len (lead-inds a))
               m))
  :hints (("Goal" :use (len-lead-inds-num-nonzero-rows num-nonzero-rows<=m))))

(defthmd nth-lead-inds
  (implies (and (natp k) (< k (len (lead-inds a))))
           (equal (nth k (lead-inds a))
	          (first-nonzero (nth k a)))))

;; (lead-inds a) is an increasing list:

(defthmd lead-inds-inc
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp i) (natp j) (< i j) (< j (len (lead-inds a))))
           (< (nth i (lead-inds a))
	      (nth j (lead-inds a))))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (num-nonzero-rows-nonzero num-nonzero-rows<=m
                        (:instance num-nonzero-rows-nonzero (i j))
			(:instance nth-lead-inds (k i))
                        (:instance nth-lead-inds (k j))
			(:instance not-flist0p-row (k i) (i j))))))

;; By dcex-lemma, it follows that (lead-inds a)) is a dlist:

(defthm dlistp-lead-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (dlistp (lead-inds a)))
  :hints (("Goal" :use ((:instance dcex-lemma (l (lead-inds a)))
                        (:instance lead-inds-inc (i (dcex1 (lead-inds a)))
			                                 (j (dcex2 (lead-inds a))))))))

(include-book "projects/groups/groups" :dir :system)

;; (lead-inds a) is a sublist of (ninit n):

(local-defthmd lead-inds-ninit-1
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (sublistp l a))
           (sublistp (lead-inds l)
	             (ninit n)))
  :hints (("Subgoal *1/2" :in-theory (enable member-ninit)  
                          :use ((:instance first-nonzero-row-bound (k (index (car l) a)))
			        (:instance ind<len (x (car l)) (l a))))))

(defthmd sublistp-lead-inds-ninit
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (sublistp (lead-inds a)
	             (ninit n)))
  :hints (("Goal" :use ((:instance lead-inds-ninit-1 (l a))))))

;; Consequently, by sublistp-<=-len, (len (lead-inds l)) <= n:

(defthmd num-nonzero-rows<=n
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (<= (num-nonzero-rows a)
               n))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (sublistp-lead-inds-ninit dlistp-lead-inds
                        (:instance sublistp-<=-len (l (lead-inds a)) (m (ninit n)))))))

(defthmd row-rank<=n
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (row-rank a)
               n))
  :hints (("Goal" :use (fmatp-row-reduce row-echelon-p-row-reduce
                        (:instance num-nonzero-rows<=n (a (row-reduce a)))))))

;; If (num-nonzero-rows a) = n, then (lead-inds a) = (ninit n):

(local-defthmd permp-lead-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (= (num-nonzero-rows a) n))
	   (permp (lead-inds a) (ninit n)))
  :hints (("Goal" :in-theory (enable sublistp-lead-inds-ninit len-lead-inds-num-nonzero-rows)
                  :use ((:instance permp-eq-len (l (lead-inds a)) (m (ninit n)))))))

(local-defun nth-lead-inds-1-induct (i a)
  (declare (xargs :measure (nfix (- (len (lead-inds a)) i))))
  (let ((j (nth i (lead-inds a))))
    (if (and (natp i) (< i j) (< j (len (lead-inds a))))
        (list (nth-lead-inds-1-induct j a))
      (list i a))))

(local-defthmd nth-lead-inds-1
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (permp (lead-inds a) (ninit n))
                (natp i) (< i (len (lead-inds a))))
	   (<= (nth i (lead-inds a))
	       i))
  :hints (("Goal" :induct (nth-lead-inds-1-induct i a)) 
          ("Subgoal *1/2" :in-theory (e/d (permp member-ninit) (len member-sublist))
	                  :use ((:instance eq-len-permp (l (lead-inds a)) (m (ninit n)))
			        (:instance member-sublist (x (nth i (lead-inds a)))
	                                                  (l (lead-inds a))
							  (m (ninit n)))))
	  ("Subgoal *1/1" :in-theory (e/d (permp member-ninit) (len member-sublist))
	                  :use ((:instance member-sublist (x (nth i (lead-inds a)))
	                                                  (l (lead-inds a))
							  (m (ninit n)))
				(:instance lead-inds-inc (j (nth i (lead-inds a))))))))

(local-defun nth-lead-inds-val-induct (i a)
  (let ((j (nth i (lead-inds a))))
    (if (and (natp i) (natp j) (< j i))
        (list (nth-lead-inds-val-induct j a))
      (list i))))

(local-defthmd nth-lead-inds-val
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (permp (lead-inds a) (ninit n))
                (natp i) (< i (len (lead-inds a))))
	   (equal (nth i (lead-inds a))
	          i))
  :hints (("Goal" :induct (nth-lead-inds-val-induct i a))
          ("Subgoal *1/2" :in-theory (e/d (member-ninit permp) (member-sublist))
	                  :use (nth-lead-inds-1
			        (:instance member-sublist (x (nth i (lead-inds a)))
	                                                  (l (lead-inds a))
							  (m (ninit n)))))))

(defthmd lead-inds-ninit
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (= (num-nonzero-rows a) n))
	   (equal (lead-inds a) (ninit n)))
  :hints (("Goal" :use (permp-lead-inds len-lead-inds-num-nonzero-rows
                        (:instance nth-diff-diff (x (lead-inds a)) (y (ninit n)))
                        (:instance nth-lead-inds-val (i (nth-diff (lead-inds a) (ninit n))))))))


;----------------------------------------------------------------------------------------
;; Row Reduction as Matrix Multiplcation
;;----------------------------------------------------------------------------------------

;; a row operation on a matrix of m rows is encoded as a list, the first member of which
;; indicates the operation type:

(defund row-op-p (op m)
  (and (true-listp op)
       (case (car op)
	 (1 (and (= (len op) 3)
		 (fp (cadr op))
		 (not (= (cadr op) (f0)))
		 (natp (caddr op))
		 (< (caddr op) m)))
	 (2 (and (= (len op) 4)
		 (fp (cadr op))
		 (natp (caddr op))
		 (< (caddr op) m)
		 (natp (cadddr op))
		 (< (cadddr op) m)
		 (not (= (caddr op) (cadddr op)))))
	 (3 (and (= (len op) 3)
		 (natp (cadr op))
		 (< (cadr op) m)
		 (natp (caddr op))
		 (< (caddr op) m))))))	 

;; apply-row-op applies an encoded op to a matrix:

(defund apply-row-op (op a)
  (case (car op)
    (1 (ero1 a (cadr op) (caddr op)))             ;(apply-row-op (list 1 c k) a) = (ero1 a c k)
    (2 (ero2 a (cadr op) (caddr op) (cadddr op))) ;(apply-row-op (list 2 c j k) a) = (ero2 a c j k)
    (3 (ero3 a (cadr op) (caddr op)))))           ;(apply-row-op (list 3 j k) a) = (ero3 a j k)

(defthm fmatp-apply-row-op
  (implies (and (fmatp a m n) (natp m) (natp n) (row-op-p op m))
           (fmatp (apply-row-op op a) m n))	   
  :hints (("Goal" :in-theory (enable apply-row-op row-op-p))))

;; Apply a list of encoded row operations from left to right:

(defun row-ops-p (ops m)
  (if (consp ops)
      (and (row-op-p (car ops) m)
	   (row-ops-p (cdr ops) m))
    (null ops)))

(defun apply-row-ops (ops a)
  (if (consp ops)
      (apply-row-ops (cdr ops) (apply-row-op (car ops) a))
    a))

(defthm fmatp-apply-row-ops
  (implies (and (fmatp a m n) (natp m) (natp n) (row-ops-p ops m))
           (fmatp (apply-row-ops ops a) m n)))

(defthmd append-row-ops
  (implies (and (row-ops-p ops1 m) (row-ops-p ops2 m))
           (and (row-ops-p (append ops1 ops2) m)
	        (equal (apply-row-ops (append ops1 ops2) a)
		       (apply-row-ops ops2 (apply-row-ops ops1 a))))))

;; The list of row operations applied by clear-column:

(defun clear-column-ops (a k j m)
  (if (zp m)
      ()
    (if (= k (1- m))
        (clear-column-ops a k j (1- m))
      (cons (list 2 (f- (nth j (nth (1- m) a))) k (1- m))
	    (clear-column-ops (ero2 a (f- (nth j (nth (1- m) a))) k (1- m)) k j (1- m))))))

(local-defthmd row-ops-p-clear-column-ops-1
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n) (natp m0) (<= m0 m))
	   (row-ops-p (clear-column-ops a k j m0) m))	   
  :hints (("Subgoal *1/10" :in-theory (enable row-op-p) :use ((:instance fp-entry (i (1- m0)))))
          ("Subgoal *1/6" :in-theory (enable row-op-p) :use ((:instance fp-entry (i (1- m0)))))))

(defthm row-ops-p-clear-column-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n))
	   (row-ops-p (clear-column-ops a k j m) m))	   
  :hints (("Goal" :use ((:instance row-ops-p-clear-column-ops-1 (m0 m))))))

(local-defun apply-clear-column-ops-1-induct (a j k m0)
  (if (zp m0)
      (list a j k m0)
    (cons (list (apply-clear-column-ops-1-induct (ero2 a (f- (nth j (nth (1- m0) a))) k (1- m0)) j k (1- m0)))
          (list (apply-clear-column-ops-1-induct a j k (1- m0))))))

(local-defthmd apply-clear-column-ops-1
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n)
                (natp m0) (<= m0 m) (natp i) (< i m) (<= m0 i))
	   (equal (nth i (apply-row-ops (clear-column-ops a k j m0) a))
	          (nth i (clear-column a k j m0))))
  :hints (("Goal" :induct (apply-clear-column-ops-1-induct a j k m0))
          ("Subgoal *1/2" :use ((:instance fp-entry (i (1- m0))))
	                  :in-theory (enable apply-row-op)
	                  :expand ((clear-column-ops a k j m0) (clear-column a k j m0)))))

(local-defthmd apply-clear-column-ops-2
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n)
                (natp m0) (<= m0 m) (natp i) (< i m0))
	   (equal (nth i (apply-row-ops (clear-column-ops a k j m0) a))
	          (nth i (clear-column a k j m0))))
  :hints (("Goal" :induct (apply-clear-column-ops-1-induct a j k m0))
          ("Subgoal *1/2" :use (fp-entry
	                        (:instance fp-entry (i (1- m0)))
				(:instance apply-clear-column-ops-1 (m0 i))
				(:instance apply-clear-column-ops-1 (m0 i) (a (ero2 a (f- (nth j (nth i a))) k i))))
	                  :in-theory (enable apply-row-op)
	                  :expand ((clear-column-ops a k j m0) (clear-column a k j m0)))))

(local-defthmd apply-clear-column-ops-3
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n)
                (natp i) (< i m))
	   (equal (nth i (apply-row-ops (clear-column-ops a k j m) a))
	          (nth i (clear-column a k j m))))
  :hints (("Goal" :use ((:instance apply-clear-column-ops-2 (m0 m))))))

(defthmd apply-clear-column-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n))
           (equal (apply-row-ops (clear-column-ops a k j m) a)
	          (clear-column a k j m)))
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (a (apply-row-ops (clear-column-ops a k j m) a))
                                                    (b (clear-column a k j m))))
		  :in-theory (enable apply-clear-column-ops-3))))

;; The list of row operations applied by row-reduce-step:

(defund row-reduce-step-ops (a m k i j)
  (cons (list 1 (f/ (nth j (nth i a))) i)
        (cons (list 3 i k)
	      (clear-column-ops (ero3 (ero1 a (f/ (nth j (nth i a))) i)
				      i k)
			        k j m))))

(defthmd row-ops-p-row-reduce-step-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n) (natp i) (< i m)
		(not (= (entry i j a) (f0))))
           (row-ops-p (row-reduce-step-ops a m k i j) m))
  :hints (("Goal" :in-theory (e/d (row-op-p row-reduce-step-ops) (row-ops-p-clear-column-ops))
                  :use (fp-entry
		        (:instance row-ops-p-clear-column-ops (a (ero3 (ero1 a (f/ (nth j (nth i a))) i) i k)))))))

(defthmd apply-row-reduce-step-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n) (natp i) (< i m)
		(not (= (entry i j a) (f0))))
           (equal (apply-row-ops (row-reduce-step-ops a m k i j) a)
                  (row-reduce-step a m k i j)))
  :hints (("Goal" :in-theory (enable row-reduce-step row-reduce-step-ops apply-row-op)
                  :use (fp-entry
		        (:instance apply-clear-column-ops (a (ERO3 (ERO1 A (F/ (NTH J (NTH I A))) I) I K)))))))

;; The list of row operations applied by row-reduce-aux:

(defun row-reduce-aux-ops (a m k)
  (declare (xargs :measure (nfix (- m k))))
  (let* ((i (row-with-nonzero-at-least-index a m k))
	 (j (and i (first-nonzero (nth i a)))))
    (if (and (natp k) (natp m) (< k m) i)
        (append (row-reduce-step-ops a m k i j)
	        (row-reduce-aux-ops (row-reduce-step a m k i j) m (1+ k)))                
      ())))

(local-defthmd apply-row-reduce-aux-ops-1
  (let* ((i (row-with-nonzero-at-least-index a m k))
	 (j (first-nonzero (nth i a))))
    (implies (and (fmatp a m n) (natp m) (natp n)
                  (natp k) (< k m) i)
	     (and (natp i) (< i m) (natp j) (< j n)
	          (not (equal (entry i j a) (f0))))))
  :hints (("Goal" :use (row-with-nonzero-at-least-index-non-nil
                        (:instance flistnp-row (i (row-with-nonzero-at-least-index a m k)))
                        (:instance first-nonzero-nonzero (x (nth (row-with-nonzero-at-least-index a m k) a)))))))
		
(in-theory (disable fmatp))

(defthmd row-ops-p-row-reduce-aux-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m))
	   (row-ops-p (row-reduce-aux-ops a m k) m))
  :hints (("Subgoal *1/1" :in-theory (enable apply-row-reduce-step-ops append-row-ops)
	                  :use (fmatp-row-reduce-step apply-row-reduce-aux-ops-1))
	  ("Subgoal *1/5" :use (apply-row-reduce-aux-ops-1
			        (:instance row-ops-p-row-reduce-step-ops (i (i$ a m k)) (j (j$ a m k)))))
	  ("Subgoal *1/4" :expand ((row-reduce-aux-ops a (+ 1 k) k))
	                  :use (apply-row-reduce-aux-ops-1
			        (:instance row-ops-p-row-reduce-step-ops (i (i$ a m k)) (j (j$ a m k)))))))

(defthmd apply-row-reduce-aux-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k))
           (equal (apply-row-ops (row-reduce-aux-ops a m k) a)
                  (row-reduce-aux a m k)))
  :hints (("Goal" :induct (row-reduce-aux-ops a m k))  
          ("Subgoal *1/1" :in-theory (enable apply-row-reduce-step-ops append-row-ops)
	                  :use (apply-row-reduce-aux-ops-1 fmatp-row-reduce-step row-echelon-p-aux-row-reduce-step
			        (:instance row-ops-p-row-reduce-aux-ops (a (row-reduce-step a m k (i$ a m k) (j$ a m k))) (k (1+ k)))
			        (:instance row-ops-p-row-reduce-step-ops (i (i$ a m k)) (j (j$ a m k)))))))

;; The list of row operations applied by row-reduce:

(defund row-reduce-ops (a)
  (row-reduce-aux-ops a (len a) 0))

(defthmd row-ops-p-row-reduce-ops
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (row-ops-p (row-reduce-ops a) m))
  :hints (("Goal" :in-theory (enable row-reduce-ops)
                  :use ((:instance row-ops-p-row-reduce-aux-ops (k 0)))))) 

(defthmd apply-row-reduce-ops
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (equal (apply-row-ops (row-reduce-ops a) a)
		  (row-reduce a)))
  :hints (("Goal" :in-theory (enable row-reduce row-reduce-ops)
                  :use ((:instance apply-row-reduce-aux-ops (k 0))))))

;; The nxn elementary matrix corresponding to a row operation:

(defund elem-mat (op m)
  (apply-row-op op (id-fmat m)))

(defthm fmatp-elem-mat
  (implies (and (row-op-p op m) (natp m))
           (fmatp (elem-mat op m) m m))
  :hints (("Goal" :in-theory (enable apply-row-op elem-mat row-op-p))))

(local-defthmd elem-mat-row-op-1
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n) (= (car op) 1))
	   (equal (entry i j (fmat* (elem-mat op m) a))
		  (entry i j (apply-row-op op a))))
  :hints (("Goal" :in-theory (e/d (nth-ero1 row-op-p apply-row-op nth-fmat* elem-mat fdot-flist-scalar-mul nth-col)
                                  (flistnp-funit fmatp-id-fmat flistnp-col))
                  :use (fmatp-elem-mat fmatp-transpose flistnp-col
		        (:instance flistnp-funit (j (caddr op)) (n m))
			(:instance flistnp-row (i (caddr op)))
		        (:instance fmatp-id-fmat (n m))))))

(local-defthmd elem-mat-row-op-2
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n) (= (car op) 2))
	   (equal (entry i j (fmat* (elem-mat op m) a))
		  (entry i j (apply-row-op op a))))
  :hints (("Goal" :in-theory (e/d (nth-ero2 row-op-p apply-row-op nth-fmat* elem-mat fdot-flist-scalar-mul nth-col)
                                  (flistnp-funit fmatp-id-fmat flistnp-col nth-flist-add ))
                  :use (fmatp-elem-mat fmatp-transpose flistnp-col
		        (:instance flistnp-funit (j (caddr op)) (n m))
		        (:instance flistnp-funit (j (cadddr op)) (n m))
			(:instance flistnp-row (i (caddr op)))
			(:instance flistnp-row (i (cadddr op)))
			(:instance fdot-flist-add (n m)
			                          (x (FLIST-SCALAR-MUL (CADR OP) (FUNIT (CADDR OP) M)))
			                          (y (FUNIT (CADDDR OP) M))
						  (z (col j a)))
			(:instance nth-flist-add (i j) (x (FLIST-SCALAR-MUL (CADR OP) (NTH (CADDR OP) A))) (y (nth (cadddr op) a)))
		        (:instance fmatp-id-fmat (n m))))))

(local-defthmd elem-mat-row-op-3
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n) (= (car op) 3))
	   (equal (entry i j (fmat* (elem-mat op m) a))
		  (entry i j (apply-row-op op a))))
  :hints (("Goal" :in-theory (e/d (nth-ero3 row-op-p apply-row-op nth-fmat* elem-mat fdot-flist-scalar-mul nth-col)
                                  (flistnp-funit fmatp-id-fmat flistnp-col))
                  :use (fmatp-elem-mat fmatp-transpose flistnp-col
		        (:instance flistnp-funit (j (caddr op)) (n m))
			(:instance flistnp-row (i (caddr op)))
		        (:instance fmatp-id-fmat (n m))))))

(local-defthmd elem-mat-row-op-4
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n) (natp i) (< i m) (natp j) (< j n))
	   (equal (entry i j (fmat* (elem-mat op m) a))
		  (entry i j (apply-row-op op a))))
  :hints (("Goal" :in-theory (enable row-op-p)
                  :use (elem-mat-row-op-1 elem-mat-row-op-2 elem-mat-row-op-3))))

(defthmd elem-mat-row-op
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n))
	   (equal (fmat* (elem-mat op m) a)
		  (apply-row-op op a)))
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (a (fmat* (elem-mat op m) a)) (b (apply-row-op op a)))
                        (:instance fmatp-fmat* (a (elem-mat op m)) (b a) (n m) (p n))
			(:instance elem-mat-row-op-4 (i (car (entry-diff (fmat* (elem-mat op m) a) (apply-row-op op a))))
			                             (j (cdr (entry-diff (fmat* (elem-mat op m) a) (apply-row-op op a)))))))))
		  
;; The product of the elementary matrices corresponding to a list of row operations:

(defun row-ops-mat (ops m)
  (if (consp ops)
      (fmat* (row-ops-mat (cdr ops) m)
             (elem-mat (car ops) m))             
    (id-fmat m)))

(defthm fmatp-row-ops-mat
  (implies (and (row-ops-p ops m) (posp m))
           (fmatp (row-ops-mat ops m) m m)))
	   
(defthmd fmat*-row-ops-mat
  (implies (and (fmatp a m n) (posp m) (posp n)
                (row-ops-p ops m))
	   (equal (fmat* (row-ops-mat ops m) a)
	          (apply-row-ops ops a)))
  :hints (("Goal" :in-theory (enable id-fmat-left))
          ("Subgoal *1/3" :in-theory (enable elem-mat-row-op)
	                  :use ((:instance fmat*-assoc (a (ROW-OPS-MAT (CDR OPS) M)) (b (ELEM-MAT (CAR OPS) M)) (c a)
	                                               (n m) (p m) (q n))))))

(defthmd row-ops-mat-append
  (implies (and (row-ops-p ops1 m) (row-ops-p ops2 m) (posp m))
           (equal (row-ops-mat (append ops1 ops2) m)
	          (fmat* (row-ops-mat ops2 m) (row-ops-mat ops1 m))))
  :hints (("Subgoal *1/3" :use ((:instance fmat*-assoc (n m) (p m) (q m)
                                                       (a (ROW-OPS-MAT OPS2 M))
                                                       (b (ROW-OPS-MAT (CDR OPS1) M))
						       (c (ELEM-MAT (CAR OPS1) M)))))
	  ("Subgoal *1/1" :in-theory (enable id-fmat-right))))

(defund row-reduce-mat (a)
  (row-ops-mat (row-reduce-ops a) (len a)))

(defthmd fmatp-row-reduce-mat
  (implies (and (fmatp a m n) (posp m) (posp n))
           (fmatp (row-reduce-mat a) m m))
  :hints (("Goal" :in-theory (enable row-ops-p-row-reduce-ops row-reduce-mat))))

(defthmd row-ops-mat-row-reduce
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (equal (fmat* (row-reduce-mat a) a)
		  (row-reduce a)))
  :hints (("Goal" :in-theory (enable fmat*-row-ops-mat apply-row-reduce-ops row-ops-p-row-reduce-ops row-reduce-mat))))


;;----------------------------------------------------------------------------------------
;; Invertibility
;;----------------------------------------------------------------------------------------

;; In this section, we focus on square matrices.  Given an nxn matrix a, we seek an nxn
;; matrix b such that (fmat* a b) = (fmat* b a) = (id-fmat n), which we shall call the
;; inverse of a.  If it exists, the inverse of a is unique in the following strong sense:
;; if (fmat* c a) = (id-fmat n), then

;;   c = (fmat* c (id-fmat n))
;;     = (fmat* c (fmat* a b))
;;     = (fmat* (fmat* c a) b))
;;     = (fmat* (id-fmat n) b))
;;     = b,

;; and if (fmat* a c) = (id-fmat n), then
;;   c = (fmat* (id-fmat n) c)
;;     = (fmat* (fmat* b a) c)
;;     = (fmat* b (fmat* a c))
;;     = (fmat* b (id-fmat n)))
;;     = b.

(defthm inverse-unique
  (implies (and (fmatp a n n) (fmatp b n n) (fmatp c n n) (posp n)
		(= (fmat* a b) (id-fmat n))
		(= (fmat* b a) (id-fmat n))
		(or (= (fmat* a c) (id-fmat n))
	            (= (fmat* c a) (id-fmat n))))
	   (equal c b))
  :hints (("Goal" :use ((:instance id-fmat-right (a c) (m n))
                        (:instance fmat*-assoc (a c) (b a) (c b) (m n) (p n) (q n))
			(:instance id-fmat-left (a b) (m n))
			(:instance id-fmat-left (a c) (m n))
                        (:instance fmat*-assoc (a b) (b a) (m n) (p n) (q n))
			(:instance id-fmat-right (a b) (m n)))))
  :rule-classes ())

;; Every elementary matrix has an inverse:

(defund invert-row-op (op)
  (case (car op)
    (1 (list 1 (f/ (cadr op)) (caddr op)))
    (2 (list 2 (f- (cadr op)) (caddr op) (cadddr op)))
    (3 op)))

(local-defthm list-3-members
  (implies (and (true-listp x) (true-listp y)
                (= (len x) 3) (= (len y) 3)
		(= (car x) (car y))
		(= (cadr x) (cadr y))
		(= (caddr x) (caddr y)))
	   (= x y))
  :rule-classes ())

(local-defthm list-4-members
  (implies (and (true-listp x) (true-listp y)
                (= (len x) 4) (= (len y) 4)
		(= (car x) (car y))
		(= (cadr x) (cadr y))
		(= (caddr x) (caddr y))
		(= (cadddr x) (cadddr y)))
	   (= x y))
  :rule-classes ())

(defthmd row-op-p-invert-row-op
  (implies (and (row-op-p op n) (posp n))
	   (and (row-op-p (invert-row-op op) n)
		(equal (invert-row-op (invert-row-op op))
		       op)))
  :hints (("Goal" :in-theory (enable row-op-p invert-row-op)
                  :use ((:instance list-3-members (x op) (y (list (car op) (cadr op) (caddr op))))
		        (:instance list-4-members (x op) (y (list (car op) (cadr op) (caddr op) (cadddr op))))))))

(local-defthmd nth-compose-invert-row-op
  (implies (and (fmatp a n n) (row-op-p op n) (posp n) (natp i) (< i n))
           (equal (nth i (apply-row-op (invert-row-op op) (apply-row-op op a)))
	          (nth i a)))
  :hints (("Goal" :in-theory (enable nth-ero1 nth-ero2 nth-ero3 apply-row-op row-op-p invert-row-op))
          ("Subgoal 3" :in-theory (e/d (nth-ero1) (fmatp-ero1))
	               :use ((:instance fmatp-ero1 (c (cadr op)) (k (caddr op)) (m n))
		             (:instance flistnp-row (i (caddr op)) (m n))))
          ("Subgoal 2" :in-theory (e/d (nth-ero3) (fmatp-ero3))
	               :use ((:instance fmatp-ero3 (j (cadr op)) (k (caddr op)) (m n))
		             (:instance flistnp-row (i (caddr op)) (m n))))
          ("Subgoal 1" :in-theory (e/d (nth-ero2) (fmatp-ero2 flist-scalar-mul-dist-2))
	               :use ((:instance fmatp-ero2 (c (cadr op)) (j (caddr op)) (k (cadddr op)) (m n))
		             (:instance flistnp-row (i (caddr op)) (m n))
		             (:instance flistnp-row (i (cadddr op)) (m n))
			     (:instance flist-add-assoc (x (flist-scalar-mul (f- (cadr op)) (nth (caddr op) a)))
			                                (y (flist-scalar-mul (cadr op) (nth (caddr op) a)))
							(z (nth (cadddr op) a)))
			     (:instance flist-scalar-mul-dist-2 (c (f- (cadr op))) (d (cadr op)) (x (nth (caddr op) a)))))))
		  
(defthmd compose-invert-row-op
  (implies (and (fmatp a n n) (row-op-p op n) (posp n))
           (equal (apply-row-op (invert-row-op op) (apply-row-op op a))
	          a))
  :hints (("Goal" :use (row-op-p-invert-row-op
                        (:instance nth-compose-invert-row-op
                          (i (car (entry-diff (apply-row-op (invert-row-op op) (apply-row-op op a)) a))))
			(:instance fmat-entry-diff-lemma (m n) (b a) (a (apply-row-op (invert-row-op op) (apply-row-op op a))))))))

(local-defthmd fmat*-elem-invert-row-op-1
  (implies (and (row-op-p op n) (posp n))
           (equal (fmat* (elem-mat (invert-row-op op) n)
			 (elem-mat op n))
		  (id-fmat n)))
  :hints (("Goal" :use (row-op-p-invert-row-op
                        (:instance elem-mat (m n))
                        (:instance compose-invert-row-op (a (id-fmat n)))
                        (:instance fmatp-elem-mat (m n))
                        (:instance elem-mat-row-op (m n) (op (invert-row-op op)) (a (elem-mat op n)))))))

(defthmd fmat*-elem-invert-row-op
  (implies (and (row-op-p op n) (posp n))
           (and (equal (fmat* (elem-mat (invert-row-op op) n)
			      (elem-mat op n))
		       (id-fmat n))
		(equal (fmat* (elem-mat op n)
		              (elem-mat (invert-row-op op) n))			      
		       (id-fmat n))))
  :hints (("Goal" :use (fmat*-elem-invert-row-op-1 row-op-p-invert-row-op
                        (:instance fmat*-elem-invert-row-op-1 (op (invert-row-op op)))))))

;; Every product of elementary matrices has an inverse:

(defun invert-row-ops (ops)
  (if (consp ops)
      (append (invert-row-ops (cdr ops))
              (list (invert-row-op (car ops))))
    ()))

(defthmd row-ops-p-invert-row-ops
  (implies (and (row-ops-p ops n) (posp n))
	   (row-ops-p (invert-row-ops ops) n))
  :hints (("Subgoal *1/2" :use ((:instance row-op-p-invert-row-op (op (car ops)))
                                (:instance append-row-ops (m n)
				                          (ops1 (invert-row-ops (cdr ops)))
				                          (ops2 (list (invert-row-op (car ops)))))))))

(local-defthmd invert-row-ops-mat-1
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                              (row-ops-mat (cdr ops) n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (row-ops-mat (append (invert-row-ops (cdr ops))
                                              (list (invert-row-op (car ops))))
                                      n)
                         (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n)))
	          (fmat* (fmat* (elem-mat (invert-row-op (car ops)) n)
		                (row-ops-mat (invert-row-ops (cdr ops)) n))
                         (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n)))))
  :hints (("goal" :in-theory (e/d (id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance row-ops-mat-append (m n)
	                                              (ops1 (invert-row-ops (cdr ops)))
	                                              (ops2 (list (invert-row-op (car ops)))))))))

(local-defthmd invert-row-ops-mat-2
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                              (row-ops-mat (cdr ops) n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (fmat* (elem-mat (invert-row-op (car ops)) n)
		                (row-ops-mat (invert-row-ops (cdr ops)) n))
                         (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n)))
	          (fmat* (elem-mat (invert-row-op (car ops)) n)
		         (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                                (fmat* (row-ops-mat (cdr ops) n)
                                       (elem-mat (car ops) n))))))
  :hints (("goal" :in-theory (e/d (id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance fmatp-elem-mat (op (car ops)) (m n))
			(:instance fmatp-fmat* (m n) (p n) (a (ROW-OPS-MAT (CDR OPS) N)) (b (elem-mat (car ops) n)))
		        (:instance fmat*-assoc (m n) (p n) (q n)
			                       (a (elem-mat (invert-row-op (car ops)) n))
					       (b (row-ops-mat (invert-row-ops (cdr ops)) n))
					       (c (fmat* (row-ops-mat (cdr ops) n)
                                                         (elem-mat (car ops) n))))))))

(local-defthmd invert-row-ops-mat-3
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                              (row-ops-mat (cdr ops) n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (elem-mat (invert-row-op (car ops)) n)
		         (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                                (fmat* (row-ops-mat (cdr ops) n)
                                       (elem-mat (car ops) n))))
		  (id-fmat n)))
  :hints (("goal" :in-theory (e/d (fmat*-elem-invert-row-op id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance fmatp-elem-mat (op (car ops)) (m n))
		        (:instance fmat*-assoc (m n) (p n) (q n)
			                       (a (row-ops-mat (invert-row-ops (cdr ops)) n))
					       (b (row-ops-mat (cdr ops) n))
					       (c (elem-mat (car ops) n)))))))

(local-defthmd invert-row-ops-mat-4
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (invert-row-ops (cdr ops)) n)
                              (row-ops-mat (cdr ops) n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (row-ops-mat (append (invert-row-ops (cdr ops))
                                              (list (invert-row-op (car ops))))
                                      n)
                         (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n)))
	          (id-fmat n)))
  :hints (("Goal" :use (invert-row-ops-mat-1 invert-row-ops-mat-2 invert-row-ops-mat-3))))

(local-defthmd invert-row-ops-mat-5
  (implies (and (row-ops-p ops n) (posp n))
           (equal (fmat* (row-ops-mat (invert-row-ops ops) n)
	                 (row-ops-mat ops n))
		  (id-fmat n)))
  :hints (("Subgoal *1/4" :in-theory (enable id-fmat-left))
          ("Subgoal *1/2" :use (invert-row-ops-mat-4))))

(local-defthmd invert-row-ops-mat-6
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (cdr ops) n)
                              (row-ops-mat (invert-row-ops (cdr ops))
                                           n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n))
                         (row-ops-mat (append (invert-row-ops (cdr ops))
                                              (list (invert-row-op (car ops))))
                                      n))
		  (fmat* (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n))
			 (fmat* (elem-mat (invert-row-op (car ops)) n)
		                (row-ops-mat (invert-row-ops (cdr ops)) n)))))
  :hints (("goal" :in-theory (e/d (id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance row-ops-mat-append (m n)
	                                              (ops1 (invert-row-ops (cdr ops)))
	                                              (ops2 (list (invert-row-op (car ops)))))))))

(local-defthmd invert-row-ops-mat-7
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (cdr ops) n)
                              (row-ops-mat (invert-row-ops (cdr ops))
                                           n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n))
			 (fmat* (elem-mat (invert-row-op (car ops)) n)
		                (row-ops-mat (invert-row-ops (cdr ops)) n)))
		  (fmat* (row-ops-mat (cdr ops) n)
		         (fmat* (elem-mat (car ops) n)
			        (fmat* (elem-mat (invert-row-op (car ops)) n)
		                       (row-ops-mat (invert-row-ops (cdr ops)) n))))))
  :hints (("Goal" :in-theory (e/d (fmat*-elem-invert-row-op id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance fmatp-elem-mat (op (car ops)) (m n))
		        (:instance fmat*-assoc (m n) (p n) (q n)
			                       (a (row-ops-mat (cdr ops) n))
					       (b (elem-mat (car ops) n))
					       (c (fmat* (elem-mat (invert-row-op (car ops)) n)
		                                         (row-ops-mat (invert-row-ops (cdr ops)) n))))))))

(local-defthmd invert-row-ops-mat-8
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (cdr ops) n)
                              (row-ops-mat (invert-row-ops (cdr ops))
                                           n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (row-ops-mat (cdr ops) n)
		         (fmat* (elem-mat (car ops) n)
			        (fmat* (elem-mat (invert-row-op (car ops)) n)
		                       (row-ops-mat (invert-row-ops (cdr ops)) n))))
		  (id-fmat n)))
  :hints (("Goal" :in-theory (e/d (fmat*-elem-invert-row-op id-fmat-left row-op-p-invert-row-op row-ops-p-invert-row-ops)
	                          (fmatp-elem-mat))
		  :use ((:instance fmatp-elem-mat (op (invert-row-op (car ops))) (m n))
		        (:instance fmatp-elem-mat (op (car ops)) (m n))
		        (:instance fmat*-assoc (m n) (p n) (q n)
			                       (a (elem-mat (car ops) n))
					       (b (elem-mat (invert-row-op (car ops)) n))
					       (c (row-ops-mat (invert-row-ops (cdr ops)) n)))))))

(local-defthmd invert-row-ops-mat-9
  (implies (and (consp ops)
                (row-op-p (car ops) n)
                (equal (fmat* (row-ops-mat (cdr ops) n)
                              (row-ops-mat (invert-row-ops (cdr ops))
                                           n))
                       (id-fmat n))
                (row-ops-p (cdr ops) n)
                (integerp n)
                (< 0 n))
           (equal (fmat* (fmat* (row-ops-mat (cdr ops) n)
                                (elem-mat (car ops) n))
                         (row-ops-mat (append (invert-row-ops (cdr ops))
                                              (list (invert-row-op (car ops))))
                                      n))
		  (id-fmat n)))
  :hints (("goal" :use (invert-row-ops-mat-6 invert-row-ops-mat-7 invert-row-ops-mat-8))))

(local-defthmd invert-row-ops-mat-10
  (implies (and (row-ops-p ops n) (posp n))
           (equal (fmat* (row-ops-mat ops n)
	                 (row-ops-mat (invert-row-ops ops) n))
	          (id-fmat n)))		  
  :hints (("Subgoal *1/4" :in-theory (enable id-fmat-left))
          ("Subgoal *1/2" :use (invert-row-ops-mat-9))))

(defthmd invert-row-ops-mat
  (implies (and (row-ops-p ops n) (posp n))
                (and (equal (fmat* (row-ops-mat (invert-row-ops ops) n)
	                           (row-ops-mat ops n))
		            (id-fmat n))
                     (equal (fmat* (row-ops-mat ops n)
			           (row-ops-mat (invert-row-ops ops) n))			      
		            (id-fmat n))))
  :hints (("Goal" :use (invert-row-ops-mat-5 invert-row-ops-mat-10))))

;; We shall show that a has an inverse iff (row-rank a) = n and that in this case,
;; the inverse of a is (row-reduce-mat a).  Thus, we define

(defund invertiblep (a n)
  (= (row-rank a) n))

(defund inverse-mat (a)
  (row-reduce-mat a))

;; First we show, as a consequence of lead-inds-ninit,  that if (invertiblep a n),
;; then (row-reduce a) = (id-fmat n):

(local-defthmd row-echelon-p-no-nonzero-rows-entry
  (implies (and (fmatp a n n)
		(posp n)
		(row-echelon-p a)
		(= (num-nonzero-rows a) n)
		(natp i) (< i n) (natp j) (< j n))
	   (equal (entry i j a)
	          (fdelta i j)))
  :hints (("Goal" :in-theory (enable lead-inds-ninit)
                  :use ((:instance num-nonzero-rows<=m (m n))
                        (:instance num-nonzero-rows-nonzero (m n))
                        (:instance num-nonzero-rows-nonzero (m n) (i j))
                        (:instance nth-first-nonzero (m n) (k i))
                        (:instance nth-first-nonzero (m n) (k i) (i j))
                        (:instance nth-first-nonzero (m n) (k j))
                        (:instance nth-first-nonzero (m n) (k j) (i j))
			(:instance nth-lead-inds (k i))
			(:instance nth-lead-inds (k j))))))

(defthm row-echelon-p-id-fmat
  (implies (and (fmatp a n n)
		(posp n)
		(row-echelon-p a)
		(= (num-nonzero-rows a) n))
	   (equal a (id-fmat n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (m n) (b (id-fmat n)))
                        (:instance row-echelon-p-no-nonzero-rows-entry
			            (i (car (entry-diff a (id-fmat n))))
			            (j (cdr (entry-diff a (id-fmat n)))))))))

;; Now let

;;    p = (inverse-mat a) = (row-reduce-mat a) = (row-ops-mat (row-reduce-ops a) n),

;;    q = (row-ops-mat (invert-row-ops (row-reduce-ops a)) n),

;; and

;;    r = (fmat* p a) = (row-reduce a).

;; By invert-row-ops-mat, (fmat* p q) = fmat* q p) = (id-fmat n).  If (row-rank a) = n,
;; then (num-nonzero-rows r) = n.  By row-echelon-p-id-fmat, (fmat* p a) = r = (id-fmat n),
;; and by inverse-unique, a = q.  Thus, (invertiblep a n) is a sufficient condition for
;; the existence of an inverse:

(defthmd invertiblep-sufficient
  (implies (and (fmatp a n n) (posp n) (invertiblep a n))
	   (let ((p (inverse-mat a)))
	     (and (fmatp p n n)
		  (equal (fmat* a p) (id-fmat n))
		  (equal (fmat* p a) (id-fmat n)))))
  :hints (("Goal" :in-theory (enable row-echelon-p-row-reduce row-ops-p-invert-row-ops row-ops-p-row-reduce-ops
                                     row-reduce-mat invertiblep inverse-mat row-reduce-mat row-rank)
                  :use ((:instance row-ops-mat-row-reduce (m n))
		        (:instance fmatp-row-reduce (m n))
		        (:instance fmatp-row-ops-mat (m n) (ops (INVERT-ROW-OPS (ROW-REDUCE-OPS A))))
		        (:instance invert-row-ops-mat (ops (row-reduce-ops a)))
		        (:instance row-echelon-p-id-fmat (a (row-reduce a)))
			(:instance inverse-unique (a (inverse-mat a))
			                          (b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))
						  (c a))))))

;; To prove the necessity of (invertiblep a n), suppose  and let (fmatp b n n).
;; If (fmat* a b) 0 (id-nat n), then

;;   (fmat* r (fmat* b q)) = (fmat* (fmt* p a) (fmat* b q))
;;                         = (fmat* p (fmat* (fmat* a b) q))
;;			   = (fmat* p q)
;;			   = (id-fmat n).

;; If (invertiblep a n) = NIL, then the last row of r is 0, and by nth-fmat*, the same
;; must be true of (id-fmat n), a contradiction.

(local-defthmd invertiblep-necessary-1
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)))
           (equal (fmat* (row-reduce a) (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))
	          (fmat* (row-ops-mat (row-reduce-ops a) n)
	                 (fmat* a (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))))))
  :hints (("Goal" :in-theory (enable row-reduce-mat)
                  :use ((:instance row-ops-p-row-reduce-ops (m n))
		        (:instance row-ops-mat-row-reduce (m n))
			(:instance row-ops-p-invert-row-ops (ops (row-reduce-ops a)))
		        (:instance invert-row-ops-mat (ops (row-reduce-ops a)))
		        (:instance fmatp-row-ops-mat (m n) (ops (row-reduce-ops a)))
		        (:instance fmatp-row-ops-mat (m n) (ops (invert-row-ops (row-reduce-ops a))))
			(:instance row-ops-p-invert-row-ops (ops (row-reduce-ops a)))
			(:instance fmatp-fmat* (m n) (p n) (a b) (b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))
			(:instance fmat*-assoc (m n) (p n) (q n)
			                       (a (row-ops-mat (row-reduce-ops a) n))
			                       (b a)
					       (c (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))))))))

(local-defthmd invertiblep-necessary-2
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)))
           (equal (fmat* (row-ops-mat (row-reduce-ops a) n)
	                 (fmat* a (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))))
	          (id-fmat n)))
  :hints (("Goal" :in-theory (enable row-reduce-mat id-fmat-left)
                  :use ((:instance row-ops-p-row-reduce-ops (m n))
		        (:instance row-ops-mat-row-reduce (m n))
			(:instance row-ops-p-invert-row-ops (ops (row-reduce-ops a)))
		        (:instance invert-row-ops-mat (ops (row-reduce-ops a)))
		        (:instance fmatp-row-ops-mat (m n) (ops (row-reduce-ops a)))
		        (:instance fmatp-row-ops-mat (m n) (ops (invert-row-ops (row-reduce-ops a))))
			(:instance row-ops-p-invert-row-ops (ops (row-reduce-ops a)))
			(:instance fmat*-assoc (m n) (p n) (q n)
					       (c (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))))))

(local-defthmd invertiblep-necessary-3
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)))
           (equal (fmat* (row-reduce a) (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))
	          (id-fmat n)))
  :hints (("Goal" :use (invertiblep-necessary-1 invertiblep-necessary-2))))

(local-defthmd invertiblep-necessary-4
  (implies (and (fmatp a n n) (posp n) (not (invertiblep a n)))
           (flist0p (nth (1- n) (row-reduce a))))
  :hints (("Goal" :in-theory (enable invertiblep row-rank)
                  :use ((:instance fmatp-row-reduce (m n))
		        (:instance row-echelon-p-row-reduce (m n))
			(:instance num-nonzero-rows<=m (m n) (a (row-reduce a)))
		        (:instance num-nonzero-rows-nonzero (m n) (a (row-reduce a)) (i (1- n)))))))

(local-defthmd invertiblep-necessary-5
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (not (invertiblep a n)))
           (equal (nth (1- n) (row-reduce a))
	          (flistn0 n)))
  :hints (("Goal" :use (invertiblep-necessary-4
			(:instance fmatp-row-reduce (m n))
			(:instance len-fmat-row (m n) (i (1- n)) (a (row-reduce a)))
			(:instance flist0p-flistn0-len (x (nth (1- n) (row-reduce a))))))))

(local-defthmd invertiblep-necessary-6
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (not (invertiblep a n)))
           (equal (entry (1- n) (1- n) (fmat* (row-reduce a) (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))))
	          (f0)))
  :hints (("Goal" :in-theory (enable fmatp-row-reduce)
                  :use (invertiblep-necessary-5
		        (:instance row-ops-p-row-reduce-ops (m n))
			(:instance row-ops-p-invert-row-ops (ops (row-reduce-ops a)))
			(:instance fmat*-entry (m n) (p n)
			                       (a (row-reduce a))
			                       (b (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))
					       (i (1- n))
					       (j (1- n)))
			(:instance flistnp-col (j (1- n)) (m n) (a (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n))))
			(:instance fdot-flistn0 (x (col (1- n) (fmat* b (row-ops-mat (invert-row-ops (row-reduce-ops a)) n)))))))))

(local-defthmd invertiblep-necessary-7
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)) (not (invertiblep a n)))
           (equal (entry (1- n) (1- n) (id-fmat n))
	          (f0)))
  :hints (("Goal" :use (invertiblep-necessary-3 invertiblep-necessary-6))))

(defthmd invertiblep-necessary
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)))
	   (invertiblep a n))
  :hints (("Goal" :in-theory (enable entry-id-fmat)
                  :use (invertiblep-necessary-7))))

;; Some consequences of the preceding results:

(defthmd inverse-inverse-mat
  (implies (and (fmatp a n n) (posp n) (invertiblep a n))
	   (and (invertiblep (inverse-mat a) n)
		(equal (inverse-mat (inverse-mat a))
		       a)))
  :hints (("Goal" :use (invertiblep-sufficient
                        (:instance invertiblep-necessary (a (inverse-mat a)) (b a))
			(:instance invertiblep-sufficient (a (inverse-mat a)))
			(:instance inverse-unique (a (inverse-mat a)) (b (inverse-mat (inverse-mat a))) (c a))))))

(defthmd invertiblep-inverse
  (implies (and (fmatp a n n) (fmatp b n n) (posp n)
		(or (= (fmat* a b) (id-fmat n))
		    (= (fmat* b a) (id-fmat n))))
	   (and (invertiblep a n)
		(equal (inverse-mat a) b)))
  :hints (("Goal" :use (invertiblep-sufficient invertiblep-necessary inverse-inverse-mat
                        (:instance invertiblep-necessary (a b) (b a))
			(:instance invertiblep-sufficient (a b))
			(:instance inverse-inverse-mat (a b))
			(:instance inverse-unique (a b) (b (inverse-mat b)) (c a))
			(:instance inverse-unique (b (inverse-mat a)) (c b))))))

(defthmd invertiblep-cancel
  (implies (and (fmatp a m n) (fmatp b m n) (fmatp p m m) (invertiblep p m) (posp m) (posp n))
           (iff (equal (fmat* p a) (fmat* p b))
	        (equal a b)))
  :hints (("Goal" :in-theory (enable id-fmat-left)
                  :use ((:instance invertiblep-sufficient (a p) (n m))
                        (:instance fmat*-assoc (n m) (p m) (q n) (a (inverse-mat p)) (b p) (c a))
                        (:instance fmat*-assoc (n m) (p m) (q n) (a (inverse-mat p)) (b p) (c b))))))

(defthmd invertiblep-row-ops-mat
  (implies (and (row-ops-p ops n) (posp n))
	   (and (invertiblep (row-ops-mat ops n) n)
		(equal (inverse-mat (row-ops-mat ops n))
		       (row-ops-mat (invert-row-ops ops) n))))
  :hints (("Goal" :use (invert-row-ops-mat row-ops-p-invert-row-ops
                        (:instance invertiblep-inverse (a (row-ops-mat ops n)) (b (row-ops-mat (invert-row-ops ops) n)))))))

(defthm invertiblep-row-reduce-mat
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (invertiblep (row-reduce-mat a) m))
  :hints (("Goal" :in-theory (enable invertiblep-row-ops-mat row-ops-p-row-reduce-ops row-reduce-mat))))

(defthmd row-reduce-mat-invertiblep
  (implies (invertiblep a n)
	   (equal (inverse-mat a)
		  (row-reduce-mat a)))
  :hints (("Goal" :in-theory (enable row-reduce-mat inverse-mat)
                  :use ((:instance row-ops-mat-row-reduce (m n))
		        (:instance fmatp-row-reduce (m n))))))

(defthmd invertiblep-factor
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (invertiblep (fmat* a b) n))
	   (and (invertiblep a n) (invertiblep b n)))
  :hints (("Goal" :use ((:instance invertiblep-sufficient (a (fmat* a b)))
                        (:instance fmatp-fmat* (m n) (p n))
			(:instance fmat*-assoc (m n) (p n) (q n) (c (inverse-mat (fmat* a b))))
			(:instance fmatp-fmat* (m n) (p n)(a b) (b (inverse-mat (fmat* a b))))
			(:instance invertiblep-inverse (b (fmat* b (inverse-mat (fmat* a b)))))
			(:instance fmat*-assoc (m n) (p n) (q n) (a (inverse-mat (fmat* a b))) (b a) (c b))
			(:instance fmatp-fmat* (m n) (p n) (a (inverse-mat (fmat* a b))) (b a))
			(:instance invertiblep-inverse (a b) (b (fmat* (inverse-mat (fmat* a b)) a)))))))			

(defthmd inverse-fmat*
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (invertiblep a n) (invertiblep b n))
	   (and (invertiblep (fmat* a b) n)
		(equal (inverse-mat (fmat* a b))
		       (fmat* (inverse-mat b) (inverse-mat a)))))
  :hints (("Goal" :in-theory (enable id-fmat-right)
                  :use (invertiblep-sufficient fmatp-fmat*
                        (:instance invertiblep-sufficient (a b))
			(:instance fmat*-assoc (m n) (p n) (q n) (a (fmat* a b)) (b (inverse-mat b)) (c (inverse-mat a)))
			(:instance fmat*-assoc (m n) (p n) (q n) (c (inverse-mat b)))
			(:instance invertiblep-inverse (a (fmat* a b)) (b (fmat* (inverse-mat b) (inverse-mat a))))
			(:instance fmatp-fmat* (m n) (p n) (a (inverse-mat b)) (b (inverse-mat a)))))))


;;----------------------------------------------------------------------------------------
;; Systems of Simultaneous Linear Equations
;;----------------------------------------------------------------------------------------

;; Let a be an mxn matrix with (entry i j a) = aij for 0 <= i < m and 0 <= j < n.
;; Let b = (b0 b1 ... b(m-1)) be an flist of length m.  We seek an flist x = (x0 x1 ... x(n-1))
;; of length n that satisfies the system of m linear equations

;;   a00*x0     + ... + a0(n-1)*x(n-1)     = b0
;;   a10*x0     + ... + a1(n-1)*x(n-1)     = b1
;;    ...
;;   a(m-1)0*x0 + ... + a(m-1)(n-1)*x{n-1) = b(m-1)

;; In order to express this as a matrix equation, we define the column matrix formed by an flist:

(defund row-mat (x)
  (list x))

(defund col-mat (x)
  (transpose-mat (row-mat x)))

(defthm fmatp-row-mat
  (implies (flistnp x n)
           (fmatp (row-mat x) 1 n))
  :hints (("Goal" :in-theory (enable fmatp row-mat))))

(defthm fmatp-col-mat
  (implies (and (posp n) (flistnp x n))
           (fmatp (col-mat x) n 1))
  :hints (("Goal" :in-theory (enable col-mat fmatp-transpose))))

;; The above system of equations may be expressed as

;;   (fmat* a (col-mat x)) = (col-mat b).

;; Thus, a solution is an flist x of length n that satisfies the following predicate:

(defund solutionp (x a b)
  (equal (fmat* a (col-mat x))
         (col-mat b)))

;; In the following, we shall use the variables bc and xc to refer to (col-mat b) and (col-mat x),
;; respectively.  Thus, we seek solutions of the equation (fmat* a xc) = bc, where bc and xc are 
;; mx1 and nx1 column matrices, respectively.

;; Let p = (row-reduce-mat a), ra = (fmat* p a), and br = (fmat* p b).  Left-multiplying the above
;; equation by p yields the equivalent equation

;;   (fmat* ar xc) = br.

(defthmd reduce-linear-equations
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n))
           (let* ((bc (col-mat b))
	          (xc (col-mat x))
		  (p (row-reduce-mat a))
		  (ar (fmat* p a))
		  (br (fmat* p bc)))
             (iff (solutionp x a b)
	          (equal (fmat* ar xc) br))))
  :hints (("Goal" :in-theory (enable id-fmat-left fmatp-row-reduce-mat solutionp)
                  :use ((:instance fmat*-assoc (n m) (p n) (q 1) (a (row-reduce-mat a)) (b a) (c (col-mat x)))		  
		        (:instance invertiblep-cancel (n 1) (p (row-reduce-mat a)) (a (fmat* a (col-mat x))) (b (col-mat b)))
			(:instance fmatp-fmat* (p 1) (b (col-mat x)))))))

;; Thus, our objective is to solve the equation (fmat* ar xc) br), where ar is a row-echelon mxn
;; matrix, xc is an nx1 column matrix, and br is an mx1 column matrix.

;; Let q = (num-nonzero-rows ar) = (row-rank a).  The existence of a solution of this equation is
;; determined by whether the last m - q entries of the mx1 matrix br are all (f0).  This is indicated 
;; by the value of the following function:

(defun find-nonzero (br q m)
  (if (and (natp q) (natp m) (< q m))
      (if (= (entry (1- m) 0 br) (f0))
          (find-nonzero br q (1- m))
	(1- m))
    ()))

(defthmd find-nonzero-nonzero
  (implies (and (natp q) (natp m) (<= q m))
           (let ((k (find-nonzero br q m)))
	     (if k
	         (and (natp k) (<= q k) (< k m)
		      (not (= (entry k 0 br) (f0))))
	       (implies (and (natp j) (<= q j) (< j m))
	                (= (entry j 0 br) (f0)))))))

(defun solvablep (a b)
  (null (find-nonzero (fmat* (row-reduce-mat a) (col-mat b))
                      (row-rank a)
		      (len a))))

;; Suppose first that (find-nonzero br q m) = k <> nil, so that (solvablep a b) = nil.  Then 
;; (row k ar) = (flistn0 n) and (entry k 0 br) <> (f0).  It follows that

;;   (entry k 0 (fmat* ar xc)) = (fdot (row k ar) (col 0 xc)) = (f0) <> (nth k 0 br),

;; and hence (fmat* ar xc) <> br:

(local-defthmd row-echelon-p-unsolvable-case-1
  (let* ((q (num-nonzero-rows ar))
         (k (find-nonzero br q m)))
    (implies (and (fmatp ar m n) (posp m) (posp n) (fmatp br m 1) (fmatp xc n 1)
                  (row-echelon-p ar)
		  k)
	     (and (natp k) (< k m) (flist0p (nth k ar)) (not (= (entry k 0 br) (f0))))))
  :hints (("Goal" :use ((:instance num-nonzero-rows<=m (a ar))
                        (:instance num-nonzero-rows-nonzero (i (find-nonzero br (num-nonzero-rows ar) m)) (a ar))
                        (:instance find-nonzero-nonzero (q (num-nonzero-rows ar)))))))

(local-defthmd row-echelon-p-unsolvable-case-2
  (let* ((q (num-nonzero-rows ar))
         (k (find-nonzero br q m)))
    (implies (and (fmatp ar m n) (posp m) (posp n) (fmatp br m 1) (fmatp xc n 1)
                  (row-echelon-p ar)
                  k)
	     (equal (entry k 0 (fmat* ar xc)) (f0))))
  :hints (("Goal" :in-theory (disable fdot-flistn0)
                  :use (row-echelon-p-unsolvable-case-1
                        (:instance fmat*-entry (a ar) (b xc) (p 1) (i (find-nonzero br (num-nonzero-rows ar) m)) (j 0))
			(:instance fmatp-fmat* (p 1) (a ar) (b xc))
			(:instance flist0p-flistn0-len (x (nth (find-nonzero br (num-nonzero-rows ar) m) ar)))
			(:instance flistnp-row (a ar) (i (find-nonzero br (num-nonzero-rows ar) m)))
			(:instance fdot-flistn0 (x (col 0 xc)))
			(:instance flistnp-col (m n) (n 1) (a xc) (j 0))))))

(defthmd row-echelon-p-unsolvable-case
  (implies (and (fmatp ar m n) (posp m) (posp n) (fmatp br m 1) (fmatp xc n 1)
                (row-echelon-p ar)
                (find-nonzero br (num-nonzero-rows ar) m))
           (not (equal (fmat* ar xc) br)))
  :hints (("Goal" :use (row-echelon-p-unsolvable-case-1 row-echelon-p-unsolvable-case-2))))

;; We combine this result with reduce-linear-equations to conclude that the system
;; of equations has no solution:

(defthmd linear-equations-unsolvable-case
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
                (not (solvablep a b)))
	   (not (solutionp x a b)))
  :hints (("Goal" :in-theory (enable solutionp)
                  :use (reduce-linear-equations fmatp-row-reduce-mat row-echelon-p-row-reduce row-ops-mat-row-reduce
		        (:instance fmatp-fmat* (n m) (p n) (a (row-reduce-mat a)) (b a))
		        (:instance row-echelon-p-unsolvable-case (ar (fmat* (row-reduce-mat a) a))
			                                         (br (fmat* (row-reduce-mat a) (col-mat b)))
								 (xc (col-mat x)))))))

;; Now suppose (find-nonzero br q m) = nil, i.e., (solvable a b m) = t.  Consider the matrices 
;; aq and bq consisting of the first q rows of ar and br, respectively, computed by the following:

(defun first-rows (q a)
  (if (zp q)
      ()
    (cons (car a) (first-rows (1- q) (cdr a)))))

;; Note that aq is a row-echelon qxn matrix of row-rank q:

(defthmd fmatp-first-rows
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp q) (<= q m))
	   (fmatp (first-rows q a) q n))
  :hints (("Goal" :in-theory (enable fmatp))))

(defthmd nth-first-rows
  (implies (and (fmatp a m n) (natp m)
                (natp q) (<= q m) (natp i) (< i q))
	   (equal (nth i (first-rows q a))
	          (nth i a)))
  :hints (("Goal" :in-theory (enable fmatp))))

(defthmd num-nonzero-rows-first-rows
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp q) (<= q (num-nonzero-rows a)))
	   (equal (num-nonzero-rows (first-rows q a)) q))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthmd column-clear-p-first-rows-1
  (implies (and (natp m) (natp q) (<= q m) (column-clear-p a k j m))
	   (column-clear-p a k j q)))

(local-defthmd column-clear-p-first-rows-2
  (implies (and (fmatp a m n) (natp m) (natp q) (<= q m) (natp r) (<= r q)
                (column-clear-p a k j r))
	   (column-clear-p (first-rows q a) k j r))
  :hints (("Goal" :induct (fact r))
          ("Subgoal *1/2" :in-theory (enable nth-first-rows))))

(local-defthmd column-clear-p-first-rows
  (implies (and (fmatp a m n) (natp m) (natp q) (<= q m)
                (column-clear-p a k j m))
	   (column-clear-p (first-rows q a) k j q))
  :hints (("Goal" :use (column-clear-p-first-rows-1
                        (:instance column-clear-p-first-rows-2 (r q))))))

(local-defthmd r-e-p-a-f-r-i-1
  (implies (and (fmatp a m n) (posp m) (posp n)
                (posp k) (natp q) (<= k q) (<= q m)
		(null (row-with-nonzero-at-least-index a m (1- k))))
	   (null (row-with-nonzero-at-least-index (first-rows q a) q (1- k))))
  :hints (("Goal" :in-theory (enable fmatp-first-rows nth-first-rows)
                  :use ((:instance row-with-nonzero-at-least-index-non-nil (k (1- k)) (a (first-rows q a)) (m q))
		        (:instance row-with-nonzero-at-least-index-nil (k (1- k))
			                                               (j (row-with-nonzero-at-least-index (first-rows q a) q (1- k))))))))

(local-defthmd r-e-p-a-f-r-i-2
  (implies (and (fmatp a m n) (posp m) (posp n)
                (posp k) (natp q) (<= k q) (<= q m)
		(row-echelon-p-aux a m k)
		(row-with-nonzero-at-least-index a m (1- k)))
	   (and (not (flist0p (nth (1- k) (first-rows q a))))
	        (column-clear-p (first-rows q a) (1- k) (first-nonzero (nth (1- k) (first-rows q a))) q)))
  :hints (("Goal" :in-theory (enable fmatp-first-rows nth-first-rows)
                  :use ((:instance row-with-nonzero-at-least-index-non-nil (k (1- k)))
		        (:instance column-clear-p-first-rows (k (1- k)) (j (first-nonzero (nth (1- k) a))))))))

(local-defthmd r-e-p-a-f-r-i-3
  (implies (and (fmatp a m n) (posp m) (posp n)
                (posp k) (natp q) (<= k q) (<= q m)
		(row-echelon-p-aux a m k)
		(row-with-nonzero-at-least-index a m (1- k))
		(natp j) (<= k j) (< j q))
	  (or (flist0p (nth j (first-rows q a)))
               (< (first-nonzero (nth (1- k) (first-rows q a)))
                  (first-nonzero (nth j (first-rows q a))))))
  :hints (("Goal" :in-theory (enable fmatp-first-rows nth-first-rows)
                  :use ((:instance row-echelon-p-aux-first-nonzero-min (q j))))))

(local-defthmd r-e-p-a-f-r-i-4
  (implies (and (fmatp a m n) (posp m) (posp n)
                (posp k) (natp q) (<= k q) (<= q m)
		(row-echelon-p-aux a m k)
		(row-with-nonzero-at-least-index a m (1- k))
		(row-with-nonzero-at-least-index (first-rows q a) q (1- k)))
	  (equal (row-with-nonzero-at-least-index (first-rows q a) q (1- k))
	         (1- k)))
  :hints (("Goal" :in-theory (enable fmatp-first-rows fmatp-first-rows)
                  :use (r-e-p-a-f-r-i-2
		        (:instance row-with-nonzero-at-least-index-non-nil (k (1- k)) (j (1- k)) (a (first-rows q a)) (m q))
			(:instance r-e-p-a-f-r-i-3 (j (row-with-nonzero-at-least-index (first-rows q a) q (1- k))))))))

(local-defthmd row-echelon-p-aux-first-rows-induction
  (implies (and (fmatp a m n) (posp m) (posp n)
                (posp k) (natp q) (<= k q) (<= q m)
		(row-echelon-p-aux a m k)
		(row-echelon-p-aux (first-rows q a) q (1- k)))
	   (row-echelon-p-aux (first-rows q a) q k))
  :hints (("Goal" :use (r-e-p-a-f-r-i-1 r-e-p-a-f-r-i-2 r-e-p-a-f-r-i-4))))

(local-defthmd row-echelon-p-aux-first-rows
  (implies (and (fmatp a m n) (posp m) (posp n)
                (natp k) (natp q) (<= k q) (<= q m)
		(row-echelon-p-aux a m k))              
	   (row-echelon-p-aux (first-rows q a) q k))
  :hints (("Goal" :induct (row-echelon-p-aux a q k))
          ("Subgoal *1/2" :use (row-echelon-p-aux-first-rows-induction))))

(defthmd row-echelon-p-first-rows
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp q) (<= q m))
	   (row-echelon-p (first-rows q a)))
  :hints (("Goal" :in-theory (e/d (row-echelon-p) (row-echelon-p-aux-<=))
                  :use (fmatp-first-rows
		        (:instance row-echelon-p-aux-first-rows (k q))
		        (:instance row-echelon-p-aux-<= (k m) (r q))))))

(defthmd first-rows-rank
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar))
           (let* ((q (num-nonzero-rows ar))
	          (aq (first-rows q ar)))
              (and (fmatp aq q n)
	           (row-echelon-p aq)
	           (equal (num-nonzero-rows aq) q))))
  :hints (("Goal" :use ((:instance row-echelon-p-first-rows (a ar) (q (num-nonzero-rows ar)))
                        (:instance num-nonzero-rows<=m (a ar))
			(:instance fmatp-first-rows (a ar) (q (num-nonzero-rows ar)))
			(:instance num-nonzero-rows-first-rows (a ar) (q (num-nonzero-rows ar)))))))

;; According to the following result, (first-rows q (fmat* ar xc)) = (fmat* aq xc):

(defthmd first-rows-fmat*
  (implies (and (fmatp a m n) (fmatp b n p) (natp m) (posp n) (posp p)
                (natp q) (<= q m))
           (equal (first-rows q (fmat* a b))
	          (fmat* (first-rows q a) b)))
  :hints (("Goal" :in-theory (enable fmatp fmat*))))

;; For q <= k < m, since (flist0p (row k ar)), (entry k 0 (fmat* ar xc)) = (f0).
;; Thus (first-nonzero (fmat* ar xc) q m) = nil, which implies

;;   ((fmat* ar xc) = br <=> (fmat* aq xc) = bq:

(local-defthmd null-first-nonzero-fmat*-1
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar) (fmatp xc n 1)
                (natp k) (>= k (num-nonzero-rows ar)) (< k m))
	   (equal (entry k 0 (fmat* ar xc))
	          (f0)))
  :hints (("Goal" :use ((:instance fmat*-entry (a ar) (b xc) (p 1) (i k) (j 0))
                        (:instance num-nonzero-rows-nonzero (a ar) (i k))
			(:instance flistnp-col (j 0) (a xc) (m n) (n 1))
			(:instance fdot-flistn0 (x (col 0 xc)))
			(:instance flist0p-flistn0-len (x (nth k ar)))
			(:instance flistnp-row (a ar) (i k))))))

(defthmd null-first-nonzero-fmat*
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar) (fmatp xc n 1))
	   (null (find-nonzero (fmat* ar xc) (num-nonzero-rows ar) m)))
  :hints (("Goal" :use ((:instance find-nonzero-nonzero (br (fmat* ar xc)) (q (num-nonzero-rows ar)))
                        (:instance null-first-nonzero-fmat*-1 (k (find-nonzero (fmat* ar xc) (num-nonzero-rows ar) m)))
			(:instance fmatp-fmat* (p 1) (a ar) (b xc))
			(:instance num-nonzero-rows<=m (a ar))))))

(local-defthmd first-rows-equal-1
  (implies (and (fmatp b m 1) (natp m)
                (natp q) (<= q m) (natp i) (>= i q) (< i m)
		(null (find-nonzero b q m)))
	   (equal (nth i b)
	          (list (f0))))
  :hints (("Goal" :use ((:instance find-nonzero-nonzero (br b) (j i))
                        (:instance flistnp-row (a b) (n 1)))
		  :expand ((flistnp (nth i b) 1)))))

(local-defthmd first-rows-equal-2
  (implies (and (fmatp b1 m 1) (fmatp b2 m 1) (natp m)
                (natp q) (<= q m)
		(null (find-nonzero b1 q m))
		(null (find-nonzero b2 q m))
		(equal (first-rows q b1) (first-rows q b2))
		(natp i) (< i m))
	   (equal (nth i b1) (nth i b2)))
  :hints (("Goal" :use ((:instance nth-first-rows (n 1) (a b1))
                        (:instance nth-first-rows (n 1) (a b2))
			(:instance first-rows-equal-1 (b b1))
                        (:instance first-rows-equal-1 (b b2))))))			

(defthmd first-rows-equal
  (implies (and (fmatp b1 m 1) (fmatp b2 m 1) (posp m)
                (natp q) (<= q m)
		(null (find-nonzero b1 q m))
		(null (find-nonzero b2 q m)))
	   (iff (equal (first-rows q b1) (first-rows q b2))
	        (equal b1 b2)))
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (n 1) (a b1) (b b2))
                        (:instance first-rows-equal-2 (i (car (entry-diff b1 b2))))))))

(defthmd first-rows-linear-equations
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar)
                (fmatp br m 1) (fmatp xc n 1)
                (null (find-nonzero br (num-nonzero-rows ar) m)))
	   (let* ((q (num-nonzero-rows ar))
	          (aq (first-rows q ar))
	          (bq (first-rows q br)))
	     (iff (equal (fmat* ar xc) br)
	          (equal (fmat* aq xc) bq))))
  :hints (("Goal" :use (null-first-nonzero-fmat*
                        (:instance first-rows-equal (b1 (fmat* ar xc)) (b2 br) (q (num-nonzero-rows ar)))
                        (:instance fmatp-fmat* (p 1) (a ar) (b xc))
			(:instance first-rows-fmat* (p 1) (a ar) (b xc) (q (num-nonzero-rows ar)))
			(:instance num-nonzero-rows<=m (a ar))))))

;; Our objective, therefore, is to solve the equation (fmat* aq xc) = bq.			

;; By row-rank<=n, q <= n.  If q = n, then by row-echelon-p-id-fmat, aq = (id-fmat n) and
;; (fmat* aq xc) = bq iff xc = bq:

(defthmd row-echelon-p-unique-solution-case
  (implies (and (fmatp aq n n) (posp n) (fmatp bq n 1) (fmatp xc n 1)
                (row-echelon-p aq)
		(= (num-nonzero-rows aq) n))
	   (iff (equal (fmat* aq xc) bq)
	        (equal xc bq)))
  :hints (("Goal" :use ((:instance row-echelon-p-id-fmat (a aq))
                        (:instance id-fmat-left (m n) (n 1) (a xc))))))

;; Combine the last 2 results with reduce-linear-equations to conclude that there exists a unique
;; solution in this case:

(local-defthmd linear-equations-unique-solution-case-1
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
                (solvablep a b)
	        (= (row-rank a) n))
	   (iff (solutionp x a b)
	        (equal (col-mat x) (first-rows n (fmat* (row-reduce-mat a) (col-mat b))))))
  :hints (("Goal" :in-theory (enable row-ops-mat-row-reduce fmatp-row-reduce-mat solutionp
                                     row-echelon-p-row-reduce fmatp-row-reduce)
                  :use (reduce-linear-equations
                        (:instance row-echelon-p-unique-solution-case
			            (aq (first-rows n (row-reduce a)))
			            (bq (first-rows n (fmat* (row-reduce-mat a) (col-mat b))))
                                    (xc (col-mat x)))
                        (:instance first-rows-linear-equations (ar (row-reduce a))
			                                       (xc (col-mat x))
							       (br (fmat* (row-reduce-mat a) (col-mat b))))
			(:instance fmatp-fmat* (a (row-reduce-mat a)) (b (col-mat b)) (n m) (p 1))
			(:instance first-rows-rank (ar (row-reduce a)))))))

(local-defthmd car-row-mat
  (equal (car (row-mat x)) x)
  :hints (("Goal" :in-theory (enable row-mat))))

(local-defthmd col-0-col-mat
  (implies (flistnp x n)
           (equal (col 0 (col-mat x)) x))
  :hints (("Goal" :in-theory (disable fmatp-row-mat)
                  :use (fmatp-row-mat car-row-mat
                        (:instance col-transpose-fmat (j 0) (a (row-mat x)) (m 1)))
                  :expand ((col-mat x)))))

(local-defthm linear-equations-unique-solution-case-3
  (implies (and (posp n) (fmatp a n 1) (fmatp b n 1) (= (col 0 a) (col 0 b)))
           (= a b))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fmat-entry-diff-lemma (m n) (n 1))
                       (:instance nth-col (j 0) (i (car (entry-diff a b))))
                       (:instance nth-col (j 0) (a b) (i (car (entry-diff a b))))))))

(defthmd linear-equations-unique-solution-case
  (let* ((br (fmat* (row-reduce-mat a) (col-mat b)))
         (bq (first-rows n br)))
    (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
                  (solvablep a b)
	          (= (row-rank a) n)) ;(invertiblep a n))
	     (iff (solutionp x a b)
	          (equal x (col 0 bq)))))
  :hints (("Goal" :in-theory (enable row-ops-mat-row-reduce fmatp-row-reduce-mat solutionp
                              invertiblep row-echelon-p-row-reduce fmatp-row-reduce)
                  :use (linear-equations-unique-solution-case-1 col-0-col-mat
                        (:instance linear-equations-unique-solution-case-3
			             (a (col-mat x)) (b (first-rows n (fmat* (row-reduce-mat a) (col-mat b)))))
			(:instance fmatp-fmat* (a (row-reduce-mat a)) (b (col-mat b)) (n m) (p 1))
			(:instance num-nonzero-rows<=m (a (row-reduce a)))
			(:instance fmatp-first-rows (q n) (n 1) (a (fmat* (row-reduce-mat a) (col-mat b))))))))

;; In the remainder of this section, we treat the general case (solvablep a b) = t with arbitrary
;; row-rank q <= n.  The equation (fmat* aq xc) = bq holds iff for 0 <= i < q,

;;   (nth i (fmat* aq xc)) = (nth i bq)

;; or equivalently,

;;   (fdot (row i aq) x) = (car (nth i bq)).

(local-defthmd nth-fmat*-aq-xc-1
  (implies (and (flistnp x n) (posp n))
           (equal (transpose-mat (col-mat x))
	          (list x)))
  :hints (("Goal" :in-theory (enable col-mat row-mat)
                  :use (fmatp-row-mat
		        (:instance transpose-fmat-2 (a (list x)) (m 1))))))

(local-defthmd nth-fmat*-aq-xc-2
  (implies (and (fmatp aq q n) (flistnp x n) (posp q) (posp n) (natp i) (< i q))
           (equal (nth i (fmat* aq (col-mat x)))
	          (list (fdot (nth i aq) x))))
  :hints (("Goal" :in-theory (enable nth-fmat*)
                  :use (nth-fmat*-aq-xc-1))))

(local-defthmd nth-fmat*-aq-xc-3
  (implies (and (fmatp bq q 1) (posp q) (natp i) (< i q))
           (equal (nth i bq) (list (car (nth i bq)))))
  :hints (("Goal" :use ((:instance flistnp-row (a bq) (m q) (n 1)))
                  :expand ((:free (x l) (flistnp x l))))))

(defthmd nth-fmat*-aq-xc
  (implies (and (fmatp aq q n) (fmatp bq q 1) (flistnp x n) (posp q) (posp n) (natp i) (< i q))
           (iff (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))
	        (equal (fdot (nth i aq) x)
		       (car (nth i bq)))))
  :hints (("Goal" :in-theory (enable nth-fmat*-aq-xc-2)
                  :use (nth-fmat*-aq-xc-3))))
			
;; We shall split (fdot (nth i aq) x) into 2 sums, corresponding to the list (lead-inds aq) and the
;; list of remaining indices, (free-inds aq n), which we define as follows:

(defund free-inds (a n)
  (set-difference-equal (ninit n) (lead-inds a)))

(local-defthmd consp-set-difference
  (implies (not (sublistp l m))
           (consp (set-difference-equal l m))))

(local-defthmd member-set-difference
  (iff (member x (set-difference-equal l m))
       (and (member x l) (not (member x m)))))

(local-defthmd dlistp-set-difference
  (implies (dlistp l)
           (dlistp (set-difference-equal l m)))
  :hints (("Subgoal *1/5" :use ((:instance member-set-difference (x (car l)) (l (cdr l)))))))

(defthmd dlistp-free-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (dlistp (free-inds a n)))
  :hints (("Goal" :in-theory (enable free-inds))))

(defthmd member-free-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (iff (member x (free-inds a n))
	        (and (member x (ninit n))
		     (not (member x (lead-inds a))))))
  :hints (("Goal" :in-theory (enable free-inds)
                  :use ((:instance member-set-difference (l (ninit n)) (m (lead-inds a)))))))

(defthmd consp-free-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a) (< m n))
           (consp (free-inds a n)))
  :hints (("Goal" :in-theory (enable free-inds permp)
                  :use (len-lead-inds-bound sublistp-lead-inds-ninit dlistp-lead-inds
		        (:instance consp-set-difference (l (ninit n)) (m (lead-inds a)))
                        (:instance eq-len-permp (l (ninit n)) (m (lead-inds a)))))))

;; Note that if q = n, then (free-inds aq n) = nil.  In general, given a sublist of (ninit n), a dot
;;  product of 2 flists of length n may be split into 2 sums as follows:

(defun fdot-select (inds r x)
  (if (consp inds)
      (f+ (f* (nth (car inds) r)
              (nth (car inds) x))
	  (fdot-select (cdr inds) r x))
    (f0)))

(defthm fp-fdot-select
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (sublistp l (ninit n)))
	   (fp (fdot-select l x y)))
  :hints (("Subgoal *1/2" :use ((:instance member-ninit (x (car l)))))))

(local-defthmd fdot-select-delete-1
  (implies (and (fp k) (fp r) (fp d) (fp a)
                (= (f+ k r) d))
	   (equal (f+ k (f+ a r))
	          (f+ a d)))
  :hints (("Goal" :use ((:instance f+assoc (x k) (y a) (z r))
                        (:instance f+comm (x k) (y a))
			(:instance f+assoc (x a) (y k) (z r))))))

(local-defthmd fdot-select-delete
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (sublistp l (ninit n))
                (member k l))
	   (equal (f+ (f* (nth k x) (nth k y))
	              (fdot-select (remove1 k l) x y))
		  (fdot-select l x y)))
  :hints (("Subgoal *1/3" :use ((:instance fdot-select-delete-1 (a (f* (nth (car l) x) (nth (car l) y)))
                                                                (d (fdot-select (cdr l) x y))
								(k (f* (nth k x) (nth k y)))
								(r (fdot-select (remove1-equal k (cdr l)) x y)))
				(:instance member-ninit (x k))
				(:instance member-ninit (x (car l)))
				(:instance sublistp-sublistp (l (remove1-equal k (cdr l))) (m (cdr l)) (n (ninit n)))))))

(defthmd fdot-select-perm
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (sublistp l (ninit n))
                (sublistp m (ninit n))
		(permutationp l m))
	   (equal (fdot-select l x y)
	          (fdot-select m x y)))
  :hints (("subgoal *1/4" :use ((:instance fdot-select-delete (k (car l)) (l m))))
          ("subgoal *1/2" :use ((:instance sublistp-sublistp (l (remove1-equal (car l) m)) (n (ninit n)))))))

(defthmd fdot-select-append
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (sublistp l (ninit n))
                (sublistp m (ninit n)))
	   (equal (fdot-select (append l m) x y)
	          (f+ (fdot-select l x y)
		      (fdot-select m x y))))
  :hints (("Subgoal *1/2" :use ((:instance f+assoc (x (F* (NTH (CAR L) X) (NTH (CAR L) Y)))
                                                   (y (FDOT-SELECT (CDR L) X Y))
						   (z (FDOT-SELECT M X Y)))
				(:instance member-ninit (x (car l)))))))

(local-defun nthcdr-induct (k n)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (natp k) (natp n) (< k n))
      (list (nthcdr-induct (1+ k) n))
    (list k n)))

(local-defthmd fdot-select-nthcdr
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (natp k) (<= k n))
	   (equal (fdot-select (nthcdr k (ninit n)) x y)
	          (fdot (nthcdr k x) (nthcdr k y))))
  :hints (("Goal" :induct (nthcdr-induct k n))))

(defthmd fdot-select-ninit
  (implies (and (natp n) (flistnp x n) (flistnp y n))
	   (equal (fdot-select (ninit n) x y)
	          (fdot x y)))
  :hints (("Goal" :use ((:instance fdot-select-nthcdr (k 0))))))

(local-defthmd sublistp-set-difference
  (sublistp (set-difference-equal l m) l))

(local-defthmd disjointp-set-difference
  (implies (dlistp l)
           (disjointp m (set-difference-equal l m)))
  :hints (("Goal" :use (sublistp-set-difference
                        (:instance common-member-shared (l (set-difference-equal l m)) (m l))))))

(local-defthmd dlistp-set-difference
  (implies (dlistp l)
           (dlistp (set-difference-equal l m)))
  :hints (("Subgoal *1/5" :use ((:instance sublistp-set-difference (l (cdr l)))))))

(local-defthmd dlistp-append-set-difference
  (implies (and (dlistp l) (dlistp m))
           (dlistp (append m (set-difference-equal l m))))
  :hints (("Goal" :use (dlistp-set-difference disjointp-set-difference
                        (:instance dlistp-append (l m) (m (set-difference-equal l m)))))))

(local-defthmd member-append
  (iff (member x (append l m))
       (or (member x l) (member x m))))

(local-defthmd sublistp-append-set-difference
  (implies (dlistp l)
           (sublistp l (append m (set-difference-equal l m))))
  :hints (("Goal" :use ((:instance scex1-lemma (m (append m (set-difference-equal l m))))
                        (:instance member-append (x (scex1 l (append m (set-difference-equal l m))))
			                         (l m)
						 (m (set-difference-equal l m)))
                        (:instance member-set-difference (x (scex1 l (append m (set-difference-equal l m)))))))))

(local-defthmd permp-append-set-difference
  (implies (and (dlistp l) (dlistp m) (sublistp m l))
           (permp (append m (set-difference-equal l m))
	          l))
  :hints (("Goal" :in-theory (enable permp)
                  :use (dlistp-append-set-difference sublistp-set-difference sublistp-append-set-difference))))

(defthmd permutationp-append-set-difference
  (implies (and (dlistp l) (sublistp l (ninit n)) (posp n))
           (permutationp (append l (set-difference-equal (ninit n) l))
	                 (ninit n)))
  :hints (("Goal" :use ((:instance permp-append-set-difference (l (ninit n)) (m l))
                        (:instance permp-permutationp (l (append l (set-difference-equal (ninit n) l))) (m (ninit n)))
			(:instance dlistp-append-set-difference (m l) (l (ninit n)))))))

(defthmd fdot-select-append-set-difference
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (dlistp l) (sublistp l (ninit n)))
           (equal (fdot-select (append l (set-difference-equal (ninit n) l)) x y)
	          (fdot x y)))
  :hints (("Goal" :use (permutationp-append-set-difference fdot-select-ninit
                        (:instance fdot-select-perm (l (append l (set-difference-equal (ninit n) l))) (m (ninit n)))
			(:instance sublistp-set-difference (l (ninit n)) (m l))))))

(defthmd fdot-split
  (implies (and (natp n) (flistnp x n) (flistnp y n)
                (dlistp l) (sublistp l (ninit n)))
	   (equal (fdot x y)
	          (f+ (fdot-select l x y)
		      (fdot-select (set-difference-equal (ninit n) l) x y))))
  :hints (("Goal" :use (fdot-select-append-set-difference
                        (:instance fdot-select-append (m (set-difference-equal (ninit n) l)))
			(:instance sublistp-set-difference (l (ninit n)) (m l))))))

;; The following is a consequence of dlistp-lead-inds and sublistp-lead-inds-ninit

(defthmd fdot-lead-free
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq) (flistnp x n)
                (natp i) (< i q))
           (equal (fdot (row i aq) x)
	          (f+ (fdot-select (lead-inds aq) (row i aq) x)
		      (fdot-select (free-inds aq n) (row i aq) x))))
  :hints (("Goal" :in-theory (enable free-inds)
                  :use ((:instance fdot-split (x (row i aq)) (y x) (l (lead-inds aq)))
                        (:instance dlistp-lead-inds (a aq) (m q))
			(:instance sublistp-lead-inds-ninit (a aq) (m q))
			(:instance flistnp-row (a aq) (m q))))))

;; The term (fdot-select (lead-inds ar) x) may be simplified according to nth-lead-inds and
;; nth-first-nonzero:

(local-defthmd nth-nth-lead-inds-row
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
                (natp i) (< i q) (natp k) (< k q))
	   (equal (nth (nth k (lead-inds aq)) (row i aq))
	          (fdelta i k)))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use ((:instance nth-first-nonzero (a aq) (m q))
                        (:instance num-nonzero-rows-nonzero (a aq) (m q) (i k))
		        (:instance nth-lead-inds (a aq))))))

(local-defthmd nth-row-lead-ins
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
                (natp i) (< i q) (member j (lead-inds aq)))
	   (equal (nth j (row i aq))
	          (if (= j (nth i (lead-inds aq)))
		      (f1) (f0))))
  :hints (("Goal" :use ((:instance len-lead-inds-num-nonzero-rows (a aq))
		        (:instance nth-nth-lead-inds-row (k (index j (lead-inds aq))))
                        (:instance dlistp-lead-inds (a aq) (m q))
                        (:instance nth-dlist-distinct (l (lead-inds aq)) (j (index j (lead-inds aq))))))))

(local-defthmd fdot-select-sublist-lead-inds
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq)                
                (= (num-nonzero-rows aq) q)
		(natp i) (< i q)
		(dlistp l) (sublistp l (lead-inds aq))
		(flistnp x n))
	   (equal (fdot-select l (nth i aq) x)
	          (if (member (nth i (lead-inds aq)) l)
		      (nth (nth i (lead-inds aq)) x)
		    (f0))))
  :hints (("Goal" :induct (dlistp l))
          ("Subgoal *1/1" :in-theory (disable member-nth)
	                  :use ((:instance len-lead-inds-num-nonzero-rows (a aq))
	                        (:instance nth-row-lead-ins (j (car l)))
	                        (:instance sublistp-lead-inds-ninit (a aq) (m q))
				(:instance member-nth (n i) (l (lead-inds aq)))
				(:instance member-ninit (x (car l)))
				(:instance member-ninit (x (nth i (lead-inds aq))))))))

(defthmd fdot-select-lead-inds
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(natp i) (< i q)
		(flistnp x n))
	   (equal (fdot-select (lead-inds aq) (nth i aq) x)
	          (nth (nth i (lead-inds aq)) x)))
  :hints (("Goal" :use ((:instance len-lead-inds-num-nonzero-rows (a aq))
                        (:instance fdot-select-sublist-lead-inds (l (lead-inds aq)))
                        (:instance dlistp-lead-inds (a aq) (m q))))))

;; Combining the lasr result with nth-fmat*-aq-xc, fdot-lead-free, and fdot-select-lead-inds,
;; we have the following reformulation of the equation (nth i (fmat* aq xc)) = (nth i bq):

(local-defthmd equal-rows-lemma-1
  (implies (and (fmatp aq q n) (fmatp bq q 1) (posp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(natp i) (< i q)
		(flistnp x n))
           (iff (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))
		(equal (f+ (nth (nth i (lead-inds aq)) x)
		           (fdot-select (free-inds aq n) (row i aq) x))
		       (car (nth i bq)))))
  :hints (("Goal" :use (nth-fmat*-aq-xc fdot-lead-free fdot-select-lead-inds))))

(local-defthmd f+cancel2
  (implies (and (fp x) (fp y) (fp z))
           (iff (equal (f+ x y) z)
	        (equal x (f+ z (f- y)))))
  :hints (("Goal" :use ((:instance f+left-cancel (x (f+ x y)) (y z) (z (f- y)))
                        (:instance f+assoc (z (f- y)))))))

(defthmd equal-rows-lemma
  (implies (and (fmatp aq q n) (fmatp bq q 1) (posp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistnp x n)
		(natp i) (< i q))
           (iff (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))
		(equal (nth (nth i (lead-inds aq)) x)
		       (f+ (car (nth i bq))
		           (f- (fdot-select (free-inds aq n) (row i aq) x))))))
  :hints (("Goal" :in-theory (enable free-inds)
                  :use (equal-rows-lemma-1
		        (:instance len-lead-inds-num-nonzero-rows (a aq))
		        (:instance num-nonzero-rows<=n (a aq) (m q))
		        (:instance sublistp-lead-inds-ninit (m q) (a aq))
                        (:instance member-ninit (x (nth i (lead-inds aq))))
			(:instance member-sublist (x (nth i (lead-inds aq))) (l (lead-inds aq)) (m (ninit n)))
			(:instance fp-entry (a bq) (m q) (n 1) (j 0))
			(:instance sublistp-set-difference (l (ninit n)) (m (lead-inds aq)))
			(:instance flistnp-row (a aq) (m q))
 			(:instance f+cancel2 (x (nth (nth i (lead-inds aq)) x))
			                     (y (fdot-select (free-inds aq n) (row i aq) x))
					     (z (car (nth i bq))))))))
			
;; Consequently, x is a solution of our system of equations iff this condition holds for
;; all i < q:

(defun solution-test-aux (x aq bq l f k)
  (if (zp k)
      t
    (and (equal (nth (nth (1- k) l) x)
                (f+ (car (nth (1- k) bq))
		    (f- (fdot-select f (nth (1- k) aq) x))))
	 (solution-test-aux x aq bq l f (1- k)))))

(local-defun solution-test-aux-cex (x aq bq l f k)
  (if (zp k)
      ()
    (if (equal (nth (nth (1- k) l) x)
               (f+ (car (nth (1- k) bq))
		   (f- (fdot-select f (nth (1- k) aq) x))))
	(solution-test-aux-cex x aq bq l f (1- k))
      (1- k))))

(local-defthmd solution-test-aux-1
  (implies (and (natp k) (solution-test-aux x aq bq l f k) (natp i) (< i k))
           (equal (nth (nth i l) x)
                  (f+ (car (nth i bq))
		      (f- (fdot-select f (nth i aq) x)))))
  :hints (("Goal" :induct (solution-test-aux x aq bq l f k))))

(local-defthmd solution-test-aux-2
  (implies (and (natp k) (not (solution-test-aux x aq bq l f k)))
           (let ((i (solution-test-aux-cex x aq bq l f k)))
	     (and (natp i) (< i k)
	          (not (equal (nth (nth i l) x)
                       (f+ (car (nth i bq))
		           (f- (fdot-select f (nth i aq) x)))))))))

(local-defthmd solution-test-aux-3
  (implies (and (fmatp aq q n) (fmatp bq q 1) (natp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistnp x n)
                (solution-test-aux x aq bq (lead-inds aq) (free-inds aq n) q)
		(natp i) (< i q))
           (equal (nth i (fmat* aq (col-mat x)))
	                 (nth i bq)))
  :hints (("Goal" :use (equal-rows-lemma
                        (:instance solution-test-aux-1 (l (lead-inds aq)) (f (free-inds aq n)) (k q))))))

(local-defthmd solution-test-aux-4
  (implies (and (fmatp aq q n) (fmatp bq q 1) (natp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistnp x n)
                (not (solution-test-aux x aq bq (lead-inds aq) (free-inds aq n) q)))
           (let ((i (solution-test-aux-cex x aq bq (lead-inds aq) (free-inds aq n) q)))
	     (and (natp i) (< i q)
	          (not (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))))))
  :hints (("Goal" :use ((:instance equal-rows-lemma (i (solution-test-aux-cex x aq bq (lead-inds aq) (free-inds aq n) q)))
                        (:instance solution-test-aux-2 (l (lead-inds aq)) (f (free-inds aq n)) (k q))))))

(local-defthmd solution-test-aux-5
  (implies (and (fmatp aq q n) (fmatp bq q 1) (posp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistnp x n))
	   (iff (solution-test-aux x aq bq (lead-inds aq) (free-inds aq n) q)
	        (equal (fmat* aq (col-mat x))
	               bq)))
  :hints (("Goal" :in-theory (disable fmatp-fmat*)
	          :use (solution-test-aux-4
			(:instance fmatp-fmat* (a aq) (b (col-mat x)) (m q) (p 1))
                        (:instance nth-diff-diff (x (fmat* aq (col-mat x))) (y bq))
                        (:instance solution-test-aux-3 (i (nth-diff (fmat* aq (col-mat x)) bq)))))))

;; The case q = 0 must be handled separately:

(local-defthm solution-test-aux-0
  (solution-test-aux x aq bq l f 0))

(local-defthmd fmat*-0
  (implies (and (fmatp a 0 n) (fmatp x n 1) (fmatp b 0 1))
           (equal (fmat* a x) b))
  :hints (("Goal" :in-theory (enable fmat* fmatp))))

(in-theory (disable solution-test-aux))

(local-defthmd solution-test-aux-6
  (let* ((ar (row-reduce a))
         (br (fmat* (row-reduce-mat a) (col-mat b)))
	 (q (num-nonzero-rows ar))
	 (aq (first-rows q ar))
	 (bq (first-rows q br))
	 (l (lead-inds aq))
	 (f (free-inds aq n)))
    (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
                  (solvablep a b))
             (iff (solutionp x a b)
                  (solution-test-aux x aq bq l f q))))
  :hints (("Goal" :in-theory (e/d (fmatp-first-rows fmatp-row-reduce-mat row-echelon-p-row-reduce fmatp-row-reduce)
                                  (fmatp-fmat*))
                  :use (reduce-linear-equations row-ops-mat-row-reduce
		        (:instance fmat*-0 (a (first-rows (num-nonzero-rows (row-reduce a)) (row-reduce a)))
			                   (x (col-mat x))
					   (b (first-rows (num-nonzero-rows (row-reduce a))
						          (fmat* (row-reduce-mat a) (col-mat b)))))
		        (:instance first-rows-rank (ar (row-reduce a)))
			(:instance num-nonzero-rows<=m (a (row-reduce a)))
                        (:instance first-rows-linear-equations (ar (row-reduce a)) (br (fmat* (row-reduce-mat a) (col-mat b)))
			                                       (xc (col-mat x)))
                        (:instance solution-test-aux-5 (q (num-nonzero-rows (row-reduce a)))
			                               (aq (first-rows (num-nonzero-rows (row-reduce a)) (row-reduce a)))
						       (bq (first-rows (num-nonzero-rows (row-reduce a))
						                       (fmat* (row-reduce-mat a) (col-mat b)))))
			(:instance fmatp-fmat* (a (row-reduce-mat a)) (b (col-mat b)) (n m) (p 1))))))
                        
(defund solution-test (x a b n)
  (let* ((ar (row-reduce a))
         (br (fmat* (row-reduce-mat a) (col-mat b)))
         (q (num-nonzero-rows ar))
         (aq (first-rows q ar))
         (bq (first-rows q br))
         (lead-inds (lead-inds aq))
         (free-inds (free-inds aq n)))
    (solution-test-aux x aq bq lead-inds free-inds q)))
  
(defthmd linear-equations-solvable-case
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
                (solvablep a b))
           (iff (solutionp x a b)
                (solution-test x a b n)))
  :hints (("Goal" :in-theory (enable solution-test)
		  :use (solution-test-aux-6))))


;; Note that if (len l) = n and f = nil, then the equation

;;   (nth (nth i l) x) = (f+ (car (nth i bq)) (f- (fdot-select f (nth i aq) x)))

;; reduces to

;;   (nth i x) = (car (nth i bq),

;; (solution-test-aux x aq bq l f q) reduces to x = (col 0 bq), and linear-equations-solvable-case
;; reduces to the earlier result linear-equations-unique-solution-case.

;; Otherwise, the entries of x corresponding to the indices in (lead-inds aq) are determined
;; by the entries corresponding to (free-inds aq n).  Thus, there is a unique solution
;; corresponding to every assignment of values to the latter set of entries, and hence an
;; infinite number of solutions.  We shall revisit this result later in tconnection with the 
;; vector space of solutions of a homogeneous system of equations.


;;--------------------------------------------------------------------------------------------------

;; A couple of results that we need in our treatment of linear dependent vectors.
;; I should have proved them earlier:

(defthmd lead-inds-first-nonzero-rows
  (implies (and (fmatp a m n) (posp m) (posp n))
           (equal (lead-inds (first-rows (num-nonzero-rows a) a))
	          (lead-inds a)))
  :hints (("Goal" :in-theory (enable fmatp))))

(local-defthmd nth-col-lead-inds-1
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp i) (< i (num-nonzero-rows a)) (member j (lead-inds a)))
	   (equal (nth j (row i a))
	          (if (= j (nth i (lead-inds a)))
		      (f1) (f0))))
  :hints (("Goal" :use (len-lead-inds-bound len-lead-inds-num-nonzero-rows lead-inds-first-nonzero-rows
                        (:instance first-rows-rank (ar a))
                        (:instance nth-row-lead-ins (aq (first-rows (num-nonzero-rows a) a))
				                    (q (num-nonzero-rows a)))
			(:instance nth-first-rows (q (num-nonzero-rows a)))))))			

(local-defthmd nth-col-lead-inds-2
  (implies (and (fmatp a m n) (row-echelon-p a) (posp m) (posp n)
		(natp i) (< i (num-nonzero-rows a)) (natp k) (< k m))
	   (equal (nth k (col (nth i (lead-inds a)) a))
		  (fdelta i k)))
  :hints (("Goal" :in-theory (disable member-sublist nth-flistn0)
                  :use (len-lead-inds-num-nonzero-rows sublistp-lead-inds-ninit
                        (:instance nth-col (i k) (j (nth i (lead-inds a))))
			(:instance num-nonzero-rows-nonzero (i k))
			(:instance flist0p-flistn0-len (x (nth k a)))
			(:instance nth-flistn0 (i (nth i (lead-inds a))))
			(:instance member-ninit (x (nth i (lead-inds a))))
			(:instance member-sublist (x (nth i (lead-inds a))) (l (lead-inds a)) (m (ninit n)))
                        (:instance nth-col-lead-inds-1 (i k) (j (nth i (lead-inds a))))))))

(defthmd nth-col-lead-inds
  (implies (and (fmatp a m n) (row-echelon-p a) (posp m) (posp n)
		(natp i) (< i (row-rank a)) (natp k) (< k m))
	   (equal (nth k (col (nth i (lead-inds a)) a))
		  (fdelta i k)))
  :hints (("Goal" :in-theory (enable row-reduce-row-echelon-p row-rank)
                  :use (nth-col-lead-inds-2))))

(defthmd nth-lead-inds-bound
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp k) (< k (len (lead-inds a))))
           (and (natp (nth k (lead-inds a)))
	        (< (nth k (lead-inds a)) n)))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (nth-lead-inds num-nonzero-rows<=m
		        (:instance num-nonzero-rows-nonzero (i k))
			(:instance first-nonzero-nonzero (x (nth k a)))
			(:instance flistnp-row (i k))
			(:instance not-flist0p-row (i k))))))
