(in-package "DM")

(include-book "field")
(local (include-book "support/fmat"))

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
		  (not (equal (entry i j a) (entry i j b)))))))

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
		  (fmat-add b a))))

(defthmd fmat-add-assoc
  (implies (and (fmatp a m n) (fmatp b m n) (fmatp c m n))
           (equal (fmat-add a (fmat-add b c))
		  (fmat-add (fmat-add a b) c))))

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

(defthmd fmatp-transpose
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (fmatp (transpose-mat a) n m)))

(defthm nth-transpose-fmat
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp i) (< i n))
	   (equal (nth i (transpose-mat a))
		  (col i a))))

(defthm transpose-fmat-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a))))

(defthm transpose-fmat-2
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (transpose-mat (transpose-mat a))
	          a)))

(defthmd col-transpose-fmat
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp j) (< j m))
	   (equal (col j (transpose-mat a))
	          (row j a))))

;; Replace kth column of a with r:

(defund replace-col (a k r)
  (transpose-mat (replace-row (transpose-mat a) k r)))

(defthm fmatp-replace-col
  (implies (and (fmatp a m n) (posp m) (posp n) (natp k) (< k n) (flistnp r m))
           (fmatp (replace-col a k r) m n)))

(defthm fmat-col-replace-col
  (implies (and (fmatp a m n) (posp m) (posp n)
		(natp k) (< k n) (natp j) (< j n)
		(flistnp r m))
           (equal (col j (replace-col a k r))
	          (if (= j k)
		      r
		    (col j a)))))

;; An important lemma in the proof of associativity of matrix multiplication:
;; If (fmatp a m n), then (fmat-sum (transpose-mat a)) = (fmat-sum a).
;; This holds trivially if either m = 0 or n = 0:

(defthm fmat-sum-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum a) (f0))))

(defthm fmat-sum-transpose-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum (transpose-mat a))
	          (f0))))
		        
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

(defthmd fmatp-strip-mat
  (implies (and (posp m) (posp n) (fmatp a m n))
           (fmatp (strip-mat a) (1- m) (1- n))))

(defthmd sum-fmat-strip-mat
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
		  (f+ (entry 0 0 a)
		      (f+ (f+ (flist-sum (cdr (row 0 a)))
			      (flist-sum (cdr (col 0 a))))
			  (fmat-sum (strip-mat a)))))))

;; Since (row 0 a) = (col 0 (transpose-mat a)) and (col 0 a) = (row 0 (transpose-mat a)), we have
;; the rollowing:

(defthmd sum-fmat-strip-mat-equal
  (implies (and (posp m) (posp n) (fmatp a m n)
                (equal (fmat-sum (strip-mat a)) (fmat-sum (strip-mat (transpose-mat a)))))
	   (equal (fmat-sum (transpose-mat a))
		  (fmat-sum a))))

;; If either m = 0 or n = 0, then the hypothesis of sum-fmat-strip-mat-equal holds trivially:

(defthm fmat-sum-strip-mat-0
  (implies (and (posp m) (posp n) (or (= m 1) (= n 1)) (fmatp a m n))
           (and (equal (fmat-sum (strip-mat a)) (f0))
	        (equal (fmat-sum (strip-mat (transpose-mat a))) (f0)))))

(defthmd strip-fmat-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp i) (natp j) (< i (1- m)) (< j (1- n)))
	   (equal (entry i j (strip-mat a))
		  (entry (1+ i) (1+ j) a))))

;; In the remaining case, we have the rollowing:

(defthmd transpose-strip-mat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (fmatp a m n))
	   (equal (transpose-mat (strip-mat a))
		  (strip-mat (transpose-mat a)))))

;; The result rollows by induction:

(defthmd sum-fmat-transpose
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (equal (fmat-sum (transpose-mat a))
		  (fmat-sum a))))


;;----------------------------------------------------------------------------------------
;; Matrix Multiplication
;;----------------------------------------------------------------------------------------

;; Dot product of 2 lists of field elements of the same length:

(defun fdot (x y)
  (if (consp x)
      (f+ (f* (car x) (car y))
          (fdot (cdr x) (cdr y)))
    (f0)))

(defthm fp-fdot
  (implies (and (flistnp x n) (flistnp y n))
           (fp (fdot x y))))

(defthm fdot-flistn0
  (implies (and (natp n) (flistnp x n))
           (equal (fdot (flistn0 n) x)
	          (f0))))

(defthmd fdot-comm
  (implies (and (flistnp x n) (flistnp y n))
           (equal (fdot x y) (fdot y x))))

(defthmd fdot-flist-add
  (implies (and (flistnp x n) (flistnp y n) (flistnp z n))
	   (equal (fdot (flist-add x y) z)
		  (f+ (fdot x z) (fdot y z)))))

(defthmd fdot-flist-add-comm
  (implies (and (flistnp x n) (flistnp y n) (flistnp z n))
	   (equal (fdot z (flist-add x y))
		  (f+ (fdot z x) (fdot z y)))))
					   
(defthmd fdot-flist-scalar-mul
  (implies (and (flistnp x n) (flistnp y n) (fp c))
	   (equal (fdot (flist-scalar-mul c x) y)
		  (f* c (fdot x y)))))

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
           (fmatp (fmat* a b) m p)))

(defthmd nth-fmat*
  (implies (and (natp m) (fmatp a m n) (natp i) (< i m))
           (equal (nth i (fmat* a b))
	          (fdot-list (nth i a) (transpose-mat b)))))

(defthmd fmat*-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* a b))
	          (fdot (row i a) (col j b)))))

(defthmd fmat*-dist-1
  (implies (and (posp m) (posp n) (posp p) (fmatp a1 m n) (fmatp a2 m n) (fmatp b n p))
	   (equal (fmat* (fmat-add a1 a2) b)
		  (fmat-add (fmat* a1 b) (fmat* a2 b)))))
			
(defthmd fmat*-dist-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b1 n p) (fmatp b2 n p))
	   (equal (fmat* a (fmat-add b1 b2))
		  (fmat-add (fmat* a b1) (fmat* a b2)))))

(defthmd fmat*-fmat-scalar-mul-1
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c))
	   (equal (fmat* (fmat-scalar-mul c a) b)
		  (fmat-scalar-mul c (fmat* a b)))))

(defthmd fmat*-fmat-scalar-mul-2
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p) (fp c))
	   (equal (fmat* a (fmat-scalar-mul c b))
		  (fmat-scalar-mul c (fmat* a b)))))

;; Transpose of a product:

(defthmd transpose-fmat*
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p))
	   (equal (transpose-mat (fmat* a b))
	          (fmat* (transpose-mat b) (transpose-mat a)))))

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

(defthm nth-funit
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i n))
           (equal (nth i (funit j n))
	          (fdelta i j))))

;; Dot product of (funit j n) with an flist of length n:

(defthm fdot-funit
  (implies (and (posp n) (flistnp x n) (natp j) (< j n))
           (equal (fdot (funit j n) x)
	          (nth j x))))

(defthm fdot-funit-comm
  (implies (and (posp n) (flistnp x n) (natp j) (< j n))
           (equal (fdot x (funit j n))
	          (nth j x))))

;; nxn identity matrix:

(defun id-fmat-aux (j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (funit j n) (id-fmat-aux (1+ j) n))
    ()))

(defund id-fmat (n)
  (id-fmat-aux 0 n))

(defthm fmatp-id-fmat
  (implies (posp n)
           (fmatp (id-fmat n) n n)))

(defthm nth-id-fmat
  (implies (and (posp n) (natp i) (< i n))
	   (equal (nth i (id-fmat n))
		  (funit i n))))

(defthmd entry-id-fmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (id-fmat n))
	          (fdelta i j))))

(defthmd transpose-id-fmat
  (implies (natp n)
           (equal (transpose-mat (id-fmat n))
	          (id-fmat n))))

(defthm col-id-fmat
  (implies (and (natp n) (natp j) (< j n))
           (equal (col j (id-fmat n))
	          (funit j n))))

;; (id-fmat n) is a right identity:

(defthmd id-fmat-right
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* a (id-fmat n))
	          a)))

;; (id-fmat n) is a left identity:

(defthmd id-fmat-left
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* (id-fmat m) a)
	          a)))
							   
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

(defthmd fmatp-fmat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (fmat12 a b c i j) n p)))

;; We derive the rollowing expression for each entry of this matrix:

(defthmd fmat12-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (entry r s (fmat12 a b c i j))
	          (f* (f* (entry i r a) (entry r s b)) (entry s j c)))))

;; The sum of these entries:

(defthm fmat-sum-fmat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat12 a b c i j))
	          (entry i j (fmat* a (fmat* b c))))))

;; The matrix (fmat21 a b c i j) similarly relates to (entry i j (fmat* (fmat* a b) c):

(defund fmat21 (a b c i j)
  (flist-scalar-mul-list (col j c)
		         (flist-mul-list (row i a) (transpose-mat b))))

(defthmd fmatp-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (fmat21 a b c i j) p n)))

(defthmd fmat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (fmat21 a b c i j))
	          (f* (entry i s a) (f* (entry s r b) (entry r j c))))))

(defthm fmat-sum-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (fmat21 a b c i j))
	          (entry i j (fmat* (fmat* a b) c)))))

;; Combine fmat21-entry and fmat12-entry:

(defthmd fmat12-fmat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (fmat21 a b c i j))
	          (entry s r (fmat12 a b c i j)))))

;; Apply transpose-fmat-entry:

(defthmd fmat12-transpose-fmat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (transpose-mat (fmat12 a b c i j))
	          (fmat21 a b c i j))))

;; By sum-fmat-transpose, (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)),
;; and the result follows:

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
