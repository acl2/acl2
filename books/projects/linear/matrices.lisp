(in-package "DM")

(include-book "field")
(include-book "projects/groups/groups" :dir :system)
(local (include-book "support/matrices"))

;;----------------------------------------------------------------------------------------
;; Matrices of Field Elements
;;----------------------------------------------------------------------------------------

;; mxn matrix over F:

(defun fmatp (a m n)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (null a)
    (and (consp a)
	 (flistp (car a) n)
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

(defthm flistp-row
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m))
           (flistp (row i a) n)))  

(defthm len-row
  (implies (and (natp m) (natp n) (fmatp a m n)
	        (natp i) (< i m))
	   (equal (len (row i a))
		  n)))

;; jth column of a:

(defun col (j a)
  (if (consp a)
      (cons (nth j (car a))
            (col j (cdr a)))
    ()))

(defthm flistp-col
  (implies (and (natp m) (natp n) (fmatp a m n)
		(natp j) (< j n))
	   (flistp (col j a) m)))

(defthm len-col
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (equal (len (col j a))
		  m)))

;; The entry of a matrix in row i and column j:

(defun entry (i j a)
  (nth j (nth i a)))

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

;; To show that 2 matrices of the same dimensions are equal, it suffices to show that
;; corresponding entries are equal.  That is, if 2 mxn matrices are not equal, then some
;; pair of corresponding entries are not equal:

(defund entry-diff (a b)
  (let* ((i (nth-diff a b))
	 (j (nth-diff (row i a) (row i b))))
    (cons i j)))

(defthmd entry-diff-lemma
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

(in-theory (disable (fmat-sum)))

(defthm fp-fmat-sum
  (implies (fmatp a m n)
           (fp (fmat-sum a))))

;;----------------------------------------------------------------------------------------
;; Transpose of a Matrix
;;----------------------------------------------------------------------------------------

;; The transpose of a matrix is the list of its columns:

(defun transpose-aux (a j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (col j a) (transpose-aux a (1+ j) n))
    ()))

(defund transpose (a)
  (transpose-aux a 0 (len (car a))))

(defthmd fmatp-transpose
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (fmatp (transpose a) n m)))

(defthm nth-transpose
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp i) (< i n))
	   (equal (nth i (transpose a))
		  (col i a))))

(defthm transpose-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose a))
		  (entry i j a))))

(defthm transpose-transpose
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (transpose (transpose a))
	          a)))

(defthmd col-transpose
  (implies (and (posp m) (posp n) (fmatp a m n)
                (natp j) (< j m))
	   (equal (col j (transpose a))
	          (row j a))))

;; An important lemma in the proof of associativity of matrix multiplication:
;; If (fmatp a m n), then (fmat-sum (transpose a)) = (fmat-sum a).
;; This holds trivially if either m = 0 or n = 0:

(defthm fmat-sum-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum a) (f0))))

(defthm fmat-sum-transpose-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (fmatp a m n))
           (equal (fmat-sum (transpose a))
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

(defthmd sum-mat-strip-mat
  (implies (and (posp m) (posp n) (fmatp a m n))
	   (equal (fmat-sum a)
		  (f+ (entry 0 0 a)
		      (f+ (f+ (flist-sum (cdr (row 0 a)))
			      (flist-sum (cdr (col 0 a))))
			  (fmat-sum (strip-mat a)))))))

;; Since (row 0 a) = (col 0 (transpose a)) and (col 0 a) = (row 0 (transpose a)), we have
;; the following:

(defthmd sum-mat-strip-mat-equal
  (implies (and (posp m) (posp n) (fmatp a m n)
                (equal (fmat-sum (strip-mat a)) (fmat-sum (strip-mat (transpose a)))))
	   (equal (fmat-sum (transpose a))
		  (fmat-sum a))))

;; If either m = 0 or n = 0, then the hypothesis of sum-mat-strip-mat-equal holds trivially:

(defthm fmat-sum-strip-mat-0
  (implies (and (posp m) (posp n) (or (= m 1) (= n 1)) (fmatp a m n))
           (and (equal (fmat-sum (strip-mat a)) (f0))
	        (equal (fmat-sum (strip-mat (transpose a))) (f0)))))

(defthmd strip-mat-entry
  (implies (and (posp m) (posp n) (fmatp a m n)
		(natp i) (natp j) (< i (1- m)) (< j (1- n)))
	   (equal (entry i j (strip-mat a))
		  (entry (1+ i) (1+ j) a))))

;; In the remaining case, we have the following:

(defthmd transpose-strip-mat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (fmatp a m n))
	   (equal (transpose (strip-mat a))
		  (strip-mat (transpose a)))))

;; The result follows by induction:

(defthmd sum-mat-transpose
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (equal (fmat-sum (transpose a))
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
  (implies (and (flistp x n) (flistp y n))
           (fp (fdot x y))))

(defthm fdot-flist0
  (implies (and (natp n) (flistp x n))
           (equal (fdot (flist0 n) x)
	          (f0))))

(defthmd fdot-comm
  (implies (and (flistp x n) (flistp y n))
           (equal (fdot x y) (fdot y x))))

(defthmd fdot-flist-add
  (implies (and (flistp x n) (flistp y n) (flistp z n))
	   (equal (fdot (flist-add x y) z)
		  (f+ (fdot x z) (fdot y z)))))

(defthmd fdot-flist-add-comm
  (implies (and (flistp x n) (flistp y n) (flistp z n))
	   (equal (fdot z (flist-add x y))
		  (f+ (fdot z x) (fdot z y)))))
					   
(defthmd fdot-flist-scalar-mul
  (implies (and (flistp x n) (flistp y n) (fp c))
	   (equal (fdot (flist-scalar-mul c x) y)
		  (f* c (fdot x y)))))

;; List of dot products of an flist x with the elements of a list of flists l:

(defun fdot-list (x l)
  (if (consp l)
      (cons (fdot x (car l))
            (fdot-list x (cdr l)))
    ()))

(defthm flistp-fdot-list
  (implies (and (fmatp l m n) (flistp x n))
           (flistp (fdot-list x l) m)))

(defthm nth-fdot-list
  (implies (and (natp j) (< j (len l)))
           (equal (nth j (fdot-list x l))
	          (fdot x (nth j l)))))

;; Product of mxn matrix a and nxp matrix b:

(defund fmat* (a b)
  (if (consp a)
      (cons (fdot-list (car a) (transpose b))
            (fmat* (cdr a) b))
    ()))

(defthm fmatp-fmat*
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (posp n) (posp p) )
           (fmatp (fmat* a b) m p)))

(defthmd nth-fmat*
  (implies (and (natp m) (fmatp a m n) (natp i) (< i m))
           (equal (nth i (fmat* a b))
	          (fdot-list (nth i a) (transpose b)))))

(defthmd fmat*-entry
  (implies (and (posp m) (posp n) (posp p) (fmatp a m n) (fmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (fmat* a b))
	          (fdot (row i a) (col j b)))))

;; Some algebraic properties:

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
	   (equal (transpose (fmat* a b))
	          (fmat* (transpose b) (transpose a)))))

;; The definition of the nxn identify matrix is based on that of an flist of length n
;; with (f1) at index j and (f0) elsewhere:

(defun unit (j n)
  (if (zp n)
      ()
    (if (zp j)
        (cons (f1) (flist0 (1- n)))
      (cons (f0) (unit (1- j) (1- n))))))

(defthm flistp-unit
  (flistp (unit j n) n))

;; The Kronecker delta function:

(defun delta (i j)
  (if (= i j) (f1) (f0)))

(defthm nth-unit
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i n))
           (equal (nth i (unit j n))
	          (delta i j))))

;; Dot product of (unit j n) with an flist of length n:

(defthm fdot-unit
  (implies (and (posp n) (flistp x n) (natp j) (< j n))
           (equal (fdot (unit j n) x)
	          (nth j x))))

(defthm fdot-unit-comm
  (implies (and (posp n) (flistp x n) (natp j) (< j n))
           (equal (fdot x (unit j n))
	          (nth j x))))

;; nxn identity matrix:

(defun id-mat-aux (j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (unit j n) (id-mat-aux (1+ j) n))
    ()))

(defund id-mat (n)
  (id-mat-aux 0 n))

(defthm fmatp-id-mat
  (implies (posp n)
           (fmatp (id-mat n) n n)))

(defthm nth-id-mat
  (implies (and (posp n) (natp i) (< i n))
	   (equal (nth i (id-mat n))
		  (unit i n))))

(defthmd entry-id-mat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (id-mat n))
	          (delta i j))))

(defthmd transpose-id-mat
  (implies (natp n)
           (equal (transpose (id-mat n))
	          (id-mat n))))

(defthm col-id-mat
  (implies (and (natp n) (natp j) (< j n))
           (equal (col j (id-mat n))
	          (unit j n))))

;; (id-mat n) is a right identity:

(defthmd id-mat-right
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* a (id-mat n))
	          a)))

;; (id-mat n) is a left identity:

(defthmd id-mat-left
  (implies (and (posp m) (posp n) (fmatp a m n))
           (equal (fmat* (id-mat m) a)
	          a)))
							   
;; Associativity:

;; Let a, b, and c be matrices of dimensions mxn, nxp, and pxq, respectively.  Then
;; (fmat* a (fmat* b c)) and (fmat* (fmat* a b) c)) are both mxp matrices.  Our
;; objective is to prove that they are equal.  Let 0 <= i < m and 0 <= j < q.  It will
;; suffice to show that

;;    (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)).

;; Applying fmat*-entry and expanding fdot, we find that both sides of this equation
;; are sums of n*p 3-way products.

;; We shall construct an nxp matrix of 3-way products, (mat12 a b c i j), such that

;;    (entry i j (fmat* a (fmat* b c))) = (fmat-sum (mat12 a b c i j))

;; and a pxn matrix of 3-way products, (mat21 a b c), such that

;;    (entry i j (fmat* (fmat* a b) c)) = (fmat-sum (mat21 a b c i j)).

;; We shall show that (mat21 a b c i j) = (transpose (mat12 a b c i j)) and apply
;; fmat-sum-transpose to conclude that

;;    (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)).

;; The entry on the left is the dot product of a row of a and a column of (fmat* b c),
;; and each entry of this column is a dot product of a row of b and a column of c.
;; This leads to the definition of the nxp matrix of 3-way products, (mat12 a b c i j):

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

(defund mat12 (a b c i j)
  (flist-scalar-mul-list (row i a)
	   	         (flist-mul-list (col j c) b)))

(defthmd fmatp-mat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (mat12 a b c i j) n p)))

;; We derive the following expression for each entry of this matrix:

(defthmd mat12-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (entry r s (mat12 a b c i j))
	          (f* (f* (entry i r a) (entry r s b)) (entry s j c)))))

;; The sum of these entries:

(defthm fmat-sum-mat12
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (mat12 a b c i j))
	          (entry i j (fmat* a (fmat* b c))))))

;; The matrix (mat21 a b c i j) similarly relates to (entry i j (fmat* (fmat* a b) c):

(defund mat21 (a b c i j)
  (flist-scalar-mul-list (col j c)
		         (flist-mul-list (row i a) (transpose b))))

(defthmd fmatp-mat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (fmatp (mat21 a b c i j) p n)))

(defthmd mat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (mat21 a b c i j))
	          (f* (entry i s a) (f* (entry s r b) (entry r j c))))))

(defthm fmat-sum-mat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (fmat-sum (mat21 a b c i j))
	          (entry i j (fmat* (fmat* a b) c)))))

;; Combine mat21-entry and mat12-entry:

(defthmd mat12-mat21-entry
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (mat21 a b c i j))
	          (entry s r (mat12 a b c i j)))))

;; Apply transpose-entry:

(defthmd mat12-transpose-mat21
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (transpose (mat12 a b c i j))
	          (mat21 a b c i j))))

;; By sum-mat-transpose, (entry i j (fmat* a (fmat* b c))) = (entry i j (fmat* (fmat* a b) c)),
;; and the result follows:

(defthmd fmat*-assoc
  (implies (and (fmatp a m n) (fmatp b n p) (fmatp c p q) (posp m) (posp n) (posp p) (posp q))
           (equal (fmat* a (fmat* b c))
	          (fmat* (fmat* a b) c))))


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
  (implies (and (flistp x n) (not (flist0p x)))
           (let ((i (first-nonzero x)))
	     (and (natp i)
	          (< i n)
		  (fp (nth i x))
		  (not (= (nth i x) (f0)))))))

(defthmd first-nonzero-first
  (implies (and (flistp x n) (not (flist0p x))
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

(defthmd row-with-nonzero-at-least-index-nil
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m)
                (null (row-with-nonzero-at-least-index a m k))
		(natp j) (<= k j) (< j m))
	   (flist0p (nth j a))))

(defthmd row-with-nonzero-at-least-index-non-nil
  (let ((i (row-with-nonzero-at-least-index a m k)))
    (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) i)
             (and (natp i) (<= k i) (< i m) (not (flist0p (nth i a)))
		  (implies (and (natp j) (<= k j) (< j m))
	                   (or (flist0p (nth j a))
                               (<= (first-nonzero (nth i a))
		                   (first-nonzero (nth j a)))))))))

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

(defund row-echelon-p (a)
  (row-echelon-p-aux a (len a) (len a)))

;; Properties of row echelon matrices:

(defthmd flist0p-row
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (flist0p (nth k a))
                (natp i) (< k i) (< i m))
           (flist0p (nth i a))))

(defthmd first-nonzero-row-bound
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (not (flist0p (nth k a))))
	   (and (natp (first-nonzero (nth k a)))
	        (< (first-nonzero (nth k a)) n))))

(defthmd not-flist0p-row
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (not (flist0p (nth k a)))
                (natp i) (< k i) (< i m) (not (flist0p (nth i a))))
           (< (first-nonzero (nth k a))
	      (first-nonzero (nth i a)))))

(defthmd nth-first-nonzero
  (implies (and (fmatp a m n) (natp m) (natp n) (row-echelon-p a)
                (natp k) (< k m) (not (flist0p (nth k a)))
                (natp i) (< i m))
	   (equal (nth (first-nonzero (nth k a))
	               (nth i a))
		  (delta i k))))


;; Next, we define a process that converts a matrix to row-echelon form by applying
;; a sequence of "elementary row operations".  These are based on the following
;; function, which replaces row k of a with r:

(defun replace-row (a k r)
  (if (zp k)
      (cons r (cdr a))
    (cons (car a) (replace-row (cdr a) (1- k) r))))

(defthm fmatp-replace-row
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) (flistp r n))
           (fmatp (replace-row a k r) m n)))

(defthmd nth-replace-row
  (implies (and (natp k) (< k (len a)) (natp j) (< j (len a)))
           (equal (nth j (replace-row a k r))
	          (if (= j k)
		      r
		    (nth j a)))))

;; 3 types of elementary row operations:

;; (1) Multiply row k by c:

(defund ero1 (a c k)
  (replace-row a k (flist-scalar-mul c (nth k a))))

(defthm fmatp-ero1
  (implies (and (fmatp a m n) (natp m) (natp n) (natp k) (< k m) (fp c))
           (fmatp (ero1 a c k) m n)))

(defthmd nth-ero1
  (implies (and (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero1 a c k))
	          (if (= i k)
		      (flist-scalar-mul c (nth k a))
		    (nth i a)))))

;; (2) Add multiple of row j to row k:

(defund ero2 (a c j k)
  (replace-row a k (flist-add (flist-scalar-mul c (nth j a)) (nth k a))))

(defthm fmatp-ero2
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j m) (natp k) (< k m) (fp c))
           (fmatp (ero2 a c j k) m n)))

(defthmd nth-ero2
  (implies (and (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero2 a c j k))
	          (if (= i k)
		      (flist-add (flist-scalar-mul c (nth j a)) (nth k a))
		    (nth i a)))))

;; (3) Interchange rows j and k:

(defund ero3 (a j k)
  (replace-row (replace-row a k (nth j a)) j (nth k a)))

(defthm fmatp-ero3
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j m) (natp k) (< k m))
           (fmatp (ero3 a j k) m n)))

(defthmd nth-ero3
  (implies (and (natp j) (< j (len a)) (natp k) (< k (len a)) (natp i) (< i (len a)))
           (equal (nth i (ero3 a j k))
	          (if (= i k)
		      (nth j a)
		    (if (= i j)
		        (nth k a)
		      (nth i a))))))

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

(defthm fmatp-clear-column
  (implies (and (fmatp a m n) (natp m) (natp n) (natp j) (< j n) (natp k) (< k m))
           (fmatp (clear-column a k j m) m n)))

(defthmd column-clear-p-clear-column
  (implies (and (fmatp a m n) (natp m ) (natp n)
                (natp k) (< k m) (natp j) (< j n)
		(= (nth j (nth k a)) (f1)))
	   (column-clear-p (clear-column a k j m) k j m)))

;; Assume (row-echelon-p-aux a m k), where k < m and that i = (row-with-nonzero-at-least-index a m k)
;; is non-NIL.  Let j = (first-nonzero (nth i a).  The following function performs the next step
;; of the reduction, producing a matrix a' satisfying (row-echelon-p-aux a' m (1+ k)):

(defund row-reduce-step (a m k i j)
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

(defthmd fmatp-row-reduce-aux
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (<= k m))
	   (fmatp (row-reduce-aux a m k) m n)))

(defthmd row-echelon-p-aux-row-reduce-aux
  (implies (and (natp m) (natp n) (fmatp a m n)
		(natp k) (<= k m) (row-echelon-p-aux a m k))
	   (row-echelon-p-aux (row-reduce-aux a m k) m m)))

;; Convert a to row-echelon form:

(defund row-reduce (a)
  (row-reduce-aux a (len a) 0))

(defthmd row-echelon-p-row-reduce
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (row-echelon-p (row-reduce a))))

(defthmd fmatp-row-reduce
  (implies (and (natp m) (natp n) (fmatp a m n))
	   (fmatp (row-reduce a) m n)))

;; If a is already in row-echelon form, then (row-reduce a) = a:

(defthmd row-reduce-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp a m n) (row-echelon-p a))
	   (equal (row-reduce a) a)))

;; The row rank of a is the number of nonzero rows of (row-reduce a):

(defun num-nonzero-rows (a)
  (if (consp a)
      (if (flist0p (car a))
          0
	(1+ (num-nonzero-rows (cdr a))))
    0))

(defthmd num-nonzero-rows-nonzero
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp i) (< i m))
	   (iff (flist0p (nth i a))
	        (>= i (num-nonzero-rows a)))))

(defun row-rank (a)
  (num-nonzero-rows (row-reduce a)))

;; Obviously, the row-rank of an mxn matrix cannot exceed m:

(defthmd num-nonzero-rows<=m
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (num-nonzero-rows a)
               m)))

(defthmd row-rank<=m
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (row-rank a)
               m)))

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
               m)))

(defthmd nth-lead-inds
  (implies (and (natp k) (< k (len (lead-inds a))))
           (equal (nth k (lead-inds a))
	          (first-nonzero (nth k a)))))

;; (lead-inds a) is an increasing list:

(defthmd lead-inds-inc
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp i) (natp j) (< i j) (< j (len (lead-inds a))))
           (< (nth i (lead-inds a))
	      (nth j (lead-inds a)))))

;; By dcex-lemma, it follows that (lead-inds a)) is a dlist:

(defthm dlistp-lead-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (dlistp (lead-inds a))))

;; By (lead-inds a), (lead-inds a) is a sublist of (ninit n):

(defthmd sublistp-lead-inds-ninit
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (sublistp (lead-inds a)
	             (ninit n))))

;; Consequently, by sublistp-<=-len, (len (lead-inds l)) <= n:

(defthmd num-nonzero-rows<=n
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a))
           (<= (num-nonzero-rows a)
               n)))

(defthmd row-rank<=n
  (implies (and (fmatp a m n) (posp m) (posp n))
           (<= (row-rank a)
               n)))

;; If (num-nonzero-rows a) = n, then (lead-inds a) = (ninit n):

(defthmd lead-inds-ninit
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (= (num-nonzero-rows a) n))
	   (equal (lead-inds a) (ninit n))))


;;----------------------------------------------------------------------------------------
;; Row Reduction as Matrix Multiplication
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
           (fmatp (apply-row-op op a) m n)))

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

(defthm row-ops-p-clear-column-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n))
	   (row-ops-p (clear-column-ops a k j m) m)))

(defthmd apply-clear-column-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n))
           (equal (apply-row-ops (clear-column-ops a k j m) a)
	          (clear-column a k j m))))

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
           (row-ops-p (row-reduce-step-ops a m k i j) m)))

(defthmd apply-row-reduce-step-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (natp j) (< j n) (natp i) (< i m)
		(not (= (entry i j a) (f0))))
           (equal (apply-row-ops (row-reduce-step-ops a m k i j) a)
                  (row-reduce-step a m k i j))))

;; The list of row operations applied by row-reduce-aux:

(defun row-reduce-aux-ops (a m k)
  (declare (xargs :measure (nfix (- m k))))
  (let* ((i (row-with-nonzero-at-least-index a m k))
	 (j (and i (first-nonzero (nth i a)))))
    (if (and (natp k) (natp m) (< k m) i)
        (append (row-reduce-step-ops a m k i j)
	        (row-reduce-aux-ops (row-reduce-step a m k i j) m (1+ k)))                
      ())))

(defthmd row-ops-p-row-reduce-aux-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m))
	   (row-ops-p (row-reduce-aux-ops a m k) m)))

(defthmd apply-row-reduce-aux-ops
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp k) (< k m) (row-echelon-p-aux a m k))
           (equal (apply-row-ops (row-reduce-aux-ops a m k) a)
                  (row-reduce-aux a m k))))

;; The list of row operations applied by row-reduce:

(defund row-reduce-ops (a)
  (row-reduce-aux-ops a (len a) 0))

(defthmd row-ops-p-row-reduce-ops
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (row-ops-p (row-reduce-ops a) m)))

(defthmd apply-row-reduce-ops
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (equal (apply-row-ops (row-reduce-ops a) a)
		  (row-reduce a))))

;; The nxn elementary matrix corresponding to a row operation:

(defund elem-mat (op m)
  (apply-row-op op (id-mat m)))

(defthm fmatp-elem-mat
  (implies (and (row-op-p op m) (natp m))
           (fmatp (elem-mat op m) m m)))

;; Application of a row-op is equivalent to multiplication by the corresponding
;; elementary matrix:

(defthmd elem-mat-row-op
  (implies (and (fmatp a m n) (row-op-p op m) (posp m) (posp n))
	   (equal (fmat* (elem-mat op m) a)
		  (apply-row-op op a))))
		  
;; The product of the elementary matrices corresponding to a list of row operations:

(defund row-ops-mat (ops m)
  (if (consp ops)
      (fmat* (row-ops-mat (cdr ops) m)
             (elem-mat (car ops) m))             
    (id-mat m)))

(defthm fmatp-row-ops-mat
  (implies (and (row-ops-p ops m) (posp m))
           (fmatp (row-ops-mat ops m) m m)))

(defthm fmat*-row-ops-mat
  (implies (and (fmatp a m n) (posp m) (posp n)
                (row-ops-p ops m))
	   (equal (fmat* (row-ops-mat ops m) a)
	          (apply-row-ops ops a))))

(defund row-reduce-mat (a)
  (row-ops-mat (row-reduce-ops a) (len a)))

(defthmd row-ops-mat-row-reduce
  (implies (and (fmatp a m n) (posp m) (posp n))
	   (equal (fmat* (row-reduce-mat a) a)
		  (row-reduce a))))

;;----------------------------------------------------------------------------------------
;; Invertibility
;;----------------------------------------------------------------------------------------

;; In this section, we focus on square matrices.  Given an nxn matrix a, we seek an nxn
;; matrix b such that (fmat* a b) = (fmat* b a) = (id-mat n), which we shall call the
;; inverse of a.  If it exists, the inverse of a is unique in the following strong sense:
;; if (fmat* c a) = (id-mat n), then

;;   c = (fmat* c (id-mat n))
;;     = (fmat* c (fmat* a b))
;;     = (fmat* (fmat* c a) b))
;;     = (fmat* (id-mat n) b))
;;     = b,

;; and if (fmat* a c) = (id-mat n), then
;;   c = (fmat* (id-mat n) c)
;;     = (fmat* (fmat* b a) c)
;;     = (fmat* b (fmat* a c))
;;     = (fmat* b (id-mat n)))
;;     = b.

(defthm inverse-unique
  (implies (and (fmatp a n n) (fmatp b n n) (fmatp c n n) (posp n)
		(= (fmat* a b) (id-mat n))
		(= (fmat* b a) (id-mat n))
		(or (= (fmat* a c) (id-mat n))
	            (= (fmat* c a) (id-mat n))))
	   (equal c b))
  :rule-classes ())

;; Every elementary matrix has an inverse:

(defund invert-row-op (op)
  (case (car op)
    (1 (list 1 (f/ (cadr op)) (caddr op)))
    (2 (list 2 (f- (cadr op)) (caddr op) (cadddr op)))
    (3 op)))

(defthmd row-op-p-invert-row-op
  (implies (and (row-op-p op n) (posp n))
	   (and (row-op-p (invert-row-op op) n)
		(equal (invert-row-op (invert-row-op op))
		       op))))
		  
(defthmd compose-invert-row-op
  (implies (and (fmatp a n n) (row-op-p op n) (posp n))
           (equal (apply-row-op (invert-row-op op) (apply-row-op op a))
	          a)))

(defthmd fmat*-elem-invert-row-op
  (implies (and (row-op-p op n) (posp n))
           (and (equal (fmat* (elem-mat (invert-row-op op) n)
			      (elem-mat op n))
		       (id-mat n))
		(equal (fmat* (elem-mat op n)
		              (elem-mat (invert-row-op op) n))			      
		       (id-mat n)))))

;; Every product of elementary matrices has an inverse:

(defun invert-row-ops (ops)
  (if (consp ops)
      (append (invert-row-ops (cdr ops))
              (list (invert-row-op (car ops))))
    ()))

(defthmd row-ops-p-invert-row-ops
  (implies (and (row-ops-p ops n) (posp n))
	   (row-ops-p (invert-row-ops ops) n)))

(defthmd invert-row-ops-mat
  (implies (and (row-ops-p ops n) (posp n))
                (and (equal (fmat* (row-ops-mat (invert-row-ops ops) n)
	                           (row-ops-mat ops n))
		            (id-mat n))
                     (equal (fmat* (row-ops-mat ops n)
			           (row-ops-mat (invert-row-ops ops) n))			      
		            (id-mat n)))))

;; We shall show that a has an inverse iff (row-rank a) = n and that in this case,
;; the inverse of a is (row-reduce-mat a).  Thus, we define

(defund invertiblep (a n)
  (= (row-rank a) n))

(defund inverse-mat (a)
  (row-reduce-mat a))

;; First we show, as a consequence of lead-inds-ninit,  that if (invertiblep a n),
;; then (row-reduce a) = (id-mat n):

(defthm row-echelon-p-id-mat
  (implies (and (fmatp a n n)
		(posp n)
		(row-echelon-p a)
		(= (num-nonzero-rows a) n))
	   (equal a (id-mat n)))
  :rule-classes ())

;; Now let

;;    p = (inverse-mat a) = (row-reduce-mat a) = (row-ops-mat (row-reduce-ops a) n),

;;    q = (row-ops-mat (invert-row-ops (row-reduce-ops a)) n),

;; and

;;    r = (fmat* p a) = (row-reduce a).

;; By invert-row-ops-mat, (fmat* p q) = fmat* q p) = (id-mat n).  If (row-rank a) = n,
;; then (num-nonzero-rows r) = n.  By row-echelon-p-id-mat, (fmat* p a) = r = (id-mat n),
;; and by inverse-unique, a = q.  Thus, (invertiblep a n) is a sufficient condition for
;; the existence of an inverse:

(defthmd invertiblep-sufficient
  (implies (and (fmatp a n n) (posp n) (invertiblep a n))
	   (let ((p (inverse-mat a)))
	     (and (fmatp p n n)
		  (equal (fmat* a p) (id-mat n))
		  (equal (fmat* p a) (id-mat n))))))

;; To prove the necessity of (invertiblep a n), suppose  and let (fmatp b n n).
;; If (fmat* a b) 0 (id-nat n), then

;;   (fmat* r (fmat* b q)) = (fmat* (fmt* p a) (fmat* b q))
;;                         = (fmat* p (fmat* (fmat* a b) q))
;;			   = (fmat* p q)
;;			   = (id-mat n).

;; If (invertiblep a n) = NIL, then the last row of r is 0, and by nth-fmat*, the same
;; must be true of (id-mat n), a contradiction.

(defthmd invertiblep-necessary
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-mat n)))
	   (invertiblep a n)))

;; Some consequences of the preceding results:

(defthmd inverse-inverse-mat
  (implies (and (fmatp a n n) (posp n) (invertiblep a n))
	   (and (invertiblep (inverse-mat a) n)
		(equal (inverse-mat (inverse-mat a))
		       a))))

(defthmd invertiblep-inverse
  (implies (and (fmatp a n n) (fmatp b n n) (posp n)
		(or (= (fmat* a b) (id-mat n))
		    (= (fmat* b a) (id-mat n))))
	   (and (invertiblep a n)
		(equal (inverse-mat a) b))))

(defthmd invertiblep-row-ops-mat
  (implies (and (row-ops-p ops n) (posp n))
	   (and (invertiblep (row-ops-mat ops n) n)
		(equal (inverse-mat (row-ops-mat ops n))
		       (row-ops-mat (invert-row-ops ops) n)))))

(defthmd row-reduce-mat-invertiblep
  (implies (invertiblep a n)
	   (equal (inverse-mat a)
		  (row-reduce-mat a))))

(defthmd invertiblep-factor
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (invertiblep (fmat* a b) n))
	   (and (invertiblep a n) (invertiblep b n))))

(defthmd inverse-fmat*
  (implies (and (fmatp a n n) (fmatp b n n) (posp n) (invertiblep a n) (invertiblep b n))
	   (and (invertiblep (fmat* a b) n)
		(equal (inverse-mat (fmat* a b))
		       (fmat* (inverse-mat b) (inverse-mat a))))))

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
  (transpose (row-mat x)))

(defthm fmatp-row-mat
  (implies (flistp x n)
           (fmatp (row-mat x) 1 n)))

(defthm fmatp-col-mat
  (implies (and (posp n) (flistp x n))
           (fmatp (col-mat x) n 1)))

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
  (implies (and (fmatp a m n) (posp m) (posp n) (flistp b m) (flistp x n))
           (let* ((bc (col-mat b))
	          (xc (col-mat x))
		  (p (row-reduce-mat a))
		  (ar (fmat* p a))
		  (br (fmat* p bc)))
             (iff (solutionp x a b)
	          (equal (fmat* ar xc) br)))))

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

(defun solvablep (a b m)
  (null (find-nonzero (fmat* (row-reduce-mat a) (col-mat b))
                      (row-rank a)
		      m)))

;; Suppose first that (find-nonzero br q m) = k <> nil, so that (solvablep a b m) = nil.  Then 
;; (row k ar) = (flist0 n) and (entry k 0 br) <> (f0).  It follows that

;;   (entry k 0 (fmat* ar xc)) = (fdot (row k ar) (col 0 xc)) = (f0) <> (nth k 0 br),

;; and hence (fmat* ar xc) <> br:

(defthmd row-echelon-p-unsolvable-case
  (implies (and (fmatp ar m n) (posp m) (posp n) (fmatp br m 1) (fmatp xc n 1)
                (row-echelon-p ar)
                (find-nonzero br (num-nonzero-rows ar) m))
           (not (equal (fmat* ar xc) br))))

;; We combine this result with reduce-linear-equations to conclude that the system
;; of equations has no solution:

(defthmd linear-equations-unsolvable-case
  (implies (and (fmatp a m n) (posp m) (posp n) (flistp b m) (flistp x n)
                (not (solvablep a b m)))
	   (not (solutionp x a b))))

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
	   (fmatp (first-rows q a) q n)))

(defthmd nth-first-rows
  (implies (and (fmatp a m n) (natp m)
                (natp q) (<= q m) (natp i) (< i q))
	   (equal (nth i (first-rows q a))
	          (nth i a))))

(defthmd num-nonzero-rows-first-rows
  (implies (and (fmatp a m n) (natp m) (natp n)
                (natp q) (<= q (num-nonzero-rows a)))
	   (equal (num-nonzero-rows (first-rows q a)) q)))

(defthmd row-echelon-p-first-rows
  (implies (and (fmatp a m n) (posp m) (posp n) (row-echelon-p a)
                (natp q) (<= q m))
	   (row-echelon-p (first-rows q a))))

(defthmd first-rows-rank
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar))
           (let* ((q (num-nonzero-rows ar))
	          (aq (first-rows q ar)))
              (and (fmatp aq q n)
	           (row-echelon-p aq)
	           (equal (num-nonzero-rows aq) q)))))

;; According to the following result, (first-rows q (fmat* ar xc)) = (fmat* aq xc):

(defthmd first-rows-fmat*
  (implies (and (fmatp a m n) (fmatp b n p) (natp m) (posp n) (posp p)
                (natp q) (<= q m))
           (equal (first-rows q (fmat* a b))
	          (fmat* (first-rows q a) b))))

;; For q <= k < m, since (flist0p (row k ar)), (entry k 0 (fmat* ar xc)) = (f0).
;; Thus (first-nonzero (fmat* ar xc) q m) = nil, which implies

;;   ((fmat* ar xc) = br <=> (fmat* aq xc) = bq:

(defthmd null-first-nonzero-fmat*
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar) (fmatp xc n 1))
	   (null (find-nonzero (fmat* ar xc) (num-nonzero-rows ar) m))))

(defthmd first-rows-equal
  (implies (and (fmatp b1 m 1) (fmatp b2 m 1) (posp m)
                (natp q) (<= q m)
		(null (find-nonzero b1 q m))
		(null (find-nonzero b2 q m)))
	   (iff (equal (first-rows q b1) (first-rows q b2))
	        (equal b1 b2))))

(defthmd first-rows-linear-equations
  (implies (and (fmatp ar m n) (posp m) (posp n) (row-echelon-p ar)
                (fmatp br m 1) (fmatp xc n 1)
                (null (find-nonzero br (num-nonzero-rows ar) m)))
	   (let* ((q (num-nonzero-rows ar))
	          (aq (first-rows q ar))
	          (bq (first-rows q br)))
	     (iff (equal (fmat* ar xc) br)
	          (equal (fmat* aq xc) bq)))))

;; Our objective, therefore, is to solve the equation (fmat* aq xc) = bq.			

;; By row-rank<=n, q <= n.  If q = n, then by row-echelon-p-id-mat, aq = (id-mat n) and
;; (fmat* aq xc) = bq iff xc = bq:

(defthmd row-echelon-p-unique-solution-case
  (implies (and (fmatp aq n n) (posp n) (fmatp bq n 1) (fmatp xc n 1)
                (row-echelon-p aq)
		(= (num-nonzero-rows aq) n))
	   (iff (equal (fmat* aq xc) bq)
	        (equal xc bq))))

;; Combine the last 2 results with reduce-linear-equations to conclude that there exists a unique
;; solution in this case:

(defthmd linear-equations-unique-solution-case
  (let* ((br (fmat* (row-reduce-mat a) (col-mat b)))
         (bq (first-rows n br)))
    (implies (and (fmatp a m n) (posp m) (posp n) (flistp b m) (flistp x n)
                  (solvablep a b m)
	          (= (row-rank a) n))
	     (iff (solutionp x a b)
	          (equal x (col 0 bq))))))

;; In the remainder of this section, we treat the general case (solvablep a b m) = t with arbitrary
;; row-rank q <= n.  The equation (fmat* aq xc) = bq holds iff for 0 <= i < q,

;;   (nth i (fmat* aq xc)) = (nth i bq)

;; or equivalently,

;;   (fdot (row i aq) x) = (car (nth i bq)).

(defthmd nth-fmat*-aq-xc
  (implies (and (fmatp aq q n) (fmatp bq q 1) (flistp x n) (posp q) (posp n) (natp i) (< i q))
           (iff (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))
	        (equal (fdot (nth i aq) x)
		       (car (nth i bq))))))
			
;; We shall split (fdot (nth i aq) x) into 2 sums, corresponding to the list (lead-inds aq) and the
;; list of remaining indices, (free-inds aq n), which we define as follows:

(defund free-inds (a n)
  (set-difference-equal (ninit n) (lead-inds a)))

;; Note that if q = n, then (free-inds aq n) = nil.  In general, given a sublist of (ninit n), a dot
;;  product of 2 flists of length n may be split into 2 sums as follows:

(defun fdot-select (inds r x)
  (if (consp inds)
      (f+ (f* (nth (car inds) r)
              (nth (car inds) x))
	  (fdot-select (cdr inds) r x))
    (f0)))

(defthm fp-fdot-select
  (implies (and (natp n) (flistp x n) (flistp y n)
                (sublistp l (ninit n)))
	   (fp (fdot-select l x y))))

(defthmd fdot-select-perm
  (implies (and (natp n) (flistp x n) (flistp y n)
                (sublistp l (ninit n))
                (sublistp m (ninit n))
		(permutationp l m))
	   (equal (fdot-select l x y)
	          (fdot-select m x y))))

(defthmd fdot-select-append
  (implies (and (natp n) (flistp x n) (flistp y n)
                (sublistp l (ninit n))
                (sublistp m (ninit n)))
	   (equal (fdot-select (append l m) x y)
	          (f+ (fdot-select l x y)
		      (fdot-select m x y)))))

(defthmd fdot-select-ninit
  (implies (and (natp n) (flistp x n) (flistp y n))
	   (equal (fdot-select (ninit n) x y)
	          (fdot x y))))

(defthmd permutationp-append-set-difference
  (implies (and (dlistp l) (sublistp l (ninit n)) (posp n))
           (permutationp (append l (set-difference-equal (ninit n) l))
	                 (ninit n))))

(defthmd fdot-select-append-set-difference
  (implies (and (natp n) (flistp x n) (flistp y n)
                (dlistp l) (sublistp l (ninit n)))
           (equal (fdot-select (append l (set-difference-equal (ninit n) l)) x y)
	          (fdot x y))))

(defthmd fdot-split
  (implies (and (natp n) (flistp x n) (flistp y n)
                (dlistp l) (sublistp l (ninit n)))
	   (equal (fdot x y)
	          (f+ (fdot-select l x y)
		      (fdot-select (set-difference-equal (ninit n) l) x y)))))

;; The following is a consequence of dlistp-lead-inds and sublistp-lead-inds-ninit

(defthmd fdot-lead-free
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq) (flistp x n)
                (natp i) (< i q))
           (equal (fdot (row i aq) x)
	          (f+ (fdot-select (lead-inds aq) (row i aq) x)
		      (fdot-select (free-inds aq n) (row i aq) x)))))

;; The term (fdot-select (lead-inds ar) x) may be simplified according to nth-lead-inds and
;; nth-first-nonzero:

(defthmd fdot-select-lead-inds
  (implies (and (fmatp aq q n) (posp q) (posp n) (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(natp i) (< i q)
		(flistp x n))
	   (equal (fdot-select (lead-inds aq) (nth i aq) x)
	          (nth (nth i (lead-inds aq)) x))))

;; Combining the lasr result with nth-fmat*-aq-xc, fdot-lead-free, and fdot-select-lead-inds,
;; we have the following reformulation of the equation (nth i (fmat* aq xc)) = (nth i bq):

(defthmd equal-rows-lemma
  (implies (and (fmatp aq q n) (fmatp bq q 1) (posp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistp x n)
		(natp i) (< i q))
           (iff (equal (nth i (fmat* aq (col-mat x)))
	               (nth i bq))
		(equal (nth (nth i (lead-inds aq)) x)
		       (f+ (car (nth i bq))
		           (f- (fdot-select (free-inds aq n) (row i aq) x)))))))
			
;; Consequently, x is a solution of our system of equations iff this condition holds for
;; all i < q:

(defun solution-test (x aq bq l f k)
  (if (zp k)
      t
    (and (equal (nth (nth (1- k) l) x)
                (f+ (car (nth (1- k) bq))
		    (f- (fdot-select f (nth (1- k) aq) x))))
	 (solution-test x aq bq l f (1- k)))))

(defthmd solution-test-lemma
  (implies (and (fmatp aq q n) (fmatp bq q 1) (posp q) (posp n)
                (row-echelon-p aq)
                (= (num-nonzero-rows aq) q)
		(flistp x n))
	   (iff (solution-test x aq bq (lead-inds aq) (free-inds aq n) q)
	        (equal (fmat* aq (col-mat x))
	               bq))))

(defthmd linear-equations-solvable-case
  (let* ((ar (row-reduce a))
         (br (fmat* (row-reduce-mat a) (col-mat b)))
	 (q (num-nonzero-rows ar))
	 (aq (first-rows q ar))
	 (bq (first-rows q br))
	 (l (lead-inds aq))
	 (f (free-inds aq n)))
    (implies (and (fmatp a m n) (posp m) (posp n) (flistp b m) (flistp x n)
                  (solvablep a b m))
             (iff (solutionp x a b)
                  (solution-test x aq bq l f q)))))                        

;; Note that if (len l) = n and f = nil, then the equation

;;   (nth (nth i l) x) = (f+ (car (nth i bq)) (f- (fdot-select f (nth i aq) x)))

;; reduces to

;;   (nth i x) = (car (nth i bq),

;; (solution-test x aq bq l f q) reduces to x = (col 0 bq), and linear-equations-solvable-case
;; reduces to the earlier result linear-equations-unique-solution-case.

;; Otherwise, the entries of x corresponding to the indices in (lead-inds aq) are determined
;; by the entries corresponding to (free-inds aq n).  Thus, there is a unique solution
;; corresponding to every assignment of values to the latter set of entries, and hence an
;; infinite number of solutions.  We shall revisit this result later in the vector space of
;; solutions of a homogeneous system of equations.
