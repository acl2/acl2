(in-package "DM")

(include-book "ring")
(local (include-book "support/rmat"))

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

;; jth column of a:

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

;; To show that 2 matrices of the same dimensions are equal, it suffices to show that
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
		  (not (equal (entry i j a) (entry i j b)))))))

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
		  (rmat-add b a))))

(defthmd rmat-add-assoc
  (implies (and (rmatp a m n) (rmatp b m n) (rmatp c m n))
           (equal (rmat-add a (rmat-add b c))
		  (rmat-add (rmat-add a b) c))))

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

(defthmd rmatp-transpose
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (rmatp (transpose-mat a) n m)))

(defthm nth-transpose-rmat
  (implies (and (posp m) (posp n) (rmatp a m n)
                (natp i) (< i n))
	   (equal (nth i (transpose-mat a))
		  (col i a))))

(defthm transpose-rmat-entry
  (implies (and (posp m) (posp n) (rmatp a m n)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a))))

(defthm transpose-rmat-2
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (transpose-mat (transpose-mat a))
	          a)))

(defthmd col-transpose-rmat
  (implies (and (posp m) (posp n) (rmatp a m n)
                (natp j) (< j m))
	   (equal (col j (transpose-mat a))
	          (row j a))))

;; Replace kth column of a with r:

(defund replace-col (a k r)
  (transpose-mat (replace-row (transpose-mat a) k r)))

(defthm rmatp-replace-col
  (implies (and (rmatp a m n) (posp m) (posp n) (natp k) (< k n) (rlistnp r m))
           (rmatp (replace-col a k r) m n)))

(defthm rmat-col-replace-col
  (implies (and (rmatp a m n) (posp m) (posp n)
		(natp k) (< k n) (natp j) (< j n)
		(rlistnp r m))
           (equal (col j (replace-col a k r))
	          (if (= j k)
		      r
		    (col j a)))))

;; An important lemma in the proof of associativity of matrix multiplication:
;; If (rmatp a m n), then (rmat-sum (transpose-mat a)) = (rmat-sum a).
;; This holds trivially if either m = 0 or n = 0:

(defthm rmat-sum-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (rmatp a m n))
           (equal (rmat-sum a) (r0))))

(defthm rmat-sum-transpose-0
  (implies (and (natp m) (natp n) (or (= m 0) (= n 0)) (rmatp a m n))
           (equal (rmat-sum (transpose-mat a))
	          (r0))))
		        
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

(defthmd rmatp-strip-mat
  (implies (and (posp m) (posp n) (rmatp a m n))
           (rmatp (strip-mat a) (1- m) (1- n))))

(defthmd sum-rmat-strip-mat
  (implies (and (posp m) (posp n) (rmatp a m n))
	   (equal (rmat-sum a)
		  (r+ (entry 0 0 a)
		      (r+ (r+ (rlist-sum (cdr (row 0 a)))
			      (rlist-sum (cdr (col 0 a))))
			  (rmat-sum (strip-mat a)))))))

;; Since (row 0 a) = (col 0 (transpose-mat a)) and (col 0 a) = (row 0 (transpose-mat a)), we have
;; the following:

(defthmd sum-rmat-strip-mat-equal
  (implies (and (posp m) (posp n) (rmatp a m n)
                (equal (rmat-sum (strip-mat a)) (rmat-sum (strip-mat (transpose-mat a)))))
	   (equal (rmat-sum (transpose-mat a))
		  (rmat-sum a))))

;; If either m = 0 or n = 0, then the hypothesis of sum-rmat-strip-mat-equal holds trivially:

(defthm rmat-sum-strip-mat-0
  (implies (and (posp m) (posp n) (or (= m 1) (= n 1)) (rmatp a m n))
           (and (equal (rmat-sum (strip-mat a)) (r0))
	        (equal (rmat-sum (strip-mat (transpose-mat a))) (r0)))))

(defthmd strip-rmat-entry
  (implies (and (posp m) (posp n) (rmatp a m n)
		(natp i) (natp j) (< i (1- m)) (< j (1- n)))
	   (equal (entry i j (strip-mat a))
		  (entry (1+ i) (1+ j) a))))

;; In the remaining case, we have the following:

(defthmd transpose-strip-rmat
  (implies (and (posp m) (posp n) (> m 1) (> n 1) (rmatp a m n))
	   (equal (transpose-mat (strip-mat a))
		  (strip-mat (transpose-mat a)))))

;; The result follows by induction:

(defthmd sum-rmat-transpose
  (implies (and (natp m) (natp n) (rmatp a m n))
	   (equal (rmat-sum (transpose-mat a))
		  (rmat-sum a))))


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
  (implies (and (rmatp a m n) (rmatp b n p) (posp m) (posp n) (posp p))
           (rmatp (rmat* a b) m p)))

(defthmd nth-rmat*
  (implies (and (natp m) (rmatp a m n) (natp i) (< i m))
           (equal (nth i (rmat* a b))
	          (rdot-list (nth i a) (transpose-mat b)))))

(defthmd rmat*-entry
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p)
                (natp i) (< i m) (natp j) (< j p))
	   (equal (entry i j (rmat* a b))
	          (rdot (row i a) (col j b)))))

;; Some algebraic properties:

(defthmd rmat*-dist-1
  (implies (and (posp m) (posp n) (posp p) (rmatp a1 m n) (rmatp a2 m n) (rmatp b n p))
	   (equal (rmat* (rmat-add a1 a2) b)
		  (rmat-add (rmat* a1 b) (rmat* a2 b)))))
			
(defthmd rmat*-dist-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b1 n p) (rmatp b2 n p))
	   (equal (rmat* a (rmat-add b1 b2))
		  (rmat-add (rmat* a b1) (rmat* a b2)))))

(defthmd rmat*-rmat-scalar-mul-1
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c))
	   (equal (rmat* (rmat-scalar-mul c a) b)
		  (rmat-scalar-mul c (rmat* a b)))))

(defthmd rmat*-rmat-scalar-mul-2
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p) (rp c))
	   (equal (rmat* a (rmat-scalar-mul c b))
		  (rmat-scalar-mul c (rmat* a b)))))

;; Transpose of a product:

(defthmd transpose-rmat*
  (implies (and (posp m) (posp n) (posp p) (rmatp a m n) (rmatp b n p))
	   (equal (transpose-mat (rmat* a b))
	          (rmat* (transpose-mat b) (transpose-mat a)))))

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

;; The Kronecker delta function:

(defun rdelta (i j)
  (if (= i j) (r1) (r0)))

(defthm nth-runit
  (implies (and (natp n) (natp j) (< j n) (natp i) (< i n))
           (equal (nth i (runit j n))
	          (rdelta i j))))

;; Dot product of (runit j n) with an rlist of length n:

(defthm rdot-runit
  (implies (and (posp n) (rlistnp x n) (natp j) (< j n))
           (equal (rdot (runit j n) x)
	          (nth j x))))

(defthm rdot-runit-comm
  (implies (and (posp n) (rlistnp x n) (natp j) (< j n))
           (equal (rdot x (runit j n))
	          (nth j x))))

;; nxn identity matrix:

(defun id-rmat-aux (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (runit i n) (id-rmat-aux (1+ i) n))
    ()))

(defund id-rmat (n)
  (id-rmat-aux 0 n))

(defthm rmatp-id-rmat
  (implies (posp n)
           (rmatp (id-rmat n) n n)))

(defthm nth-id-rmat
  (implies (and (posp n) (natp i) (< i n))
	   (equal (nth i (id-rmat n))
		  (runit i n))))

(defthmd entry-id-rmat
  (implies (and (natp n) (natp i) (natp j) (< i n) (< j n))
           (equal (entry i j (id-rmat n))
	          (rdelta i j))))

(defthmd transpose-id-rmat
  (implies (natp n)
           (equal (transpose-mat (id-rmat n))
	          (id-rmat n))))

(defthm col-id-rmat
  (implies (and (natp n) (natp j) (< j n))
           (equal (col j (id-rmat n))
	          (runit j n))))

;; (id-rmat n) is a right identity:

(defthmd id-rmat-right
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (rmat* a (id-rmat n))
	          a)))

;; (id-rmat n) is a left identity:

(defthmd id-rmat-left
  (implies (and (posp m) (posp n) (rmatp a m n))
           (equal (rmat* (id-rmat m) a)
	          a)))
							   
;; Associativity:

;; Let a, b, and c be matrices of dimensions mxn, nxp, and pxq, respectively.  Then
;; (rmat* a (rmat* b c)) and (rmat* (rmat* a b) c)) are both mxp matrices.  Our
;; objective is to prove that they are equal.  Let 0 <= i < m and 0 <= j < q.  It will
;; suffice to show that

;;    (entry i j (rmat* a (rmat* b c))) = (entry i j (rmat* (rmat* a b) c)).

;; Applying rmat*-entry and expanding rdot, we find that both sides of this equation
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

(defthmd rmatp-rmat12
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (rmatp (rmat12 a b c i j) n p)))

;; We shall derive an expression for (entry r s (rmat12 a b c i j)).  First we compute its rth row:

;;  (nth r (rmat12 a b c i j)) = (rlist-scalar-mul (nth r (row i a)) (nth r (rlist-mul-list (col j c) b)))
;;                             = (rlist-scalar-mul (entry i r a) (rlist-mul (col j c) (nth r b)))

;; Now the sth entry of the rth row:

;;  (entry r s (rmat12 a b c i j)) = (nth s (nth r (rmat12 a b c i j)))
;;                                 = (nth s (rlist-scalar-mul (entry i r a) (rlist-mul (col j c) (nth r b))))
;;                                 = (entry i r a) * (nth s (rlist-mul (col j c) (nth r b)))
;;                                 = (entry i r a) * ((nth s (col j c)) * (nth s (nth r b)))
;;                                 = (entry i r a) * ((entry s j c) * (entry r s b))
;;                                 = (entry i r a) * (entry r s b) * (entry s j c)

(defthmd rmat12-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r n) (natp s) (< s p))
           (equal (entry r s (rmat12 a b c i j))
	          (r* (r* (entry i r a) (entry r s b)) (entry s j c)))))

;; Next we show that (rmat-sum (rmat12 a b c i j)) = (entry i j (rmat* a (rmat* b c).  As a first step, it is easily 
;; shown by induction that if x is an rlist of length n and l is a matrix with n rows, then

;;    (rmat-sum (rlist-scalar-mul-list x l)) = (rdot x (rlist-sum-list l)).

;; We apply this result to the definition of rmat-sum, substituting (row i a) for x and (rlist-mul-list (col j c) b)
;; for l.  This yields

;;    (rmat-sum (rmat12 a b c i j)) = (rdot (row i a) (rlist-sum-list (rlist-mul-list (col j c) b))),

;; Note that (rlist-sum-list (rlist-mul-list (col j c) b)) and (col j (rmat* b c)) are both rlists of length n.
;; To prove that they are equal, it suffices to show that corresponding members are equal:

;;    (nth k (rlist-sum-list (rlist-mul-list (col j c) b))) = (rlist-sum (nth k (rlist-mul-list (col j c) b)))
;;                                                          = (rlist-sum (rlist-mul (col j c) (nth k b)))
;;                                                          = (rdot (col j c) (nth k b))
;;                                                          = (rdot (col j c) (row k b))
;;                                                          = (rdot (row k b) (col j c))
;;                                                          = (entry k j (rmat* b c))
;;                                                          = (nth k (col j (rmat* b c)))

;; Thus, (rlist-sum-list (rlist-mul-list (col j c) b)) = (col j (rmat* b c)).  It follows that

;;    (rmat-sum (rmat12 a b c i j)) = (rdot (row i a) (col j (rmat* b c))) = (entry i j (rmat* a (rmat* b c))):

(defthm rmat-sum-rmat12
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat12 a b c i j))
	          (entry i j (rmat* a (rmat* b c))))))

;; The matrix (rmat21 a b c i j) similarly relates to (entry i j (rmat* (rmat* a b) c):

(defund rmat21 (a b c i j)
  (rlist-scalar-mul-list (col j c)
		         (rlist-mul-list (row i a) (transpose-mat b))))

(defthmd rmatp-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
	   (rmatp (rmat21 a b c i j) p n)))

(defthmd rmat21-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (rmat21 a b c i j))
	          (r* (entry i s a) (r* (entry s r b) (entry r j c))))))

(defthm rmat-sum-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (rmat-sum (rmat21 a b c i j))
	          (entry i j (rmat* (rmat* a b) c)))))

;; Combine rmat21-entry and rmat12-entry:

(defthmd rmat12-rmat21-entry
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q)
		(natp r) (< r p) (natp s) (< s n))
           (equal (entry r s (rmat21 a b c i j))
	          (entry s r (rmat12 a b c i j)))))

;; Apply transpose-rmat-entry:

(defthmd rmat12-transpose-rmat21
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q)
                (natp i) (< i m) (natp j) (< j q))
           (equal (transpose-mat (rmat12 a b c i j))
	          (rmat21 a b c i j))))

;; By sum-rmat-transpose, (entry i j (rmat* a (rmat* b c))) = (entry i j (rmat* (rmat* a b) c)),
;; and the result follows:

(defthmd rmat*-assoc
  (implies (and (rmatp a m n) (rmatp b n p) (rmatp c p q) (posp m) (posp n) (posp p) (posp q))
           (equal (rmat* a (rmat* b c))
	          (rmat* (rmat* a b) c))))
