(in-package "DM")

(include-book "projects/groups/symmetric" :dir :system)

;; Here we replace the constrained functions in field.lisp with the corresponding rational
;; functions and in this context, we repeat the function definitions in field.lisp,
;; fmat.lisp, fdet.lisp, and reduction.lisp.  The result is that these definitions are now
;; executable and can be used for the purpose of illustration.

(defun fp (x) (rationalp x))
(defun f+ (x y) (+ x y))
(defun f* (x y) (* x y))
(defun f0 () 0)
(defun f1 () 1)
(defun f- (x) (- x))
(defun f/ (x) (/ x))


;;----------------------------------------------------------------------------------------
;; Lists of Field Elements
;;----------------------------------------------------------------------------------------

(defun flistp (l)
  (if (consp l)
      (and (fp (car l)) (flistp (cdr l)))
    (null l)))

;; Sum of the members of l:

(defun flist-sum (l)
  (if (consp l)
      (f+ (car l) (flist-sum (cdr l)))
    (f0)))

;; Product of the members of l:

(defun flist-prod (l)
  (if (consp l)
      (f* (car l) (flist-prod (cdr l)))
    (f1)))

;; List of ring elements of length n:

(defun flistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (fp (car x))
	 (flistnp (cdr x) (1- n)))))

;; Every member of x is (f0):

(defun flist0p (x)
  (if (consp x)
      (and (= (car x) (f0))
           (flist0p (cdr x)))
    (null x)))

;; List of n copies of (f0):

(defun flistn0 (n)
  (if (zp n)
      () 
    (cons (f0) (flistn0 (1- n)))))

;; List of sums of corresponding members of x and y:

(defun flist-add (x y)
  (if (consp x)
      (cons (f+ (car x) (car y))
            (flist-add (cdr x) (cdr y)))
    ()))

;; List of products of corresponding members of x and y:

(defun flist-mul (x y)
  (if (consp x)
      (cons (f* (car x) (car y))
	    (flist-mul (cdr x) (cdr y)))
    ()))

;; Multiply each member of x by c:

(defun flist-scalar-mul (c x)
  (if (consp x)
      (cons (f* c (car x))
            (flist-scalar-mul c (cdr x)))
    ()))

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

;; ith row of a:

(defun row (i a)
  (nth i a))

;; jth column or a:

(defun col (j a)
  (if (consp a)
      (cons (nth j (car a))
            (col j (cdr a)))
    ()))

;; The entry of a matrix in row i and column j:

(defun entry (i j mat)
  (nth j (nth i mat)))

;; Replace kth row of a with r:

(defun replace-row (a k r)
  (if (zp k)
      (cons r (cdr a))
    (cons (car a) (replace-row (cdr a) (1- k) r))))

;; Addition of mxn matrices:

(defun fmat-add (a b)
  (if (consp a)
      (cons (flist-add (car a) (car b))
	    (fmat-add (cdr a) (cdr b)))
    ()))

;; Multiply each entry of a by c:

(defun fmat-scalar-mul (c a)
  (if (consp a)
      (cons (flist-scalar-mul c (car a))
	    (fmat-scalar-mul c (cdr a)))
    ()))

;; Sum of all entries of a:

(defun fmat-sum (a)
  (if (consp a)
      (f+ (flist-sum (car a))
	  (fmat-sum (cdr a)))
    (f0)))

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

;; Replace kth column of a with r:

(defund replace-col (a k r)
  (transpose-mat (replace-row (transpose-mat a) k r)))


;;----------------------------------------------------------------------------------------
;; Matrix Multiplication
;;----------------------------------------------------------------------------------------

;; Dot product of 2 lists of field elements of the same length:

(defun fdot (x y)
  (if (consp x)
      (f+ (f* (car x) (car y))
          (fdot (cdr x) (cdr y)))
    (f0)))

;; List of dot products of an flist x with the elements of a list of flists l:

(defun fdot-list (x l)
  (if (consp l)
      (cons (fdot x (car l))
            (fdot-list x (cdr l)))
    ()))

;; Product of mxn matrix a and nxp matrix b:

(defund fmat* (a b)
  (if (consp a)
      (cons (fdot-list (car a) (transpose-mat b))
            (fmat* (cdr a) b))
    ()))

;; The definition of the nxn identity matrix is based on that of an flist of length n
;; with (f1) at index j and (f0) elsewhere:

(defun funit (j n)
  (if (zp n)
      ()
    (if (zp j)
        (cons (f1) (flistn0 (1- n)))
      (cons (f0) (funit (1- j) (1- n))))))

;; nxn identity matrix:

(defun id-fmat-aux (j n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (funit j n) (id-fmat-aux (1+ j) n))
    ()))

(defund id-fmat (n)
  (id-fmat-aux 0 n))

;;----------------------------------------------------------------------------------------
;; Determinants
;;----------------------------------------------------------------------------------------

;; The term contributed by a permutation p in (sym n) to the determinant of an nxn
;;  matrix a is computed as follows:
;;   (1) select an entry from each row of a, the selection from row i being the one
;;       in column (nth i p), i.e., (entry i (nth i p) a);
;;   (2) compute the product of these n entries;
;;   (3) negate the product if p is an odd permutation.

(defun fdet-prod (a p n)
  (if (zp n)
      (f1)
    (f* (fdet-prod a p (1- n))
        (entry (1- n) (nth (1- n) p) a))))

(defund fdet-term (a p n)
  (if (even-perm-p p n)
      (fdet-prod a p n)
    (f- (fdet-prod a p n))))

;; The determinant of a is the sum over (slist n) of these signed products:

(defun fdet-sum (a l n)
  (if (consp l)
      (f+ (fdet-term a (car l) n)
	  (fdet-sum a (cdr l) n))
    (f0)))

(defund fdet (a n)
  (fdet-sum a (slist n) n))


;;-------------------------------------------------------------------------------------------------------
;;   Cofactor Expansion
;;-------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we define the submatrix (minor i j a) to be the result of deleting
;; the ith row and the jth column of a:

(defun delete-row (k a)
  (if (zp k)
      (cdr a)
    (cons (car a) (delete-row (1- k) (cdr a)))))

(defund delete-col (k a)
  (transpose-mat (delete-row k (transpose-mat a))))

(defund minor (i j a)
  (delete-col j (delete-row i a)))

;; Next, we define the cofactor of an entry of a:

(defund fdet-cofactor (i j a n)
  (if (evenp (+ i j))
      (fdet (minor i j a) (1- n))
    (f- (fdet (minor i j a) (1- n)))))

;; Cofactor expansion of the determinant of a by column j:

(defun expand-fdet-col-aux (a i j n)
  (if (zp i)
      (f0)
    (f+ (f* (entry (1- i) j a)
            (fdet-cofactor (1- i) j a n))
	(expand-fdet-col-aux a (1- i) j n))))

(defund expand-fdet-col (a j n)
  (expand-fdet-col-aux a n j n))

;; Cofactor expansion of the determinant of a by row i:

(defun expand-fdet-row-aux (a i j n)
  (if (zp j)
      (f0)
    (f+ (f* (entry i (1- j) a)
            (fdet-cofactor i (1- j) a n))
	(expand-fdet-row-aux a i (1- j) n))))

(defund expand-fdet-row (a i n)
  (expand-fdet-row-aux a i n n))

;; (defthmd expand-fdet-col-fdet
;;   (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
;;            (equal (expand-fdet-col a k n)
;;                   (fdet a n))))

;; (defthmd expand-fdet-row-fdet
;;   (implies (and (fmatp a n n) (posp n) (> n 1) (natp k) (< k n))
;;            (equal (expand-fdet-row a k n)
;;                   (fdet a n))))

;; As a consequence of expand-fdet-row-fdet, we have a recursive version of fdet, based on 
;; cofactor expansion with respect to row 0:

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  (defund fdet-rec-cofactor (j a n)
    (declare (xargs :measure (list (nfix n) 0 0)))
    (if (zp n)
        ()
      (if (evenp j)
          (fdet-rec (minor 0 j a) (1- n))
        (f- (fdet-rec (minor 0 j a) (1- n))))))

  (defun expand-fdet-rec-aux (a j n)
    (declare (xargs :measure (list (nfix n) 1 (nfix j))))
    (if (zp j)
        (f0)
      (f+ (f* (entry 0 (1- j) a)
              (fdet-rec-cofactor (1- j) a n))
	  (expand-fdet-rec-aux a (1- j) n))))

  (defund expand-fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 2 0)))
    (expand-fdet-rec-aux a n n))

  (defun fdet-rec (a n)
    (declare (xargs :measure (list (nfix n) 3 0)))
    (if (zp n)
        (f0)
      (if (= n 1)
          (entry 0 0 a)
        (expand-fdet-rec a n))))
  ))

;; (defthmd fdet-rec-fdet
;;   (implies (and (fmatp a n n) (posp n))
;;            (equal (fdet-rec a n)
;;                   (fdet a n))))


;;---------------------------------------------------------------------------------------------------------
;;    Classical Adjoint
;;---------------------------------------------------------------------------------------------------------

;; Given an nxn matrix a, we shall define its cofactor matrix (cofactor-fmat a n) to be the nxn
;; matrix with entries

;;    (entry i j (cofactor-fmat a n)) = (fdet-cofactor i j a n).

;; We begin by defining the ith row of the cofactor matrix:

(defun cofactor-fmat-row-aux (i j a n)
  (declare (xargs :measure (nfix (- n j))))
  (if (and (natp n) (> n 1) (natp j) (< j n))
      (cons (fdet-cofactor i j a n)
            (cofactor-fmat-row-aux i (1+ j) a n))
    ()))

(defund cofactor-fmat-row (i a n)
  (cofactor-fmat-row-aux i 0 a n))

;; The cofactor matrix may now be defined:

(defun cofactor-fmat-aux (i a n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp n) (natp i) (< i n))
      (cons (cofactor-fmat-row i a n)
            (cofactor-fmat-aux (1+ i) a n))
    ()))

(defund cofactor-fmat (a n)
  (cofactor-fmat-aux 0 a n))

;; The classsical adjoint of a is the transpose of its cofactor matrix:

(defund adjoint-fmat (a n)
  (transpose-mat (cofactor-fmat a n)))

;; (defthmd fmat*-adjoint-fmat
;;   (implies (and (fmatp a n n) (natp n) (> n 1))
;;            (equal (fmat* a (adjoint-fmat a n))
;;                   (fmat-scalar-mul (fdet a n) (id-fmat n)))))


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

;; Let a be a matrix with m rows.  Check that the jth entry of row k of a is (f1) and that
;;  the jth entry of every other row of a is (f0):

(defun column-clear-p (a k j m)
  (if (zp m)
      t
    (and (= (nth j (nth (1- m) a))
	    (if (= (1- m) k) (f1) (f0)))
	 (column-clear-p a k j (1- m)))))

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

;; Next, we define a process that converts a matrix to row-echelon form by applying
;; a sequence of "elementary row operations".

;; 3 types of elementary row operations:

;; (1) Multiply row k by c:

(defund ero1 (a c k)
  (replace-row a k (flist-scalar-mul c (nth k a))))

;; (2) Add multiple of row j to row k:

(defund ero2 (a c j k)
  (replace-row a k (flist-add (flist-scalar-mul c (nth j a)) (nth k a))))

;; (3) Interchange rows j and k:

(defund ero3 (a j k)
  (replace-row (replace-row a k (nth j a)) j (nth k a)))

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

;; Convert a to row-echelon form:

(defund row-reduce (a)
  (row-reduce-aux a (len a) 0))

;; (defthmd row-echelon-p-row-reduce
;;   (implies (and (natp m) (natp n) (fmatp a m n))
;;            (row-echelon-p (row-reduce a))))

;; The row rank of a is the number of nonzero rows of (row-reduce a):

(defun num-nonzero-rows (a)
  (if (consp a)
      (if (flist0p (car a))
          0
	(1+ (num-nonzero-rows (cdr a))))
    0))

(defun row-rank (a)
  (num-nonzero-rows (row-reduce a)))


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

;; The list of row operations applied by clear-column:

(defun clear-column-ops (a k j m)
  (if (zp m)
      ()
    (if (= k (1- m))
        (clear-column-ops a k j (1- m))
      (cons (list 2 (f- (nth j (nth (1- m) a))) k (1- m))
	    (clear-column-ops (ero2 a (f- (nth j (nth (1- m) a))) k (1- m)) k j (1- m))))))

;; The list of row operations applied by row-reduce-step:

(defund row-reduce-step-ops (a m k i j)
  (cons (list 1 (f/ (nth j (nth i a))) i)
        (cons (list 3 i k)
	      (clear-column-ops (ero3 (ero1 a (f/ (nth j (nth i a))) i)
				      i k)
			        k j m))))

;; The list of row operations applied by row-reduce-aux:

(defun row-reduce-aux-ops (a m k)
  (declare (xargs :measure (nfix (- m k))))
  (let* ((i (row-with-nonzero-at-least-index a m k))
	 (j (and i (first-nonzero (nth i a)))))
    (if (and (natp k) (natp m) (< k m) i)
        (append (row-reduce-step-ops a m k i j)
	        (row-reduce-aux-ops (row-reduce-step a m k i j) m (1+ k)))                
      ())))

;; The list of row operations applied by row-reduce:

(defund row-reduce-ops (a)
  (row-reduce-aux-ops a (len a) 0))

;; The nxn elementary matrix corresponding to a row operation:

(defund elem-mat (op m)
  (apply-row-op op (id-fmat m)))
		  
;; The product of the elementary matrices corresponding to a list of row operations:

(defund row-ops-mat (ops m)
  (if (consp ops)
      (fmat* (row-ops-mat (cdr ops) m)
             (elem-mat (car ops) m))             
    (id-fmat m)))

(defund row-reduce-mat (a)
  (row-ops-mat (row-reduce-ops a) (len a)))

;; (defthmd row-ops-mat-row-reduce
;;   (implies (and (fmatp a m n) (posp m) (posp n))
;;            (equal (fmat* (row-reduce-mat a) a)
;;                   (row-reduce a))))


;;----------------------------------------------------------------------------------------
;; Invertibility
;;----------------------------------------------------------------------------------------

;; In this section, we focus on square matrices.  Given an nxn matrix a, we seek an nxn
;; matrix b such that (fmat* a b) = (fmat* b a) = (id-fmat n), which we shall call the
;; inverse of a.

;; Every elementary matrix has an inverse:

(defund invert-row-op (op)
  (case (car op)
    (1 (list 1 (f/ (cadr op)) (caddr op)))
    (2 (list 2 (f- (cadr op)) (caddr op) (cadddr op)))
    (3 op)))

;; Every product of elementary matrices has an inverse:

(defun invert-row-ops (ops)
  (if (consp ops)
      (append (invert-row-ops (cdr ops))
              (list (invert-row-op (car ops))))
    ()))

;; We shall show that a has an inverse iff (row-rank a) = n and that in this case,
;; the inverse of a is (row-reduce-mat a).  Thus, we define

(defund invertiblep (a n)
  (= (row-rank a) n))

(defund inverse-mat (a)
  (row-reduce-mat a))

;; a has an inverse iff (invertiblep a n):

;; (defthmd invertiblep-sufficient
;;   (implies (and (fmatp a n n) (posp n) (invertiblep a n))
;;            (let ((p (inverse-mat a)))
;;              (and (fmatp p n n)
;;                   (equal (fmat* a p) (id-fmat n))
;;                   (equal (fmat* p a) (id-fmat n))))))

;; (defthmd invertiblep-necessary
;;   (implies (and (fmatp a n n) (fmatp b n n) (posp n) (= (fmat* a b) (id-fmat n)))
;;            (invertiblep a n)))

;; a is invertible iff (fdet a n) <> (f0).

;; (defthmd invertiblep-fdet-not-zero
;;   (implies (and (fmatp a n n) (posp n) (invertiblep a n))
;;            (not (equal (fdet a n) (f0)))))

;; (defthmd fdet-not-invertiblep-zero
;;   (implies (and (fmatp a n n) (natp n) (> n 1) (not (equal (fdet a n) (f0))))
;;            (and (invertiblep a n)
;;                 (equal (inverse-mat a)
;;                        (fmat-scalar-mul (f/ (fdet a n)) (adjoint-fmat a n))))))


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

(defun solvablep (a b m)
  (null (find-nonzero (fmat* (row-reduce-mat a) (col-mat b))
                      (row-rank a)
		      m)))

;; (defthmd linear-equations-unsolvable-case
;;   (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
;;                 (not (solvablep a b m)))
;; 	      (not (solutionp x a b))))


;; Now suppose (find-nonzero br q m) = nil, i.e., (solvable a b m) = t.  Consider the matrices 
;; aq and bq consisting of the first q rows of ar and br, respectively, computed by the following:

(defun first-rows (q a)
  (if (zp q)
      ()
    (cons (car a) (first-rows (1- q) (cdr a)))))

;; If (row-rank a) = n, then there exists a unique solution:

;; (defthmd linear-equations-unique-solution-case
;;   (let* ((br (fmat* (row-reduce-mat a) (col-mat b)))
;;          (bq (first-rows n br)))
;;     (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
;;                   (solvablep a b m)
;; 	             (= (row-rank a) n))
;; 	        (iff (solutionp x a b)
;; 	             (equal x (col 0 bq))))))

;; Cramer's rule:

;; (defthmd cramer
;;   (implies (and (fmatp a n n) (natp n) (> n 1) (invertiblep a n)
;;                 (flistnp b n) (flistnp x n) (solutionp x a b)
;; 	   	   (natp i) (< i n))
;;            (equal (nth i x)
;; 	             (f* (f/ (fdet a n))
;; 		         (fdet (replace-col a i b) n)))))
	
;;---------------------------------------------

;; In the remaining case, we split (fdot (nth i aq) x) into 2 sums, corresponding to (1) the list
;; of indices of the leading 1s of the nonzero rows of aq and (2) the list of remaining indices:

(defun lead-inds (a)
  (if (and (consp a) (not (flist0p (car a))))
      (cons (first-nonzero (car a))
	    (lead-inds (cdr a)))
    ()))

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

;; x is a solution of our system of equations iff the following condition holds:

(defun solution-test (x aq bq l f k)
  (if (zp k)
      t
    (and (equal (nth (nth (1- k) l) x)
                (f+ (car (nth (1- k) bq))
		    (f- (fdot-select f (nth (1- k) aq) x))))
	 (solution-test x aq bq l f (1- k)))))

;; (defthmd linear-equations-solvable-case
;;   (let* ((ar (row-reduce a))
;;          (br (fmat* (row-reduce-mat a) (col-mat b)))
;;          (q (num-nonzero-rows ar))
;;          (aq (first-rows q ar))
;;          (bq (first-rows q br))
;;          (l (lead-inds aq))
;;          (f (free-inds aq n)))
;;     (implies (and (fmatp a m n) (posp m) (posp n) (flistnp b m) (flistnp x n)
;;                   (solvablep a b m))
;;              (iff (solutionp x a b)
;;                   (solution-test x aq bq l f q)))))                        

;; Note that if (len l) = n and f = nil, then the equation

;;   (nth (nth i l) x) = (f+ (car (nth i bq)) (f- (fdot-select f (nth i aq) x)))

;; reduces to

;;   (nth i x) = (car (nth i bq),

;; (solution-test x aq bq l f q) reduces to x = (col 0 bq), and linear-equations-solvable-case
;; reduces to the earlier result linear-equations-unique-solution-case.

;; Otherwise, the entries of x corresponding to the indices in (lead-inds aq) are determined
;; by the entries corresponding to (free-inds aq n).  Thus, there is a unique solution
;; corresponding to every assignment of values to the latter set of entries, and hence an
;; infinite number of solutions.  We shall revisit this result later in tconnection with the
;; vector space of solutions of a homogeneous system of equations.
