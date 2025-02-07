(in-package "DM")

(include-book "rtl/rel11/lib/util" :dir :system)
(include-book "projects/groups/lists" :dir :system)
(local (include-book "support/field"))

;; Field:

(encapsulate (((fp *) => *)                   ;field element recognizer
              ((f+ * *) => *) ((f* * *) => *) ;addition and multiplication
	      ((f0) => *) ((f1) => *)         ;identities
	      ((f- *) => *) ((f/ *) => *))    ;inverses 
  (local (defun fp (x) (rationalp x)))
  (local (defun f+ (x y) (+ x y)))
  (local (defun f* (x y) (* x y)))
  (local (defun f0 () 0))
  (local (defun f1 () 1))
  (local (defun f- (x) (- x)))
  (local (defun f/ (x) (/ x)))
  ;; Closure:
  (defthm f+closed (implies (and (fp x) (fp y)) (fp (f+ x y))))
  (defthm f*closed (implies (and (fp x) (fp y)) (fp (f* x y))))
  ;; Commutativity
  (defthmd f+comm (implies (and (fp x) (fp y)) (equal (f+ x y) (f+ y x))))
  (defthmd f*comm (implies (and (fp x) (fp y)) (equal (f* x y) (f* y x))))
  ;; Associativity:
  (defthmd f+assoc (implies (and (fp x) (fp y) (fp z)) (equal (f+ x (f+ y z)) (f+ (f+ x y) z))))
  (defthmd f*assoc (implies (and (fp x) (fp y) (fp z)) (equal (f* x (f* y z)) (f* (f* x y) z))))
  ;; Identity:
  (defthm fpf0 (fp (f0)))
  (defthm fpf1 (fp (f1)))
  (defthm f1f0 (not (equal (f1) (f0))))
  (defthm f0id (implies (fp x) (equal (f+ x (f0)) x)))
  (defthm f1id (implies (fp x) (equal (f* x (f1)) x)))
  ;; Inverse:
  (defthm fpf- (implies (fp x) (fp (f- x))))
  (defthm fpf/ (implies (and (fp x) (not (equal x (f0)))) (fp (f/ x))))
  (defthm f+inv (implies (fp x) (equal (f+ x (f- x)) (f0))))
  (defthm f*inv (implies (and (fp x) (not (equal x (f0)))) (equal (f* x (f/ x)) (f1))))
  ;; Distributivity:
  (defthm fdist (implies (and (fp x) (fp y) (fp z)) (equal (f* x (f+ y z)) (f+ (f* x y) (f* x z))))))

;; Trivial consequences of the axioms:

(defthm f0id2
  (implies (fp x) (equal (f+ (f0) x) x)))

(defthm f1id2
  (implies (fp x) (equal (f* (f1) x) x)))

(defthm f+inv2
  (implies (fp x) (equal (f+ (f- x) x) (f0))))

(defthm f-f0
  (equal (f- (f0)) (f0)))

(defthm f*inv2
  (implies (and (fp x) (not (equal x (f0)))) (equal (f* (f/ x) x) (f1))))

(defthm f0*f0
  (implies (fp x) (equal (f* x (f0)) (f0))))

(defthm f0*f02
  (implies (fp x) (equal (f* (f0) x) (f0))))

(defthm fdist-comm
  (implies (and (fp x) (fp y) (fp z))
	   (equal (f* (f+ x y) z)
		  (f+ (f* x z) (f* y z)))))

(defthmd f*f0
  (implies (and (fp x) (fp y))
	   (iff (equal (f* x y) (f0))
		(or (equal x (f0)) (equal y (f0))))))

(defthm f/f0
  (implies (and (fp x) (equal (f/ x) (f0)))
	   (equal (f0) x)))

(defthm f-f-
  (implies (fp x)
           (equal (f- (f- x)) x)))

(defthm f/f1
  (implies (and (fp x) (not (= x (f0))))
	   (iff (equal (f/ x) (f1))
		(equal x (f1)))))

(defthm f/f/
  (implies (and (fp x) (not (= x (f0))))
	   (equal (f/ (f/ x)) x)))

(defthmd f+left-cancel
  (implies (and (fp x) (fp y) (fp z))
           (iff (equal (f+ x z) (f+ y z))
	        (equal x y))))

(defthmd f+right-cancel
  (implies (and (fp x) (fp y) (fp z))
           (iff (equal (f+ z x) (f+ z y))
	        (equal x y))))
  
(defthmd f-unique
  (implies (and (fp x) (fp y) (= (f+ x y) (f0)))
	   (equal (f- x) y)))

(defthmd f-f+
  (implies (and (fp x) (fp y))
	   (equal (f- (f+ x y))
		  (f+ (f- x) (f- y)))))

(defthmd f-f*
  (implies (and (fp x) (fp y))
	   (equal (f- (f* x y))
		  (f* x (f- y)))))


;;----------------------------------------------------------------------------------------
;; Lists of Field Elements
;;----------------------------------------------------------------------------------------

(defun flistp (l)
  (if (consp l)
      (and (fp (car l)) (flistp (cdr l)))
    (null l)))

(defthm fp-member
  (implies (and (flistp l) (member x l))
           (fp x)))

;; Sum of the members of l:

(defun flist-sum (l)
  (if (consp l)
      (f+ (car l) (flist-sum (cdr l)))
    (f0)))

(in-theory (disable (flist-sum)))

(defthm fp-flist-sum
  (implies (flistp l)
           (fp (flist-sum l))))

;; Product of the members of l:

(defun flist-prod (l)
  (if (consp l)
      (f* (car l) (flist-prod (cdr l)))
    (f1)))

(in-theory (disable (flist-prod)))

(defthm fp-flist-prod
  (implies (flistp l)
           (fp (flist-prod l))))

;; List of field elements of length n:

(defun flistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (fp (car x))
	 (flistnp (cdr x) (1- n)))))

(defthm fp-flistnp
  (implies (and (flistnp x n) (natp n) (natp i) (< i n))
	   (fp (nth i x))))

(defthm len-flist
  (implies (and (natp n) (flistnp x n))
	   (equal (len x) n)))

(defthm true-listp-flist
  (implies (flistnp x n)
	   (true-listp x)))

(defthm fp-flistn-sum
  (implies (flistnp x n)
           (fp (flist-sum x))))

(defthm fp-flistn-prod
  (implies (flistnp x n)
           (fp (flist-prod x))))

;; Every member of x is (f0):

(defun flist0p (x)
  (if (consp x)
      (and (= (car x) (f0))
           (flist0p (cdr x)))
    (null x)))

(defthm nth-flist0p
  (implies (and (flist0p x) (natp i) (< i (len x)))
           (equal (nth i x) (f0))))

;; List of n copies of (f0):

(defun flistn0 (n)
  (if (zp n)
      () 
    (cons (f0) (flistn0 (1- n)))))

(defthm flistnp-flistn0
  (flistnp (flistn0 n) n))

(defthm flist0p-flistn0
  (flist0p (flistn0 n)))

(defthmd flist0p-flistn0-len
  (implies (flist0p x)
           (equal (flistn0 (len x)) x)))

(defthm nth-flistn0
  (implies (and (natp n) (natp i) (< i n))
           (equal (nth i (flistn0 n))
	          (f0))))

;; List of sums of corresponding members of x and y:

(defun flist-add (x y)
  (if (consp x)
      (cons (f+ (car x) (car y))
            (flist-add (cdr x) (cdr y)))
    ()))

(defthm flist-add-flist0p
  (implies (and (flistnp x n) (flistnp y n) (flist0p y))
	   (equal (flist-add x y) x)))

(defthm flist-add-flistn0
  (implies (flistnp x n)
	   (equal (flist-add (flistn0 n) x)
		  x)))

(defthm flistnp-flist-add
  (implies (and (flistnp x n) (flistnp y n))
	   (flistnp (flist-add x y) n)))

(defthm nth-flist-add
  (implies (and (flistnp x n) (flistnp y n) (natp n) (natp i) (< i n))
	   (equal (nth i (flist-add x y))
		  (f+ (nth i x) (nth i y)))))

(defthmd flist-add-comm
  (implies (and (flistnp x n) (flistnp y n))
	   (equal (flist-add x y)
		  (flist-add y x))))

(defthmd flist-add-assoc
  (implies (and (flistnp x n) (flistnp y n) (flistnp z n))
	   (equal (flist-add x (flist-add y z))
		  (flist-add (flist-add x y) z))))

;; List of products of corresponding members of x and y:

(defun flist-mul (x y)
  (if (consp x)
      (cons (f* (car x) (car y))
	    (flist-mul (cdr x) (cdr y)))
    ()))

(defthm flistnp-flist-mul
  (implies (and (flistnp x n) (flistnp y n))
	   (flistnp (flist-mul x y) n)))

;; Multiply each member of x by c:

(defun flist-scalar-mul (c x)
  (if (consp x)
      (cons (f* c (car x))
            (flist-scalar-mul c (cdr x)))
    ()))

(defthm flistnp-flist-scalar-mul
  (implies (and (fp c) (flistnp x n))
	   (flistnp (flist-scalar-mul c x) n)))

(defthm flist0p-scalar-mul
  (implies (and (flist0p x) (fp c))
           (flist0p (flist-scalar-mul c x))))

(defthm flist-scalar-mul-f0
  (implies (flistnp x n)
	   (equal (flist-scalar-mul (f0) x)
		  (flistn0 n))))

(defthm flist-scalar-mul-f1
  (implies (flistnp x n)
	   (equal (flist-scalar-mul (f1) x)
		  x)))

(defthm nth-flist-scalar-mul
  (implies (and (fp c) (flistnp x n) (natp n) (natp i) (< i n))
	   (equal (nth i (flist-scalar-mul c x))
		  (f* c (nth i x)))))

(defthm flist-scalar-mul-assoc
  (implies (and (fp c) (fp d) (flistnp x n))
	   (equal (flist-scalar-mul c (flist-scalar-mul d x))
		  (flist-scalar-mul (f* c d) x))))

(defthm flist-scalar-mul-dist-1
  (implies (and (fp c) (flistnp x n) (flistnp y n))
	   (equal (flist-scalar-mul c (flist-add x y))
		  (flist-add (flist-scalar-mul c x) (flist-scalar-mul c y)))))

(defthm flist-scalar-mul-dist-2
  (implies (and (fp c) (fp d) (flistnp x n))
	   (equal (flist-scalar-mul (f+ c d) x)
		  (flist-add (flist-scalar-mul c x) (flist-scalar-mul d x)))))

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

(defthm nth-fdot-list
  (implies (and (natp j) (< j (len l)))
           (equal (nth j (fdot-list x l))
	          (fdot x (nth j l)))))


;;------------------------------------------

;; The following results are useful in the analysis of determinants.

;; Let fval be a function that maps the domain recognized by the predicate
;; fargp into the field f:

(encapsulate (((fval *) => *) ((fargp *) => *))
  (local (defun fval (x) (declare (ignore x)) (f0)))
  (local (defun fargp (x) (declare (ignore x)) t))
  (defthm farg-fval (implies (fargp x) (fp (fval x)))))

(defun farg-listp (l)
  (if (consp l)
      (and (fargp (car l))
           (farg-listp (cdr l)))
    t))

(defthm member-farg-list
  (implies (and (farg-listp l) (member x l))
           (fp (fval x))))

;; Given a list l of elements of the domain, compote the sum of the values of the members of l:

(defun fval-sum (l)
  (if (consp l)
      (f+ (fval (car l))
          (fval-sum (cdr l)))
    (f0)))

(in-theory (disable (fval-sum)))

(defthm fp-fval-sum
  (implies (farg-listp l)
           (fp (fval-sum l))))

;; Given 2 lists l and m of elements of the domain, compute the sum of the values of (append l m):

(defthmd fval-sum-append
  (implies (and (farg-listp l) (farg-listp m))
           (equal (fval-sum (append l m))
	          (f+ (fval-sum l) (fval-sum m)))))

;; (fval-sum l) is invariant under permutation of l:

(defthmd fval-sum-permutationp
  (implies (and (farg-listp l) (farg-listp m) (permutationp l m))
	        (equal (fval-sum l) (fval-sum m))))

(defthmd fval-sum-permp
  (implies (and (dlistp l) (dlistp m) (farg-listp l) (farg-listp m) (permp l m))
	        (equal (fval-sum l) (fval-sum m))))

;; Repeat for products:

(defun fval-prod (l)
  (if (consp l)
      (f* (fval (car l))
          (fval-prod (cdr l)))
    (f1)))

(in-theory (disable (fval-prod)))

(defthm fp-fval-prod
  (implies (farg-listp l)
           (fp (fval-prod l))))

;; Given 2 lists l and m of elements of the domain, compute the product of the values of (append l m):

(defthmd fval-prod-append
  (implies (and (farg-listp l) (farg-listp m))
           (equal (fval-prod (append l m))
	          (f* (fval-prod l) (fval-prod m)))))

;; (fval-prod l) is invariant under permutation of l:

(defthmd fval-prod-permutationp
  (implies (and (farg-listp l) (farg-listp m) (permutationp l m))
	        (equal (fval-prod l) (fval-prod m))))

(defthmd fval-prod-permp
  (implies (and (dlistp l) (dlistp m) (farg-listp l) (farg-listp m) (permp l m))
	        (equal (fval-prod l) (fval-prod m))))


;; In the simplest case, (fargp x) = (fp x) and (fval x) = x.

;; flist-sum is invariant under permutation:

(defthmd flist-sum-permutationp
  (implies (and (flistp l) (flistp m) (permutationp l m))
	        (equal (flist-sum l) (flist-sum m))))

(defthmd flist-sum-permp
  (implies (and (dlistp l) (dlistp m) (flistp l) (flistp m) (permp l m))
	        (equal (flist-sum l) (flist-sum m))))

;; flist-prod is invariant under permutation:

(defthmd flist-prod-permutationp
  (implies (and (flistp l) (flistp m) (permutationp l m))
	        (equal (flist-prod l) (flist-prod m))))

(defthmd flist-prod-permp
  (implies (and (dlistp l) (dlistp m) (flistp l) (flistp m) (permp l m))
	        (equal (flist-prod l) (flist-prod m))))
