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

(defthmd f+cancel
  (implies (and (fp x) (fp y) (fp z))
           (iff (equal (f+ x z) (f+ y z))
	        (equal x y))))
  

;;----------------------------------------------------------------------------------------
;; Lists of Field Elements
;;----------------------------------------------------------------------------------------

;; List of field elements of length n:

(defun flistp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (fp (car x))
	 (flistp (cdr x) (1- n)))))

(defthm fp-flistp
  (implies (and (flistp x n) (natp n) (natp i) (< i n))
	   (fp (nth i x))))

(defthm len-flist
  (implies (and (natp n) (flistp x n))
	   (equal (len x) n)))

(defthm true-listp-flist
  (implies (flistp x n)
	   (true-listp x)))

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

(defun flist0 (n)
  (if (zp n)
      () 
    (cons (f0) (flist0 (1- n)))))

(defthm flistp-flist0
  (flistp (flist0 n) n))

(defthm flist0p-flist0
  (flist0p (flist0 n)))

(defthmd flist0p-flist0-len
  (implies (flist0p x)
           (equal (flist0 (len x)) x)))

(defthm nth-flist0
  (implies (and (natp n) (natp i) (< i n))
           (equal (nth i (flist0 n))
	          (f0))))

;; List of sums of corresponding members of x and y:

(defun flist-add (x y)
  (if (consp x)
      (cons (f+ (car x) (car y))
            (flist-add (cdr x) (cdr y)))
    ()))

(defthm flist-add-flist0p
  (implies (and (flistp x n) (flistp y n) (flist0p y))
	   (equal (flist-add x y) x)))

(defthm flist-add-flist0
  (implies (flistp x n)
	   (equal (flist-add (flist0 n) x)
		  x)))

(defthm flistp-flist-add
  (implies (and (flistp x n) (flistp y n))
	   (flistp (flist-add x y) n)))

(defthm nth-flist-add
  (implies (and (flistp x n) (flistp y n) (natp n) (natp i) (< i n))
	   (equal (nth i (flist-add x y))
		  (f+ (nth i x) (nth i y)))))

(defthmd flist-add-comm
  (implies (and (flistp x n) (flistp y n))
	   (equal (flist-add x y)
		  (flist-add y x))))

(defthmd flist-add-assoc
  (implies (and (flistp x n) (flistp y n) (flistp z n))
	   (equal (flist-add x (flist-add y z))
		  (flist-add (flist-add x y) z))))

;; List of products of corresponding members of x and y:

(defun flist-mul (x y)
  (if (consp x)
      (cons (f* (car x) (car y))
	    (flist-mul (cdr x) (cdr y)))
    ()))

(defthm flistp-flist-mul
  (implies (and (flistp x n) (flistp y n))
	   (flistp (flist-mul x y) n)))

;; Multiply each member of x by c:

(defun flist-scalar-mul (c x)
  (if (consp x)
      (cons (f* c (car x))
            (flist-scalar-mul c (cdr x)))
    ()))

(defthm flistp-flist-scalar-mul
  (implies (and (fp c) (flistp x n))
	   (flistp (flist-scalar-mul c x) n)))

(defthm flist0p-scvalar-mul
  (implies (and (flist0p x) (fp c))
           (flist0p (flist-scalar-mul c x))))

(defthm flist-scalar-mul-f0
  (implies (flistp x n)
	   (equal (flist-scalar-mul (f0) x)
		  (flist0 n))))

(defthm nth-flist-scalar-mul
  (implies (and (fp c) (flistp x n) (natp n) (natp i) (< i n))
	   (equal (nth i (flist-scalar-mul c x))
		  (f* c (nth i x)))))

(defthm flist-scalar-mul-assoc
  (implies (and (fp c) (fp d) (flistp x n))
	   (equal (flist-scalar-mul c (flist-scalar-mul d x))
		  (flist-scalar-mul (f* c d) x))))

(defthm flist-scalar-mul-dist-1
  (implies (and (fp c) (flistp x n) (flistp y n))
	   (equal (flist-scalar-mul c (flist-add x y))
		  (flist-add (flist-scalar-mul c x) (flist-scalar-mul c y)))))

(defthm flist-scalar-mul-dist-2
  (implies (and (fp c) (fp d) (flistp x n))
	   (equal (flist-scalar-mul (f+ c d) x)
		  (flist-add (flist-scalar-mul c x) (flist-scalar-mul d x)))))

;; Sum of the members of x:

(defund flist-sum (x)
  (if (consp x)
      (f+ (car x) (flist-sum (cdr x)))
    (f0)))

(defthm fp-flist-sum
  (implies (flistp x n)
           (fp (flist-sum x))))
