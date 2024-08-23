(in-package "DM")

(include-book "rtl/rel11/lib/util" :dir :system)
(include-book "projects/groups/lists" :dir :system)

;; Characterization of a commutative ring with unity as a constrained set of functions:

(encapsulate (((rp *) => *)                   ;ring element recognizer
              ((r+ * *) => *) ((r* * *) => *) ;addition and multiplication
	      ((r0) => *) ((r1) => *)         ;identities
	      ((r- *) => *))                  ;additive inverse
  (local (defun rp (x) (rationalp x)))
  (local (defun r+ (x y) (+ x y)))
  (local (defun r* (x y) (* x y)))
  (local (defun r0 () 0))
  (local (defun r1 () 1))
  (local (defun r- (x) (- x)))
  ;; Closure:
  (defthm r+closed (implies (and (rp x) (rp y)) (rp (r+ x y))))
  (defthm r*closed (implies (and (rp x) (rp y)) (rp (r* x y))))
  ;; Commutativity
  (defthmd r+comm (implies (and (rp x) (rp y)) (equal (r+ x y) (r+ y x))))
  (defthmd r*comm (implies (and (rp x) (rp y)) (equal (r* x y) (r* y x))))
  ;; Associativity:
  (defthmd r+assoc (implies (and (rp x) (rp y) (rp z)) (equal (r+ x (r+ y z)) (r+ (r+ x y) z))))
  (defthmd r*assoc (implies (and (rp x) (rp y) (rp z)) (equal (r* x (r* y z)) (r* (r* x y) z))))
  ;; Identity:
  (defthm rpr0 (rp (r0)))
  (defthm rpr1 (rp (r1)))
  (defthm r1r0 (not (equal (r1) (r0))))
  (defthm r0id (implies (rp x) (equal (r+ x (r0)) x)))
  (defthm r1id (implies (rp x) (equal (r* x (r1)) x)))
  ;; Inverse:
  (defthm rpr- (implies (rp x) (rp (r- x))))
  (defthm r+inv (implies (rp x) (equal (r+ x (r- x)) (r0))))
  ;; Distributivity:
  (defthm rdist (implies (and (rp x) (rp y) (rp z)) (equal (r* x (r+ y z)) (r+ (r* x y) (r* x z))))))

;; Trivial consequences of the axioms:

(defthm r0id2
  (implies (rp x) (equal (r+ (r0) x) x))
  :hints (("Goal" :use ((:instance r+comm (y (r0)))))))

(defthm r1id2
  (implies (rp x) (equal (r* (r1) x) x))
  :hints (("Goal" :use ((:instance r*comm (y (r1)))))))

(defthm r+inv2
  (implies (rp x) (equal (r+ (r- x) x) (r0)))
  :hints (("Goal" :use ((:instance r+comm (y (r- x)))))))

(defthm r-r0
  (equal (r- (r0)) (r0))
  :hints (("Goal" :in-theory (disable r0id2)
	          :use ((:instance r0id2 (x (r- (r0))))))))

(defthm r0*r0
  (implies (rp x) (equal (r* x (r0)) (r0)))
  :hints (("Goal" :in-theory (disable r+assoc r+inv r1id r0id rdist r0id2 r1id2)
                  :use (r+inv r1id
		        (:instance r0id (x (r* x (r0))))
		        (:instance r+assoc (x (r* x (r0))) (y x) (z (r- x)))
			(:instance rdist (y (r0)) (z (r1)))
			(:instance r0id2 (x (r1)))))))

(defthm r0*r02
  (implies (rp x) (equal (r* (r0) x) (r0)))
  :hints (("Goal" :use (r0*r0 (:instance r*comm (y (r0)))))))

(defthm rdist-comm
  (implies (and (rp x) (rp y) (rp z))
	   (equal (r* (r+ x y) z)
		  (r+ (r* x z) (r* y z))))
  :hints (("Goal" :use ((:instance r*comm (x z) (y (r+ x y)))
			(:instance r*comm (x z))
			(:instance r*comm (y z))))))

(defthm r-r-
  (implies (rp x)
           (equal (r- (r- x)) x))
  :hints (("Goal" :use ((:instance r+assoc (x (r- (r- x))) (y (r- x)) (z x))))))

(defthmd r+left-cancel
  (implies (and (rp x) (rp y) (rp z))
           (iff (equal (r+ x z) (r+ y z))
	        (equal x y)))
  :hints (("Goal" :use ((:instance r+assoc (y z) (z (r- z)))
                        (:instance r+assoc (x y) (y z) (z (r- z)))))))

(defthmd r+right-cancel
  (implies (and (rp x) (rp y) (rp z))
           (iff (equal (r+ z x) (r+ z y))
	        (equal x y)))
  :hints (("Goal" :use (r+left-cancel
			(:instance r+comm (y z))
                        (:instance r+comm (x z))))))
  
(defthmd r-unique
  (implies (and (rp x) (rp y) (= (r+ x y) (r0)))
	   (equal (r- x) y))
  :hints (("Goal" :use (r+inv
			(:instance r+right-cancel (z x) (x (r- x)))))))

(defthmd r-r+
  (implies (and (rp x) (rp y))
	   (equal (r- (r+ x y))
		  (r+ (r- x) (r- y))))
  :hints (("Goal" :use (r+comm
			(:instance r+assoc (x (r+ x y)) (y (r- x)) (z (r- y)))
			(:instance r+assoc (x y) (y x) (z (r- x)))
			(:instance r-unique (x (r+ x y)) (y (r+ (r- x) (r- y))))))))

(defthmd r-r*
  (implies (and (rp x) (rp y))
	   (equal (r- (r* x y))
		  (r* x (r- y))))
  :hints (("Goal" :use ((:instance rdist (z (r- y)))
			(:instance r-unique (x (r* x y)) (y (r* x (r- y))))))))
		

;;----------------------------------------------------------------------------------------
;; Lists of Ring Elements
;;----------------------------------------------------------------------------------------

(defun rlistp (l)
  (if (consp l)
      (and (rp (car l)) (rlistp (cdr l)))
    (null l)))

(defthm rp-member
  (implies (and (rlistp l) (member x l))
           (rp x)))

;; Sum of the members of l:

(defun rlist-sum (l)
  (if (consp l)
      (r+ (car l) (rlist-sum (cdr l)))
    (r0)))

(in-theory (disable (rlist-sum)))

(defthm rp-rlist-sum
  (implies (rlistp l)
           (rp (rlist-sum l))))

;; Product of the members of l:

(defun rlist-prod (l)
  (if (consp l)
      (r* (car l) (rlist-prod (cdr l)))
    (r1)))

(in-theory (disable (rlist-prod)))

(defthm rp-rlist-prod
  (implies (rlistp l)
           (rp (rlist-prod l))))

;; List of ring elements of length n:

(defun rlistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (rp (car x))
	 (rlistnp (cdr x) (1- n)))))

(defthm rp-rlistnp
  (implies (and (rlistnp x n) (natp n) (natp i) (< i n))
	   (rp (nth i x))))

(defthm len-rlist
  (implies (and (natp n) (rlistnp x n))
	   (equal (len x) n)))

(defthm true-listp-rlist
  (implies (rlistnp x n)
	   (true-listp x)))

(defthm rp-rlistn-sum
  (implies (rlistnp x n)
           (rp (rlist-sum x))))

(defthm rp-rlistn-prod
  (implies (rlistnp x n)
           (rp (rlist-prod x))))

;; Every member of x is (r0):

(defun rlist0p (x)
  (if (consp x)
      (and (= (car x) (r0))
           (rlist0p (cdr x)))
    (null x)))

(defthm nth-rlist0p
  (implies (and (rlist0p x) (natp i) (< i (len x)))
           (equal (nth i x) (r0))))

;; List of n copies of (r0):

(defun rlistn0 (n)
  (if (zp n)
      () 
    (cons (r0) (rlistn0 (1- n)))))

(defthm rlistnp-rlistn0
  (rlistnp (rlistn0 n) n))

(defthm rlist0p-rlistn0
  (rlist0p (rlistn0 n)))

(defthmd rlist0p-rlistn0-len
  (implies (rlist0p x)
           (equal (rlistn0 (len x)) x)))

(defun nth-rlistn0-induct (i n)
  (if (zp n)
      (list i)
    (list (nth-rlistn0-induct (1- i) (1- n)))))

(defthm nth-rlistn0
  (implies (and (natp n) (natp i) (< i n))
           (equal (nth i (rlistn0 n))
	          (r0)))
  :hints (("Goal" :induct (nth-rlistn0-induct i n))))

;; List of sums of corresponding members of x and y:

(defun rlist-add (x y)
  (if (consp x)
      (cons (r+ (car x) (car y))
            (rlist-add (cdr x) (cdr y)))
    ()))

(defthm rlist-add-rlist0p
  (implies (and (rlistnp x n) (rlistnp y n) (rlist0p y))
	   (equal (rlist-add x y) x)))

(defthm rlist-add-rlistn0
  (implies (rlistnp x n)
	   (equal (rlist-add (rlistn0 n) x)
		  x)))

(defthm rlistnp-rlist-add
  (implies (and (rlistnp x n) (rlistnp y n))
	   (rlistnp (rlist-add x y) n)))

(defthm nth-rlist-add
  (implies (and (rlistnp x n) (rlistnp y n) (natp n) (natp i) (< i n))
	   (equal (nth i (rlist-add x y))
		  (r+ (nth i x) (nth i y)))))

(defthmd rlist-add-comm
  (implies (and (rlistnp x n) (rlistnp y n))
	   (equal (rlist-add x y)
		  (rlist-add y x)))
  :hints (("Subgoal *1/3" :use ((:instance r+comm (x (car x)) (y (car y)))))))

(defthmd rlist-add-assoc
  (implies (and (rlistnp x n) (rlistnp y n) (rlistnp z n))
	   (equal (rlist-add x (rlist-add y z))
		  (rlist-add (rlist-add x y) z)))
  :hints (("Subgoal *1/4" :in-theory (enable r+assoc))))

;; List of products of corresponding members of x and y:

(defun rlist-mul (x y)
  (if (consp x)
      (cons (r* (car x) (car y))
	    (rlist-mul (cdr x) (cdr y)))
    ()))

(defthm rlistnp-rlist-mul
  (implies (and (rlistnp x n) (rlistnp y n))
	   (rlistnp (rlist-mul x y) n)))

;; Multiply each member of x by c:

(defun rlist-scalar-mul (c x)
  (if (consp x)
      (cons (r* c (car x))
            (rlist-scalar-mul c (cdr x)))
    ()))

(defthm rlistnp-rlist-scalar-mul
  (implies (and (rp c) (rlistnp x n))
	   (rlistnp (rlist-scalar-mul c x) n)))

(defthm rlist0p-scalar-mul
  (implies (and (rlist0p x) (rp c))
           (rlist0p (rlist-scalar-mul c x))))

(defthm rlist-scalar-mul-r0
  (implies (rlistnp x n)
	   (equal (rlist-scalar-mul (r0) x)
		  (rlistn0 n))))

(defthm rlist-scalar-mul-r1
  (implies (rlistnp x n)
	   (equal (rlist-scalar-mul (r1) x)
		  x)))

(defthm nth-rlist-scalar-mul
  (implies (and (rp c) (rlistnp x n) (natp n) (natp i) (< i n))
	   (equal (nth i (rlist-scalar-mul c x))
		  (r* c (nth i x)))))

(defthm rlist-scalar-mul-assoc
  (implies (and (rp c) (rp d) (rlistnp x n))
	   (equal (rlist-scalar-mul c (rlist-scalar-mul d x))
		  (rlist-scalar-mul (r* c d) x)))
  :hints (("Goal" :in-theory (enable r*assoc))))

(defthm rlist-scalar-mul-dist-1
  (implies (and (rp c) (rlistnp x n) (rlistnp y n))
	   (equal (rlist-scalar-mul c (rlist-add x y))
		  (rlist-add (rlist-scalar-mul c x) (rlist-scalar-mul c y)))))

(defthm rlist-scalar-mul-dist-2
  (implies (and (rp c) (rp d) (rlistnp x n))
	   (equal (rlist-scalar-mul (r+ c d) x)
		  (rlist-add (rlist-scalar-mul c x) (rlist-scalar-mul d x))))
  :hints (("Subgoal *1/2" :use ((:instance r*comm (x c) (y (car x)))
				(:instance r*comm (x d) (y (car x)))
				(:instance r*comm (x (r+ c d)) (y (car x)))
				(:instance rdist (x (car x)) (y c) (z d))))))


;;------------------------------------------

;; The following results are useful in the analysis of determinants.

;; Let rval be a function that maps the domain recognized by the predicate
;; rargp into the ring r:

(encapsulate (((rval *) => *) ((rargp *) => *))
  (local (defun rval (x) (declare (ignore x)) (r0)))
  (local (defun rargp (x) (declare (ignore x)) t))
  (defthm rarg-rval (implies (rargp x) (rp (rval x)))))

(defun rarg-listp (l)
  (if (consp l)
      (and (rargp (car l))
           (rarg-listp (cdr l)))
    t))

(defthm member-rarg-list
  (implies (and (rarg-listp l) (member x l))
           (rp (rval x))))

;; Given a list l of elements of the domain, compote the sum of the values of the members of l:

(defun rval-sum (l)
  (if (consp l)
      (r+ (rval (car l))
          (rval-sum (cdr l)))
    (r0)))

(in-theory (disable (rval-sum)))

(defthm rp-rval-sum
  (implies (rarg-listp l)
           (rp (rval-sum l))))

;; Given 2 lists l and m of elements of the domain, compute the sum of the values of (append l m):

(defthmd rval-sum-append
  (implies (and (rarg-listp l) (rarg-listp m))
           (equal (rval-sum (append l m))
	          (r+ (rval-sum l) (rval-sum m))))
  :hints (("Subgoal *1/3" :use ((:instance r+assoc (x (rval (car l))) (y (rval-sum (cdr l))) (z (rval-sum m)))))))

;; (rval-sum l) is invariant under permutation of l:

(local-defthm rarg-list-remove1
  (implies (rarg-listp l)
           (rarg-listp (remove1 x l))))

(local-defthmd rval-sum-remove1
  (implies (and (rarg-listp l) (member x l))
           (equal (r+ (rval x) (rval-sum (remove1 x l)))
	          (rval-sum l)))
  :hints (("Subgoal *1/5" :use ((:instance r+assoc (x (rval (car l))) (y (rval x))
                                                   (z (rval-sum (remove1 x (cdr l)))))
                                (:instance r+comm (x (rval x)) (y (rval (car l))))
				(:instance r+assoc (x (rval x)) (y (rval (car l)))
				                   (z (rval-sum (remove1 x (cdr l)))))))))

(defthmd rval-sum-permutationp
  (implies (and (rarg-listp l) (rarg-listp m) (permutationp l m))
	        (equal (rval-sum l) (rval-sum m)))
  :hints (("Subgoal *1/4" :use ((:instance rval-sum-remove1 (x (car l)) (l m))))))

(defthmd rval-sum-permp
  (implies (and (dlistp l) (dlistp m) (rarg-listp l) (rarg-listp m) (permp l m))
	        (equal (rval-sum l) (rval-sum m)))
  :hints (("Goal" :use (rval-sum-permutationp permp-permutationp))))

;; Repeat for products:

(defun rval-prod (l)
  (if (consp l)
      (r* (rval (car l))
          (rval-prod (cdr l)))
    (r1)))

(in-theory (disable (rval-prod)))

(defthm rp-rval-prod
  (implies (rarg-listp l)
           (rp (rval-prod l))))

;; Given 2 lists l and m of elements of the domain, compute the product of the values of (append l m):

(defthmd rval-prod-append
  (implies (and (rarg-listp l) (rarg-listp m))
           (equal (rval-prod (append l m))
	          (r* (rval-prod l) (rval-prod m))))
  :hints (("Subgoal *1/3" :use ((:instance r*assoc (x (rval (car l))) (y (rval-prod (cdr l))) (z (rval-prod m)))))))

;; (rval-prod l) is invariant under permutation of l:

(local-defthm rarg-list-remove1
  (implies (rarg-listp l)
           (rarg-listp (remove1 x l))))

(local-defthmd rval-prod-remove1
  (implies (and (rarg-listp l) (member x l))
           (equal (r* (rval x) (rval-prod (remove1 x l)))
	          (rval-prod l)))
  :hints (("Subgoal *1/5" :use ((:instance r*assoc (x (rval (car l))) (y (rval x))
                                                   (z (rval-prod (remove1 x (cdr l)))))
                                (:instance r*comm (x (rval x)) (y (rval (car l))))
				(:instance r*assoc (x (rval x)) (y (rval (car l)))
				                   (z (rval-prod (remove1 x (cdr l)))))))))

(defthmd rval-prod-permutationp
  (implies (and (rarg-listp l) (rarg-listp m) (permutationp l m))
	        (equal (rval-prod l) (rval-prod m)))
  :hints (("Subgoal *1/4" :use ((:instance rval-prod-remove1 (x (car l)) (l m))))))

(defthmd rval-prod-permp
  (implies (and (dlistp l) (dlistp m) (rarg-listp l) (rarg-listp m) (permp l m))
	        (equal (rval-prod l) (rval-prod m)))
  :hints (("Goal" :use (rval-prod-permutationp permp-permutationp))))


;; In the simplest case, (rargp x) = (rp x) and (rval x) = x.

;; rlist-sum is invariant under permutation:

(local-defthm rlistp-remove1
  (implies (rlistp l)
           (rlistp (remove1 x l))))

(local-defthm rp-rlist-sum-remove1
  (implies (rlistp l)
           (rp (rlist-sum (remove1 x l)))))

(local-defthmd rlist-sum-remove1
  (implies (and (rlistp l) (member x l))
           (equal (r+ x (rlist-sum (remove1 x l)))
	          (rlist-sum l)))
  :hints (("Subgoal *1/5" :use ((:instance r+assoc (x (car l)) (y x) (z (rlist-sum (remove1 x (cdr l)))))
                                (:instance r+comm (y (car l)))
				(:instance r+assoc (y (car l)) (z (rlist-sum (remove1 x (cdr l)))))))))

(defthmd rlist-sum-permutationp
  (implies (and (rlistp l) (rlistp m) (permutationp l m))
	        (equal (rlist-sum l) (rlist-sum m)))
  :hints (("Subgoal *1/4" :use ((:instance rlist-sum-remove1 (x (car l)) (l m))))))

(defthmd rlist-sum-permp
  (implies (and (dlistp l) (dlistp m) (rlistp l) (rlistp m) (permp l m))
	        (equal (rlist-sum l) (rlist-sum m)))
  :hints (("Goal" :use (rlist-sum-permutationp permp-permutationp))))

(in-theory (disable (rlist-sum)))

;; rlist-prod is invariant under permutation:

(local-defthm rp-rlist-prod-remove1
  (implies (rlistp l)
           (rp (rlist-prod (remove1 x l)))))

(local-defthmd rlist-prod-remove1
  (implies (and (rlistp l) (member x l))
           (equal (r* x (rlist-prod (remove1 x l)))
	          (rlist-prod l)))
  :hints (("Subgoal *1/5" :use ((:instance r*assoc (x (car l)) (y x) (z (rlist-prod (remove1 x (cdr l)))))
                                (:instance r*comm (y (car l)))
				(:instance r*assoc (y (car l)) (z (rlist-prod (remove1 x (cdr l)))))))))

(defthmd rlist-prod-permutationp
  (implies (and (rlistp l) (rlistp m) (permutationp l m))
	        (equal (rlist-prod l) (rlist-prod m)))
  :hints (("Subgoal *1/4" :use ((:instance rlist-prod-remove1 (x (car l)) (l m))))))

(defthmd rlist-prod-permp
  (implies (and (dlistp l) (dlistp m) (rlistp l) (rlistp m) (permp l m))
	        (equal (rlist-prod l) (rlist-prod m)))
  :hints (("Goal" :use (rlist-prod-permutationp permp-permutationp))))
