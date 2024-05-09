(in-package "DM")

(include-book "projects/groups/groups" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "rtl/rel11/lib/basic" :dir :system)
(in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
                          |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)| mod-cancel-*-const
			  cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
			  |(equal x (if a b c))| |(equal (if a b c) x)| |(logior 1 x)|
			  mod-theorem-one-b |(mod (- x) y)|))

;; A list of 4 integers:

(defund int4p (l)
  (and (true-listp l)
       (equal (len l) 4)
       (integerp (nth 0 l))
       (integerp (nth 1 l))
       (integerp (nth 2 l))
       (integerp (nth 3 l))))

;; The sum of their squares:

(defund sum-squares (l)
  (+ (* (nth 0 l) (nth 0 l))
     (* (nth 1 l) (nth 1 l))
     (* (nth 2 l) (nth 2 l))
     (* (nth 3 l) (nth 3 l))))

(local-defthmd square>=0
  (implies (integerp x) (>= (* x x) 0))
  :hints (("Goal" :in-theory (disable ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTs)
                  :cases ((>= x 0)))))

(local-defthm natp-sum-squares
  (implies (int4p l)
           (natp (sum-squares l)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable sum-squares int4p)
                  :use ((:instance square>=0 (x (nth 0 l)))
		        (:instance square>=0 (x (nth 1 l)))
			(:instance square>=0 (x (nth 2 l)))
			(:instance square>=0 (x (nth 3 l)))))))

;; According to Euler's 4-square identity, if each of 2 integers is a sum of 4 squares,
;; then so is their product:

(defund p0 (l m)
  (+ (* (nth 0 l) (nth 0 m)) (* (nth 1 l) (nth 1 m))
     (* (nth 2 l) (nth 2 m)) (* (nth 3 l) (nth 3 m))))

(defund p1 (l m)
  (+ (* (nth 0 l) (nth 1 m)) (- (* (nth 1 l) (nth 0 m)))
     (* (nth 2 l) (nth 3 m)) (- (* (nth 3 l) (nth 2 m)))))

(defund p2 (l m)
  (+ (* (nth 0 l) (nth 2 m)) (- (* (nth 1 l) (nth 3 m)))
     (- (* (nth 2 l) (nth 0 m))) (* (nth 3 l) (nth 1 m))))

(defund p3 (l m)
  (+ (* (nth 0 l) (nth 3 m)) (* (nth 1 l) (nth 2 m))
     (- (* (nth 2 l) (nth 1 m))) (- (* (nth 3 l) (nth 0 m)))))

(defund prod4 (l m)
  (list (p0 l m) (p1 l m) (p2 l m) (p3 l m)))

(defthmd prod4-lemma
  (implies (and (int4p l) (int4p m))
	   (and (int4p (prod4 l m))
		(equal (sum-squares (prod4 l m))
		       (* (sum-squares l) (sum-squares m)))))
  :hints (("Goal" :in-theory (enable int4p sum-squares p0 p1 p2 p3 prod4))))

;; The list of integers (mod (* k k) p), k = 0, ..., n-1:

(defund square-mod (n p)
  (mod (* n n) p))

(defun squares-mod (n p)
  (if (posp n)
      (append (squares-mod (1- n) p)
              (list (square-mod (1- n) p)))
    ()))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(defthm len-squares-mod
  (implies (natp n)
           (equal (len (squares-mod n p)) n)))

;; The value of a member of (squares-mod n p):

(local-defthmd nth-append
  (implies (and (natp k) (<= k (len l)))
           (equal (nth k (append l (list x)))
	          (if (< k (len l))
		      (nth k l)
		    x))))

(local-defun natp-induct (n)
  (if (posp n)
      (natp-induct (1- n))
    n))

(local-defthm kth-squares-mod
  (implies (and (primep p) (natp n) (natp k) (< k n))
           (equal (nth k (squares-mod n p))
	          (square-mod k p)))
  :hints (("Goal" :induct (natp-induct n))
          ("Subgoal *1/1" :use ((:instance nth-append (l (squares-mod (1- n) p)) (x (square-mod (1- n) p)))))))
		  
(defthmd member-squares-mod
  (implies (and (natp n) (member-equal x (squares-mod n p)))
           (let ((k (index x (squares-mod n p))))
	     (equal (square-mod k p) x))))

;; The list of integers (mod (- (1+ (* k k))) p), k = 0, ..., n-1:

(defund neg-square-mod (n p)
  (mod (- (1+ (* n n))) p))

(defun neg-squares-mod (n p)
  (if (posp n)
      (append (neg-squares-mod (1- n) p)
              (list (neg-square-mod (1- n) p)))
    ()))

(defthm len-neg-squares-mod
  (implies (natp n)
           (equal (len (neg-squares-mod n p)) n)))

;; The value of a member of (neg-squares-mod n p):

(local-defthm kth-neg-squares-mod
  (implies (and (primep p) (natp n) (natp k) (< k n))
           (equal (nth k (neg-squares-mod n p))
	          (neg-square-mod k p)))
  :hints (("Goal" :induct (natp-induct n))
          ("Subgoal *1/1" :use ((:instance nth-append (l (neg-squares-mod (1- n) p)) (x (neg-square-mod (1- n) p)))))))
		  
(defthmd member-neg-squares-mod
  (implies (and (natp n) (member-equal x (neg-squares-mod n p)))
           (let ((k (index x (neg-squares-mod n p))))
	     (equal (neg-square-mod k p) x))))

;; Both lists are sublists of the list of the first p naturals:

(local-defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
           (member-equal x m))))

(local-defthmd member-square-mod-ninit
  (implies (and (posp p) (natp n))
           (member-equal (square-mod n p)
	                 (ninit p)))
  :hints (("Goal" :in-theory (enable square-mod)
                  :use ((:instance member-ninit (x (square-mod n p)) (n p))))))

(defthmd sublistp-squares-mod-ninit
  (implies (and (posp p) (natp n))
           (sublistp (squares-mod n p) (ninit p)))
  :hints (("Subgoal *1/3" :use ((:instance member-square-mod-ninit (n (1- n)))))))

(in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)|))

(local-defthmd neg-square-mod-bound
  (implies (and (posp p) (natp n))
           (and (natp (neg-square-mod n p))
	        (< (neg-square-mod n p) p)))
  :hints (("Goal" :in-theory (enable neg-square-mod))))

(local-defthmd member-neg-square-mod-ninit
  (implies (and (posp p) (natp n))
           (member-equal (neg-square-mod n p)
	                 (ninit p)))
  :hints (("Goal" :use (neg-square-mod-bound
                        (:instance member-ninit (x (neg-square-mod n p)) (n p))))))

(defthmd sublistp-neg-squares-mod-ninit
  (implies (and (posp p) (natp n))
           (sublistp (neg-squares-mod n p) (ninit p)))
  :hints (("Subgoal *1/3" :use ((:instance member-neg-square-mod-ninit (n (1- n)))))))

;; If p is an odd prime and n = (/ (1+ p) 2), then (squares-mod n p) is a dlist, for
;; otherwise, for some i and j, 0 <= i < j <= (/ (1- p) 2) and (mod (* i i) p) =
;; (mod (* j j) p), implying p divides (- (* j j) (* i i)), and by euclid p divides
;; either (+ j i) or (- j i), which is impossible since (+ i j) < p:

(local-defthmd squares-mod-distinct-1
  (implies (and (primep p) (oddp p) (natp k) (natp n) (< k n) (< n (/ p 2)))
           (not (divides p (- (* n n) (* k k)))))
  :hints (("Goal" :use ((:instance euclid (a (+ n k)) (b (- n k)))
                        (:instance divides-leq (x p) (y (+ n k)))
                        (:instance divides-leq (x p) (y (- n k)))))))

(in-theory (enable divides))

(local-defthmd squares-mod-distinct-2
  (implies (and (primep p) (oddp p) (natp k) (natp n) (< k n) (< n (/ p 2)))
           (not (equal (square-mod n p) (square-mod k p))))
  :hints (("Goal" :in-theory (enable square-mod)
                  :use (squares-mod-distinct-1
		        (:instance rtl::mod-equal-int (rtl::n p) (rtl::a (* n n)) (rtl::b (* k k)))))))

(local-defthmd squares-mod-distinct
  (implies (and (primep p) (oddp p) (natp k) (natp n) (<= k n) (< n (/ p 2)))
           (not (member-equal (square-mod n p) (squares-mod k p))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/1" :use ((:instance squares-mod-distinct-2 (k (1- k))))))) 

(local-defthmd dlistp-squares-mod-1
  (implies (and (dlistp l) (not (member-equal x l)))
           (dlistp (append l (list x)))))

(local-defthmd dlistp-squares-mod-2
  (implies (and (primep p) (oddp p) (natp k) (<= k (/ (1+ p) 2)))
           (dlistp (squares-mod k p)))
  :hints (("Subgoal *1/4" :use ((:instance dlistp-squares-mod-1 (l (squares-mod (1- k) p))
                                                                (x (square-mod (1- k) p)))
				(:instance squares-mod-distinct (k (1- k)) (n (1- k)))))))

(defthmd dlistp-squares-mod
  (implies (and (primep p) (oddp p))
           (dlistp (squares-mod (/ (1+ p) 2) p)))
  :hints (("Goal" :use ((:instance dlistp-squares-mod-2 (k (/ (1+ p) 2)))))))

;; Similarly, (neg-squares-mod n p) is a dlist:

(local-defthmd neg-squares-mod-distinct-2
  (implies (and (primep p) (oddp p) (natp k) (natp n) (< k n) (< n (/ p 2)))
           (not (equal (neg-square-mod n p) (neg-square-mod k p))))
  :hints (("Goal" :in-theory (enable neg-square-mod)
                  :use (squares-mod-distinct-1
		        (:instance rtl::mod-equal-int (rtl::n p) (rtl::a (- (1+ (* n n)))) (rtl::b (- (1+ (* k k)))))))))

(local-defthmd neg-squares-mod-distinct
  (implies (and (primep p) (oddp p) (natp k) (natp n) (<= k n) (< n (/ p 2)))
           (not (member-equal (neg-square-mod n p) (neg-squares-mod k p))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/1" :use ((:instance neg-squares-mod-distinct-2 (k (1- k))))))) 

(local-defthmd dlistp-neg-squares-mod-2
  (implies (and (primep p) (oddp p) (natp k) (<= k (/ (1+ p) 2)))
           (dlistp (neg-squares-mod k p)))
  :hints (("Subgoal *1/4" :use ((:instance dlistp-squares-mod-1 (l (neg-squares-mod (1- k) p))
                                                                (x (neg-square-mod (1- k) p)))
				(:instance neg-squares-mod-distinct (k (1- k)) (n (1- k)))))))

(defthmd dlistp-neg-squares-mod
  (implies (and (primep p) (oddp p))
           (dlistp (neg-squares-mod (/ (1+ p) 2) p)))
  :hints (("Goal" :use ((:instance dlistp-neg-squares-mod-2 (k (/ (1+ p) 2)))))))

;; Since the sum of their lengths exceeds that of (ninit p), these lists have a common
;; member x:

(local-defthmd not-disjointp-squares-mod
  (implies (and (primep p) (oddp p))
           (not (disjointp (squares-mod (/ (1+ p) 2) p)
	                   (neg-squares-mod (/ (1+ p) 2) p))))
  :hints (("Goal" :use (dlistp-squares-mod dlistp-neg-squares-mod
                        (:instance sublistp-squares-mod-ninit (n (/ (1+ p) 2)))
                        (:instance sublistp-neg-squares-mod-ninit (n (/ (1+ p) 2)))
			(:instance len-squares-mod (n (/ (1+ p) 2)))
			(:instance len-neg-squares-mod (n (/ (1+ p) 2)))
			(:instance dlistp-append (l (squares-mod (/ (1+ p) 2) p))
			                         (m (neg-squares-mod (/ (1+ p) 2) p)))
			(:instance sublistp-append (l (squares-mod (/ (1+ p) 2) p))
			                           (m (neg-squares-mod (/ (1+ p) 2) p)))
			(:instance sublistp-<=-len (l (append (squares-mod (/ (1+ p) 2) p) (neg-squares-mod (/ (1+ p) 2) p)))
			                           (m (ninit p)))))))

(defthmd common-member-squares-mod
  (implies (and (primep p) (oddp p))
           (let ((x (common-member (squares-mod (/ (1+ p) 2) p)
	                           (neg-squares-mod (/ (1+ p) 2) p))))
	     (and (member-equal x (squares-mod (/ (1+ p) 2) p))
	          (member-equal x (neg-squares-mod (/ (1+ p) 2) p)))))
  :hints (("Goal" :use (not-disjointp-squares-mod
                        (:instance common-member-shared (l (squares-mod (/ (1+ p) 2) p))
			                                (m (neg-squares-mod (/ (1+ p) 2) p)))))))

;; Let i = (index x (squares-mod (/ (1+ p) 2) p)) and
;; j = (index x (neg-squares-mod (/ (1+ p) 2) p)).
;; Since x = (mod (* i i) p) = (mod (- (1+ (* j j))) p), (mod (+ (* i i) (* j j) 1) p) = 0,
;; and (+ (* i i) (* j j) 1) = m * p for some m > 0.  Since (+ (* i i) (* j j) 1) < (* p p),
;; m < p.  Consider the list (i j 1 0):

(defund int4-init (p)
  (let* ((l (squares-mod (/ (1+ p) 2) p))
	 (m (neg-squares-mod (/ (1+ p) 2) p))
	 (x (common-member l m)))
    (list (index x l) (index x m) 1 0)))

(defthm int4p-int4-init
  (int4p (int4-init p))
  :hints (("Goal" :in-theory (enable int4p int4-init))))

;; According to the above observations, (sum-squares (int4-init p)) = m * p, where
;; 0 < m < p:

(local-defun x* (p)
  (common-member (squares-mod (/ (1+ p) 2) p)
	         (neg-squares-mod (/ (1+ p) 2) p)))

(local-defthmd sum-squares-int4-init-1
  (implies (and (primep p) (oddp p))
           (let* ((x (common-member (squares-mod (/ (1+ p) 2) p)
	                            (neg-squares-mod (/ (1+ p) 2) p)))
		  (i (index x (squares-mod (/ (1+ p) 2) p)))
		  (j (index x (neg-squares-mod (/ (1+ p) 2) p))))
	     (equal (square-mod i p)
	            (neg-square-mod j p))))
  :hints (("Goal" :use (common-member-squares-mod
                        (:instance member-squares-mod (x (x* p)) (n (/ (1+ p) 2)))
                        (:instance member-neg-squares-mod (x (x* p)) (n (/ (1+ p) 2)))))))

(local-defthmd sum-squares-int4-init-2
  (implies (and (primep p) (natp i) (natp j) (equal (square-mod i p) (neg-square-mod j p)))
           (divides p (+ (* i i) (* j j) 1)))
  :hints (("Goal" :in-theory (enable square-mod neg-square-mod)
                  :use ((:instance rtl::mod-equal-int (rtl::n p)
			                              (rtl::a (* i i)) (rtl::b (- (1+ (* j j)))))))))

(local-defthmd sum-squares-int4-init-3
  (implies (and (primep p) (oddp p))
           (let* ((x (common-member (squares-mod (/ (1+ p) 2) p)
	                            (neg-squares-mod (/ (1+ p) 2) p)))
		  (i (index x (squares-mod (/ (1+ p) 2) p)))
		  (j (index x (neg-squares-mod (/ (1+ p) 2) p))))
             (divides p (+ (* i i) (* j j) 1))))
  :hints (("Goal" :use (sum-squares-int4-init-1
                        (:instance sum-squares-int4-init-2 (i (index (x* p) (squares-mod (/ (1+ p) 2) p)))
							   (j (index (x* p) (neg-squares-mod (/ (1+ p) 2) p))))))))

(local-defthmd sum-squares-int4-init-4
  (implies (and (primep p) (oddp p) (equal (len l) (/ (1+ p) 2)) (member-equal x l))
           (let ((i (index x l)))
	     (and (natp i) (<= i (/ (1- p) 2)))))
  :hints (("Goal" :in-theory (disable ind<len) :use (ind<len))))

(local-defthmd sum-squares-int4-init-5
  (implies (and (primep p) (oddp p) (natp i) (<= i (/ (1- p) 2)) (natp j) (<= j (/ (1- p) 2)))
           (< (+ (* i i) (* j j) 1) (* p p)))	   
  :hints (("Goal" :nonlinearp t)))

(local-defthmd sum-squares-int4-init-6
  (implies (and (primep p) (oddp p))
           (let* ((x (common-member (squares-mod (/ (1+ p) 2) p)
	                            (neg-squares-mod (/ (1+ p) 2) p)))
		  (i (index x (squares-mod (/ (1+ p) 2) p)))
		  (j (index x (neg-squares-mod (/ (1+ p) 2) p))))
             (< (+ (* i i) (* j j) 1) (* p p))))
  :hints (("Goal" :use (common-member-squares-mod
			(:instance len-squares-mod (n (/ (1+ p) 2)))
			(:instance len-neg-squares-mod (n (/ (1+ p) 2)))
                        (:instance sum-squares-int4-init-4 (x (x* p)) (l (squares-mod (/ (1+ p) 2) p)))
                        (:instance sum-squares-int4-init-4 (x (x* p)) (l (neg-squares-mod (/ (1+ p) 2) p)))
                        (:instance sum-squares-int4-init-5 (i (index (x* p) (squares-mod (/ (1+ p) 2) p)))
			                                   (j (index (x* p) (neg-squares-mod (/ (1+ p) 2) p))))))))

(defthmd sum-squares-int4-init
  (implies (and (primep p) (oddp p))
           (let ((m (/ (sum-squares (int4-init p)) p)))
	     (and (posp m)
	          (< m p))))
  :hints (("Goal" :in-theory (enable sum-squares int4-init)
                  :nonlinearp t
                  :use (sum-squares-int4-init-3 sum-squares-int4-init-6))))

;; Given an int4 l = (x0 x1 x2 x3) with sum of squares m * p, where 1 < m < p, we shall 
;; construct an int4 with sum of squares r * p, where 0 < r < m.
;; As a first step, we construct an int4 l' = (y0 y1 y2 y3) with sum of squares r * m, 
;; where 0 < r < m.  We select yi to be the unique integer satisfying (mod yi m) =
;; (mod xi m) and |yi| <= m/2:

(defund shift-mod (x m)
  (let ((y (mod x m)))
    (if (> y (/ m 2))
        (- y m)
      y)))

(defthmd shift-mod-bound
  (implies (and (posp m) (integerp x))
           (let ((y (shift-mod x m)))
	     (and (integerp y)
	          (equal (mod y m) (mod x m))
	          (<= (abs y) (/ m 2)))))
  :hints (("Goal" :in-theory (enable shift-mod))))

;; l' is defined as follows:

(defund shift-mod-list (l m)
  (list (shift-mod (nth 0 l) m)
        (shift-mod (nth 1 l) m)
	(shift-mod (nth 2 l) m)
	(shift-mod (nth 3 l) m)))

(defthmd int4p-shift-mod-list
  (implies (and (posp m) (int4p l))
           (int4p (shift-mod-list l m)))
  :hints (("Goal" :in-theory (enable int4p shift-mod-list shift-mod))))
  
;; Then (mod (sum-squares l') m) = (mod (sum-squares l) m) = 0 and 0 <= (sum-squares l') 
;; <= m * m.  Suppose (sum-squares l') = 0.  Then each yi = 0, which implies m divides
;; each xi.  But then m * m divides (sum-squares l) = m * p and m divides p, a contradiction.
;; On the other hand, suppose (sum-squares l') = m * m.  Then for each i, yi = m/2, which 
;; implies (mod xi m) = m/2 and (mod (* xi xi) (* m m)) = (mod (/ (* m m) 4) (* m m)) and
;; again (* m m) divides (sum-squares l), a contradiction.  Thus, (sum-squares l') = r * m, 
;; where 0 < r < m:

(defthmd shift-mod-m/2
  (implies (and (posp m) (integerp x) (equal (shift-mod x m) (/ m 2)))
           (equal (mod x m) (/ m 2)))
  :hints (("Goal" :in-theory (enable shift-mod))))

(defthmd shift-mod-0
  (implies (and (posp m) (integerp x) (equal (shift-mod x m) 0))
           (equal (mod x m) 0))
  :hints (("Goal" :in-theory (enable shift-mod))))

(local-defthmd shift-mod-sqr-bound-1
  (implies (and (integerp x) (posp m) (equal (mod x m) (/ m 2)))
           (equal (mod (* x x) (* m m))
	          (/ (* m m) 4)))
  :hints (("Goal" :use ((:instance rtl::mod-def (rtl::y m))
                        (:instance rtl::mod-mult (rtl::n (* m m)) (rtl::m (/ (* m m) 4))
			                         (rtl::a (* (fl (/ x m)) (1+ (fl (/ x m))))))))))

(defthmd shift-mod-sqr-bound
  (implies (and (posp m) (integerp x))
           (let ((y (shift-mod x m)))
	     (and (integerp y)
	          (or (< (* y y) (/ (* m m) 4))
		      (and (equal (* y y) (/ (* m m) 4))
		           (equal (mod (* x x) (* m m)) (/ (* m m) 4)))))))
  :hints (("Goal" :use (shift-mod-bound shift-mod-sqr-bound-1 shift-mod-m/2) :nonlinearp t)))

(defthmd shift-mod-sqr-0
  (implies (and (posp m) (integerp x))
           (let ((y (shift-mod x m)))
	     (and (integerp y)
	          (or (> (* y y) 0)
		      (and (equal (* y y) 0)
		           (divides (* m m) (* x x)))))))
  :hints (("Goal" :use (shift-mod-bound shift-mod-0) :nonlinearp t)))

(local-defthmd mod-int4-1
  (implies (and (integerp x0) (integerp x1) (integerp x2) (integerp x3))
           (equal (mod (+ (mod x0 m) (mod x1 m) (mod x2 m) (mod x3 m)) m) 
	          (mod (+ x0 x1 x2 x3) m)))
  :hints (("Goal" :in-theory (disable acl2::|(mod (+ x y) z) where (<= z 0)| acl2::mod-bounds-1 acl2::mod-bounds-2
                                      acl2::mod-negative acl2::mod-positive acl2::mod-bounds-3 rtl::mod-bnd-1
				      acl2::mod-x-y-=-x acl2::default-mod-ratio)
                  :use ((:instance rtl::mod-sum (rtl::n m) (rtl::a (+ (mod x0 m) (mod x1 m) (mod x2 m))) (rtl::b x3))
                        (:instance rtl::mod-sum (rtl::n m) (rtl::a (+ (mod x0 m) (mod x1 m) x3)) (rtl::b x2))
                        (:instance rtl::mod-sum (rtl::n m) (rtl::a (+ (mod x0 m) x3 x2)) (rtl::b x1))
                        (:instance rtl::mod-sum (rtl::n m) (rtl::a (+ x3 x2 x1)) (rtl::b x0))))))

(local-defthmd mod-int4
  (implies (and (integerp x0) (integerp x1) (integerp x2) (integerp x3)
                (integerp y0) (integerp y1) (integerp y2) (integerp y3)
		(= (mod x0 m) (mod y0 m)) (= (mod x1 m) (mod y1 m))
		(= (mod x2 m) (mod y2 m)) (= (mod x3 m) (mod y3 m)))
           (equal (mod (+ x0 x1 x2 x3) m)
	          (mod (+ y0 y1 y2 y3) m)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :Use (mod-int4-1 (:instance mod-int4-1 (x0 y0) (x1 y1) (x2 y2) (x3 y3))))))

(local-defthmd mod-mod-square
  (implies (and (integerp a)
                (integerp b)
		(posp m)
		(equal (mod a m) (mod b m)))
	   (equal (mod (* a a) m)
	          (mod (* b b) m)))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (rtl::n m) (rtl::a a) (rtl::b a))
                        (:instance rtl::mod-mod-times (rtl::n m) (rtl::a a) (rtl::b (mod a m)))
			(:instance rtl::mod-mod-times (rtl::n m) (rtl::a b) (rtl::b b))
                        (:instance rtl::mod-mod-times (rtl::n m) (rtl::a b) (rtl::b (mod b m)))))))

(local-defthm nth-shift-mod-list
  (and (equal (nth 0 (shift-mod-list l m)) (shift-mod (nth 0 l) m))
       (equal (nth 1 (shift-mod-list l m)) (shift-mod (nth 1 l) m))
       (equal (nth 2 (shift-mod-list l m)) (shift-mod (nth 2 l) m))
       (equal (nth 3 (shift-mod-list l m)) (shift-mod (nth 3 l) m)))
  :hints (("Goal" :in-theory (enable shift-mod-list))))
       
(local-defthmd sum-squares-shift-mod-list-1
  (implies (and (primep p) (oddp p) (posp m) (< m p) (int4p l))
           (equal (mod (sum-squares (shift-mod-list l m)) m)
	          (mod (sum-squares l) m)))
  :hints (("Goal" :in-theory '(int4p sum-squares nth-shift-mod-list)
                  :use ((:instance shift-mod-bound (x (nth 0 l)))
		        (:instance shift-mod-bound (x (nth 1 l)))
		        (:instance shift-mod-bound (x (nth 2 l)))
		        (:instance shift-mod-bound (x (nth 3 l)))
			(:instance mod-mod-square (a (nth 0 l)) (b (shift-mod (nth 0 l) m)))
			(:instance mod-mod-square (a (nth 1 l)) (b (shift-mod (nth 1 l) m)))
			(:instance mod-mod-square (a (nth 2 l)) (b (shift-mod (nth 2 l) m)))
			(:instance mod-mod-square (a (nth 3 l)) (b (shift-mod (nth 3 l) m)))
                        (:instance mod-int4 (x0 (* (nth 0 l) (nth 0 l))) (x1 (* (nth 1 l) (nth 1 l)))
			                    (x2 (* (nth 2 l) (nth 2 l))) (x3 (* (nth 3 l) (nth 3 l))) 
			                    (y0 (* (shift-mod (nth 0 l) m) (shift-mod (nth 0 l) m)))
			                    (y1 (* (shift-mod (nth 1 l) m) (shift-mod (nth 1 l) m)))
			                    (y2 (* (shift-mod (nth 2 l) m) (shift-mod (nth 2 l) m)))
			                    (Y3 (* (shift-mod (nth 3 l) m) (shift-mod (nth 3 l) m))))))))

(local-defthmd sum-squares-shift-mod-list-2
  (implies (and (primep p) (oddp p) (posp m) (< m p) (int4p l))
           (or (> (sum-squares (shift-mod-list l m)) 0)
	       (and (= (sum-squares (shift-mod-list l m)) 0)
	            (= (mod (sum-squares l) (* m m)) 0))))
  :hints (("Goal" :in-theory (enable int4p sum-squares)
                  :use ((:instance shift-mod-sqr-0 (x (nth 0 l)))
                        (:instance shift-mod-sqr-0 (x (nth 1 l)))
			(:instance shift-mod-sqr-0 (x (nth 2 l)))
			(:instance shift-mod-sqr-0 (x (nth 3 l)))))))
			
(local-defthmd sum-squares-shift-mod-list-3
  (implies (and (primep p) (oddp p) (posp m) (< m p) (int4p l))
           (or (< (sum-squares (shift-mod-list l m)) (* m m))
	       (and (= (sum-squares (shift-mod-list l m)) (* m m))
	            (= (mod (sum-squares l) (* m m)) 0))))
  :hints (("Goal" :in-theory (enable int4p sum-squares)
                  :use ((:instance shift-mod-sqr-bound (x (nth 0 l)))
                        (:instance shift-mod-sqr-bound (x (nth 1 l)))
			(:instance shift-mod-sqr-bound (x (nth 2 l)))
			(:instance shift-mod-sqr-bound (x (nth 3 l)))
			(:instance mod-int4-1 (m (* m m)) (x0 (* (nth 0 l) (nth 0 l))) (x1 (* (nth 1 l) (nth 1 l)))
			                                  (x2 (* (nth 2 l) (nth 2 l))) (x3 (* (nth 3 l) (nth 3 l))))))))

(local-defthmd sum-squares-shift-mod-list-4
  (implies (and (primep p) (oddp p) (posp m) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((sum (sum-squares (shift-mod-list l m))))
             (divides m sum)))
  :hints (("Goal" :use (sum-squares-shift-mod-list-1
                        (:instance rtl::mod-equal-int (rtl::n m) (rtl::a (sum-squares l))
			                              (rtl::b (sum-squares (shift-mod-list l m))))))))

(local-defthmd sum-squares-shift-mod-list-5
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((sum (sum-squares (shift-mod-list l m))))
             (> sum 0)))
  :hints (("Goal" :use (sum-squares-shift-mod-list-2
                        (:instance primep-no-divisor (d m))
                        (:instance rtl::mod-equal-int (rtl::n (* m m)) (rtl::a (sum-squares l)) (rtl::b 0))))))

(local-defthmd sum-squares-shift-mod-list-6
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((sum (sum-squares (shift-mod-list l m))))
             (< sum (* m m))))
  :hints (("Goal" :use (sum-squares-shift-mod-list-3
                        (:instance primep-no-divisor (d m))
                        (:instance rtl::mod-equal-int (rtl::n (* m m)) (rtl::a (sum-squares l)) (rtl::b 0))))))

(defthmd sum-squares-shift-mod-list
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((r (/ (sum-squares (shift-mod-list l m)) m)))
	     (and (posp r)
	          (< r m))))
  :hints (("Goal" :nonlinearp t
                  :use (sum-squares-shift-mod-list-4 sum-squares-shift-mod-list-5 sum-squares-shift-mod-list-6))))

;; Now consider the list l'' = (prod4 l l') = (p0 p1 p3 p3).  By prod4-lemma,
;; (sum-squares l'') = (sum-squares l) * (sum-squares l') = m * p * r * m.  We shall 
;; show that each pi is divisible by m:

(local-defthmd mod-x-y
  (implies (and (posp m) (integerp x) (integerp y) (integerp z) (= (mod y m) (mod z m)))
           (equal (mod (* x y) m) (mod (* x z) m)))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (rtl::n m) (rtl::a y) (rtl::b x))
                        (:instance rtl::mod-mod-times (rtl::n m) (rtl::a z) (rtl::b x))))))

(local-defthmd mod-minus-x-y
  (implies (and (posp m) (integerp x) (integerp y) (integerp z) (= (mod y m) (mod z m)))
           (equal (mod (- (* x y)) m) (mod (- (* x z)) m)))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (rtl::n m) (rtl::a y) (rtl::b (- x)))
                        (:instance rtl::mod-mod-times (rtl::n m) (rtl::a z) (rtl::b (- x)))))))

;; (mod p0 m) = (mod (+ (* x0 y0) (* x1 y1) (* x2 y2) (* x3 y3)) m)
;;            = (mod (+ (* x0 x0) (* x1 x1) (* x2 x2  (* x3 x3)) m)
;;            = (mod (sum-squares l) m)
;;	      = 0.

(local-defthm nth-0-prod4-1 (equal (nth 0 (prod4 l m)) (p0 l m))
  :hints (("Goal" :in-theory (enable prod4))))  

(local-defthmd nth-0-prod4
  (implies (and (int4p l1) (int4p l2) (posp m)
                (equal (mod (nth 0 l1) m) (mod (nth 0 l2) m))
                (equal (mod (nth 1 l1) m) (mod (nth 1 l2) m))
                (equal (mod (nth 2 l1) m) (mod (nth 2 l2) m))
                (equal (mod (nth 3 l1) m) (mod (nth 3 l2) m)))
	   (equal (mod (nth 0 (prod4 l1 l2)) m)
	          (mod (sum-squares l1) m)))
  :hints (("Goal" :in-theory '(int4p sum-squares nth-0-prod4-1 p0)
                  :use ((:instance mod-x-y (x (nth 0 l1)) (y (nth 0 l2)) (z (nth 0 l1)))
		        (:instance mod-x-y (x (nth 1 l1)) (y (nth 1 l2)) (z (nth 1 l1)))
			(:instance mod-x-y (x (nth 2 l1)) (y (nth 2 l2)) (z (nth 2 l1)))
			(:instance mod-x-y (x (nth 3 l1)) (y (nth 3 l2)) (z (nth 3 l1)))
			(:instance mod-int4 (x0 (* (nth 0 l1) (nth 0 l1))) (y0 (* (nth 0 l1) (nth 0 l2)))
			                    (x1 (* (nth 1 l1) (nth 1 l1))) (y1 (* (nth 1 l1) (nth 1 l2)))
					    (x2 (* (nth 2 l1) (nth 2 l1))) (y2 (* (nth 2 l1) (nth 2 l2)))
					    (x3 (* (nth 3 l1) (nth 3 l1))) (y3 (* (nth 3 l1) (nth 3 l2))))))))
                  

(defthmd m-divides-nth-0-prod
  (implies (and (posp m) (int4p l) (divides m (sum-squares l)))
           (divides m (nth 0 (prod4 l (shift-mod-list l m)))))
  :hints (("Goal" :in-theory (enable int4p)
                  :use (int4p-shift-mod-list
                        (:instance nth-0-prod4 (l1 l) (l2 (shift-mod-list l m)))
                        (:instance rtl::mod-equal-int (rtl::n m) (rtl::a (nth 0 (prod4 l (shift-mod-list l m))))
			                              (rtl::b (sum-squares l)))
			(:instance shift-mod-bound (x (nth 0 l)))
			(:instance shift-mod-bound (x (nth 1 l)))
			(:instance shift-mod-bound (x (nth 2 l)))
			(:instance shift-mod-bound (x (nth 3 l)))))))

;; (mod p1 m) = (mod (+ (* x0 y1) (- (* x1 y0)) (* x2 y3) (- (* x3 y2)) m)
;;            = (mod (+ (* x0 x1) (- (* x1 x0)) (* x2 x3) (- (* x3 x2)) m)
;;	      = (mod 0 m)
;;	      = 0.

(local-defthm nth-1-prod4-1 (equal (nth 1 (prod4 l m)) (p1 l m))
  :hints (("Goal" :in-theory (enable prod4))))  

(local-defthmd nth-1-prod4
  (implies (and (int4p l1) (int4p l2) (posp m)
                (equal (mod (nth 0 l1) m) (mod (nth 0 l2) m))
                (equal (mod (nth 1 l1) m) (mod (nth 1 l2) m))
                (equal (mod (nth 2 l1) m) (mod (nth 2 l2) m))
                (equal (mod (nth 3 l1) m) (mod (nth 3 l2) m)))
	   (equal (mod (nth 1 (prod4 l1 l2)) m)
	          0))
  :hints (("Goal" :in-theory '(int4p nth-1-prod4-1 p1)
                  :use ((:instance mod-x-y (x (nth 0 l1)) (y (nth 1 l2)) (z (nth 1 l1)))
		        (:instance mod-minus-x-y (x (nth 1 l1)) (y (nth 0 l2)) (z (nth 0 l1)))
			(:instance mod-x-y (x (nth 2 l1)) (y (nth 3 l2)) (z (nth 3 l1)))
			(:instance mod-minus-x-y (x (nth 3 l1)) (y (nth 2 l2)) (z (nth 2 l1)))
			(:instance mod-int4 (x0 (* (nth 0 l1) (nth 1 l1))) (x1 (- (* (nth 1 l1) (nth 0 l1))))
			                    (x2 (* (nth 2 l1) (nth 3 l1))) (x3 (- (* (nth 3 l1) (nth 2 l1))))
					    (y0 (* (nth 0 l1) (nth 1 l2))) (y1 (- (* (nth 1 l1) (nth 0 l2))))
			                    (y2 (* (nth 2 l1) (nth 3 l2))) (y3 (- (* (nth 3 l1) (nth 2 l2)))))))
	  ("Goal'''" :in-theory (enable))))                  

(defthmd m-divides-nth-1-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 1 (prod4 l (shift-mod-list l m)))))
  :hints (("Goal" :in-theory (enable int4p)
                  :use (int4p-shift-mod-list
                        (:instance nth-1-prod4 (l1 l) (l2 (shift-mod-list l m)))
                        (:instance rtl::mod-equal-int (rtl::n m) (rtl::a (nth 1 (prod4 l (shift-mod-list l m))))
			                              (rtl::b 0))
			(:instance shift-mod-bound (x (nth 0 l)))
			(:instance shift-mod-bound (x (nth 1 l)))
			(:instance shift-mod-bound (x (nth 2 l)))
			(:instance shift-mod-bound (x (nth 3 l)))))))


;; (mod p2 m) = (mod (+ (* x0 y2) (- (* x1 y3)) (- (* x2 y0)) (* x3 y1)) m)
;;            = (mod (+ (* x0 x2) (- (* x1 x3)) (- (* x2 x0)) (* x3 x1)) m)
;;	      = (mod 0 m)
;;	      = 0.

(local-defthm nth-2-prod4-1 (equal (nth 2 (prod4 l m)) (p2 l m))
  :hints (("Goal" :in-theory (enable prod4))))  

(local-defthmd nth-2-prod4
  (implies (and (int4p l1) (int4p l2) (posp m)
                (equal (mod (nth 0 l1) m) (mod (nth 0 l2) m))
                (equal (mod (nth 1 l1) m) (mod (nth 1 l2) m))
                (equal (mod (nth 2 l1) m) (mod (nth 2 l2) m))
                (equal (mod (nth 3 l1) m) (mod (nth 3 l2) m)))
	   (equal (mod (nth 2 (prod4 l1 l2)) m)
	          0))
  :hints (("Goal" :in-theory '(int4p nth-2-prod4-1 p2)
                  :use ((:instance mod-x-y (x (nth 0 l1)) (y (nth 2 l2)) (z (nth 2 l1)))
		        (:instance mod-minus-x-y (x (nth 1 l1)) (y (nth 3 l2)) (z (nth 3 l1)))
			(:instance mod-minus-x-y (x (nth 2 l1)) (y (nth 0 l2)) (z (nth 0 l1)))
			(:instance mod-x-y (x (nth 3 l1)) (y (nth 1 l2)) (z (nth 1 l1)))
			(:instance mod-int4 (x0 (* (nth 0 l1) (nth 2 l1))) (x1 (- (* (nth 1 l1) (nth 3 l1))))
			                    (x2 (- (* (nth 2 l1) (nth 0 l1)))) (x3 (* (nth 3 l1) (nth 1 l1)))
					    (y0 (* (nth 0 l1) (nth 2 l2))) (y1 (- (* (nth 1 l1) (nth 3 l2))))
			                    (y2 (- (* (nth 2 l1) (nth 0 l2)))) (y3 (* (nth 3 l1) (nth 1 l2))))))
	  ("Goal'''" :in-theory (enable))))

(defthmd m-divides-nth-2-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 2 (prod4 l (shift-mod-list l m)))))
  :hints (("Goal" :in-theory (enable int4p)
                  :use (int4p-shift-mod-list
                        (:instance nth-2-prod4 (l1 l) (l2 (shift-mod-list l m)))
                        (:instance rtl::mod-equal-int (rtl::n m) (rtl::a (nth 2 (prod4 l (shift-mod-list l m))))
			                              (rtl::b 0))
			(:instance shift-mod-bound (x (nth 0 l)))
			(:instance shift-mod-bound (x (nth 1 l)))
			(:instance shift-mod-bound (x (nth 2 l)))
			(:instance shift-mod-bound (x (nth 3 l)))))))

;; (mod p3 m) = (mod (+ (* x0 y3) (* x1 y2) (- (* x2 y1)) (- (* x3 y0)) m)
;;            = (mod (+ (* x0 x3) (* x1 x2) (- (* x2 x1)) (- (* x3 x0)) m)
;;	      = (mod 0 m)
;;	      = 0.

(local-defthm nth-3-prod4-1 (equal (nth 3 (prod4 l m)) (p3 l m))
  :hints (("Goal" :in-theory (enable prod4))))  

(local-defthmd nth-3-prod4
  (implies (and (int4p l1) (int4p l2) (posp m)
                (equal (mod (nth 0 l1) m) (mod (nth 0 l2) m))
                (equal (mod (nth 1 l1) m) (mod (nth 1 l2) m))
                (equal (mod (nth 2 l1) m) (mod (nth 2 l2) m))
                (equal (mod (nth 3 l1) m) (mod (nth 3 l2) m)))
	   (equal (mod (nth 3 (prod4 l1 l2)) m)
	          0))
  :hints (("Goal" :in-theory '(int4p nth-3-prod4-1 p3)
                  :use ((:instance mod-x-y (x (nth 0 l1)) (y (nth 3 l2)) (z (nth 3 l1)))
		        (:instance mod-x-y (x (nth 1 l1)) (y (nth 2 l2)) (z (nth 2 l1)))
			(:instance mod-minus-x-y (x (nth 2 l1)) (y (nth 1 l2)) (z (nth 1 l1)))
			(:instance mod-minus-x-y (x (nth 3 l1)) (y (nth 0 l2)) (z (nth 0 l1)))
			(:instance mod-int4 (x0 (* (nth 0 l1) (nth 3 l1))) (x1 (* (nth 1 l1) (nth 2 l1)))
			                    (x2 (- (* (nth 2 l1) (nth 1 l1)))) (x3 (- (* (nth 3 l1) (nth 0 l1))))
					    (y0 (* (nth 0 l1) (nth 3 l2))) (y1 (* (nth 1 l1) (nth 2 l2)))
			                    (y2 (- (* (nth 2 l1) (nth 1 l2)))) (y3 (- (* (nth 3 l1) (nth 0 l2)))))))
	  ("Goal'''" :in-theory (enable))))

(defthmd m-divides-nth-3-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 3 (prod4 l (shift-mod-list l m)))))
  :hints (("Goal" :in-theory (enable int4p)
                  :use (int4p-shift-mod-list
                        (:instance nth-3-prod4 (l1 l) (l2 (shift-mod-list l m)))
                        (:instance rtl::mod-equal-int (rtl::n m) (rtl::a (nth 3 (prod4 l (shift-mod-list l m))))
			                              (rtl::b 0))
			(:instance shift-mod-bound (x (nth 0 l)))
			(:instance shift-mod-bound (x (nth 1 l)))
			(:instance shift-mod-bound (x (nth 2 l)))
			(:instance shift-mod-bound (x (nth 3 l)))))))

;; We define (reduce-int4 l p) to be the result of dividing each pi by m:

(defund div-int4 (l m)
  (list (/ (nth 0 l) m) (/ (nth 1 l) m) (/ (nth 2 l) m) (/ (nth 3 l) m)))

(defund reduce-int4 (l p)
  (let ((m (/ (sum-squares l) p)))
    (div-int4 (prod4 l (shift-mod-list l m))
              m)))

;; Thus, (sum-squares (reduce-int4 l p)) = (sum-squares (prod4 l l')) / (m * m)
;;                                       = r * p
;;                                       < m * p:

(defthmd int4p-reduce
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (int4p (reduce-int4 l p)))
  :hints (("Goal" :in-theory (enable int4p div-int4 reduce-int4)
                  :use (m-divides-nth-0-prod m-divides-nth-1-prod m-divides-nth-2-prod m-divides-nth-3-prod))))

(local-defthmd sum-squares-reduce-int4-1
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
	   (equal (sum-squares (reduce-int4 l p))
	          (/ (sum-squares (prod4 l (shift-mod-list l m)))
		     (* m m))))
  :hints (("Goal" :in-theory (enable sum-squares int4p div-int4 reduce-int4)
                  :use (int4p-shift-mod-list
		        (:instance prod4-lemma (m (shift-mod-list l m)))))))

(local-defthmd sum-squares-reduce-int4-2
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((r (/ (sum-squares (shift-mod-list l m)) m)))
  	     (equal (sum-squares (reduce-int4 l p))
	            (* r p))))
  :hints (("Goal" :in-theory (enable sum-squares-reduce-int4-1)
                  :use (int4p-shift-mod-list sum-squares-shift-mod-list
		        (:instance prod4-lemma (m (shift-mod-list l m)))))))

(defthmd sum-squares-reduce-int4
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
	   (let ((r (/ (sum-squares (reduce-int4 l p)) p)))
 	     (and (posp r)
	          (< r m))))
  :hints (("Goal" :in-theory (enable sum-squares-reduce-int4-2)
                  :use (sum-squares-shift-mod-list))))
	      
;; Applying reduce-int4 recursively, we have an int4 with sum of sqares p:

(local-defthmd int4-prime-aux-hint
  (and (implies (and (primep p) (oddp p) (int4p l)
                     (divides p (sum-squares l))
	             (> (sum-squares l) p)
	             (< (sum-squares l) (* p p)))
                (o< (nfix (sum-squares (reduce-int4 l p)))
	            (nfix (sum-squares l))))
       (o-p (nfix (sum-squares l))))
  :hints (("Goal" :nonlinearp t :use ((:instance sum-squares-reduce-int4 (m (/ (sum-squares l) p)))))))

(defun int4-prime-aux (l p)
  (declare (xargs :measure (nfix (sum-squares l))
                  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (int4-prime-aux-hint)))))                  
  (if (and (primep p) (oddp p) (int4p l)
           (divides p (sum-squares l))
	   (> (sum-squares l) p)
	   (< (sum-squares l) (* p p)))
      (int4-prime-aux (reduce-int4 l p) p)
    l))

(defthmd sum-squares-int4-prime-aux
  (implies (and (primep p) (oddp p) (int4p l)
                (>= (sum-squares l) p)
		(< (sum-squares l) (* p p))
		(divides p (sum-squares l)))
           (and (int4p (int4-prime-aux l p))
	        (equal (sum-squares (int4-prime-aux l p)) p)))
  :hints (("Subgoal *1/1" :nonlinearp t
                          :use ((:instance int4p-reduce (m (/ (sum-squares l) p)))
                                (:instance sum-squares-reduce-int4 (m (/ (sum-squares l) p)))))))

(defund int4-prime (p)
  (if (equal p 2)
      '(1 1 0 0)
    (int4-prime-aux (int4-init p) p)))

(local-defthmd sum-squares-int4-odd-prime
  (implies (and (primep p) (oddp p))
           (and (int4p (int4-prime p))
                (equal (sum-squares (int4-prime p))
	               p)))
  :hints (("Goal" :in-theory (enable int4-prime)
                  :nonlinearp t
		  :use ((:instance sum-squares-int4-prime-aux (l (int4-init p)))
		        (:instance sum-squares-int4-init)))))

(defthmd sum-squares-int4-prime
  (implies (primep p)
           (and (int4p (int4-prime p))
                (equal (sum-squares (int4-prime p))
	               p)))
  :hints (("Goal" :in-theory (enable int4-prime)
                  :use (sum-squares-int4-odd-prime
		        (:instance primep-no-divisor (d 2))))))

;; By induction, every prime power is a sum of 4 squares:

(defun int4-prime-power-aux (k l acc)
  (if (posp k)
      (int4-prime-power-aux (1- k) l (prod4 l acc))
    acc))

(defthmd sum-squares-int4-prime-power-aux
  (implies (and (natp k) (int4p l) (int4p acc))
           (and (int4p (int4-prime-power-aux k l acc))
	        (equal (sum-squares (int4-prime-power-aux k l acc))
		       (* (expt (sum-squares l) k)
		          (sum-squares acc)))))
  :hints (("Subgoal *1/1" :use ((:instance prod4-lemma (m acc))))))

(defund int4-prime-power (p k)
  (int4-prime-power-aux k (int4-prime p) '(1 0 0 0)))

(defthmd sum-squares-int4-prime-power
  (implies (and (primep p) (natp k))
           (and (int4p (int4-prime-power p k))
	        (equal (sum-squares (int4-prime-power p k))
	               (expt p k))))
  :hints (("Goal" :in-theory (enable int4-prime-power)
                  :use (sum-squares-int4-prime
		        (:instance sum-squares-int4-prime-power-aux (l (int4-prime p)) (acc '(1 0 0 0)))))))

;; The final theorem follows from the fundamental theorem of arithmetic:

(defun int4-nat-aux (l)
  (if (consp l)
      (prod4 (int4-prime-power (caar l) (cdar l))
             (int4-nat-aux (cdr l)))
    '(1 0 0 0)))

(defthmd sum-squares-int4-nat-aux
  (implies (prime-pow-list-p l)
           (and (int4p (int4-nat-aux l))
	        (equal (sum-squares (int4-nat-aux l))
		       (pow-prod l))))
  :hints (("Subgoal *1/1" :use ((:instance prod4-lemma (l (INT4-PRIME-POWER (CAR (CAR L)) (CDR (CAR L))))
                                                       (m (INT4-NAT-AUX (CDR L))))
				(:instance sum-squares-int4-prime-power (p (caar l)) (k (cdar l)))))))

(defund int4-nat (n)
  (if (zp n)
      '(0 0 0 0)
    (int4-nat-aux (prime-fact n))))

(defthmd nat-sum-of-4-squares
  (implies (natp n)
           (and (int4p (int4-nat n))
	        (equal (sum-squares (int4-nat n)) n)))
  :hints (("Goal" :in-theory (enable int4-nat)
                  :use (prime-fact-existence (:instance sum-squares-int4-nat-aux (l (prime-fact n)))))))

    
  
  

