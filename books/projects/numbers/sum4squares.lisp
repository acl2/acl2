(in-package "DM")

(include-book "projects/groups/groups" :dir :system)
(local (include-book "support/sum4squares"))

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
		       (* (sum-squares l) (sum-squares m))))))

;; The list of integers (mod (* k k) p), k = 0, ..., n-1:

(defund square-mod (n p)
  (mod (* n n) p))

(defun squares-mod (n p)
  (if (posp n)
      (append (squares-mod (1- n) p)
              (list (square-mod (1- n) p)))
    ()))

(defthm len-squares-mod
  (implies (natp n)
           (equal (len (squares-mod n p)) n)))

;; The value of a member of (squares-mod n p):

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

(defthmd member-neg-squares-mod
  (implies (and (natp n) (member-equal x (neg-squares-mod n p)))
           (let ((k (index x (neg-squares-mod n p))))
	     (equal (neg-square-mod k p) x))))

;; Both lists are sublists of the list of the first p naturals:

(defthmd sublistp-squares-mod-ninit
  (implies (and (posp p) (natp n))
           (sublistp (squares-mod n p) (ninit p))))

(defthmd sublistp-neg-squares-mod-ninit
  (implies (and (posp p) (natp n))
           (sublistp (neg-squares-mod n p) (ninit p))))

;; If p is an odd prime and n = (/ (1+ p) 2), then (squares-mod n p) is a dlist, for
;; otherwise, for some i and j, 0 <= i < j <= (/ (1- p) 2) and (mod (* i i) p) =
;; (mod (* j j) p), implying p divides (- (* j j) (* i i)), and by euclid p divides
;; either (+ j i) or (- j i), which is impossible since (+ i j) < p:

(defthmd dlistp-squares-mod
  (implies (and (primep p) (oddp p))
           (dlistp (squares-mod (/ (1+ p) 2) p))))

;; Similarly, (neg-squares-mod n p) is a dlist:

(defthmd dlistp-neg-squares-mod
  (implies (and (primep p) (oddp p))
           (dlistp (neg-squares-mod (/ (1+ p) 2) p))))

;; Since the sum of their lengths exceeds that of (ninit p), these lists have a common
;; member x:

(defthmd common-member-squares-mod
  (implies (and (primep p) (oddp p))
           (let ((x (common-member (squares-mod (/ (1+ p) 2) p)
	                           (neg-squares-mod (/ (1+ p) 2) p))))
	     (and (member-equal x (squares-mod (/ (1+ p) 2) p))
	          (member-equal x (neg-squares-mod (/ (1+ p) 2) p))))))

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
  (int4p (int4-init p)))

;; According to the above observations, (sum-squares (int4-init p)) = m * p, where
;; 0 < m < p:

(defthmd sum-squares-int4-init
  (implies (and (primep p) (oddp p))
           (let ((m (/ (sum-squares (int4-init p)) p)))
	     (and (posp m)
	          (< m p)))))

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
	          (<= (abs y) (/ m 2))))))

;; l' is defined as follows:

(defund shift-mod-list (l m)
  (list (shift-mod (nth 0 l) m)
        (shift-mod (nth 1 l) m)
	(shift-mod (nth 2 l) m)
	(shift-mod (nth 3 l) m)))

(defthmd int4p-shift-mod-list
  (implies (and (posp m) (int4p l))
           (int4p (shift-mod-list l m))))
  
;; Then (mod (sum-squares l') m) = (mod (sum-squares l) m) = 0 and 0 <= (sum-squares l') 
;; <= m * m.  Suppose (sum-squares l') = 0.  Then each yi = 0, which implies m divides
;; each xi.  But then m * m divides (sum-squares l) = m * p and m divides p, a contradiction.
;; On the other hand, suppose (sum-squares l') = m * m.  Then for each i, yi = m/2, which 
;; implies (mod xi m) = m/2 and (mod (* xi xi) (* m m)) = (mod (/ (* m m) 4) (* m m)) and
;; again (* m m) divides (sum-squares l), a contradiction.  Thus, (sum-squares l') = r * m, 
;; where 0 < r < m:

(defthmd shift-mod-m/2
  (implies (and (posp m) (integerp x) (equal (shift-mod x m) (/ m 2)))
           (equal (mod x m) (/ m 2))))

(defthmd shift-mod-0
  (implies (and (posp m) (integerp x) (equal (shift-mod x m) 0))
           (equal (mod x m) 0)))

(defthmd shift-mod-sqr-0
  (implies (and (posp m) (integerp x))
           (let ((y (shift-mod x m)))
	     (and (integerp y)
	          (or (> (* y y) 0)
		      (and (equal (* y y) 0)
		           (divides (* m m) (* x x))))))))

(defthmd sum-squares-shift-mod-list
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
           (let ((r (/ (sum-squares (shift-mod-list l m)) m)))
	     (and (posp r)
	          (< r m)))))

;; Now consider the list l'' = (prod4 l l') = (p0 p1 p3 p3).  By prod4-lemma,
;; (sum-squares l'') = (sum-squares l) * (sum-squares l') = m * p * r * m.  We shall 
;; show that each pi is divisible by m:

;; (mod p0 m) = (mod (+ (* x0 y0) (* x1 y1) (* x2 y2) (* x3 y3)) m)
;;            = (mod (+ (* x0 x0) (* x1 x1) (* x2 x2  (* x3 x3)) m)
;;            = (mod (sum-squares l) m)
;;	      = 0.

(defthmd m-divides-nth-0-prod
  (implies (and (posp m) (int4p l) (divides m (sum-squares l)))
           (divides m (nth 0 (prod4 l (shift-mod-list l m))))))

;; (mod p1 m) = (mod (+ (* x0 y1) (- (* x1 y0)) (* x2 y3) (- (* x3 y2)) m)
;;            = (mod (+ (* x0 x1) (- (* x1 x0)) (* x2 x3) (- (* x3 x2)) m)
;;	      = (mod 0 m)
;;	      = 0.

(defthmd m-divides-nth-1-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 1 (prod4 l (shift-mod-list l m))))))


;; (mod p2 m) = (mod (+ (* x0 y2) (- (* x1 y3)) (- (* x2 y0)) (* x3 y1)) m)
;;            = (mod (+ (* x0 x2) (- (* x1 x3)) (- (* x2 x0)) (* x3 x1)) m)
;;	      = (mod 0 m)
;;	      = 0.

(defthmd m-divides-nth-2-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 2 (prod4 l (shift-mod-list l m))))))

;; (mod p3 m) = (mod (+ (* x0 y3) (* x1 y2) (- (* x2 y1)) (- (* x3 y0)) m)
;;            = (mod (+ (* x0 x3) (* x1 x2) (- (* x2 x1)) (- (* x3 x0)) m)
;;	      = (mod 0 m)
;;	      = 0.

(defthmd m-divides-nth-3-prod
  (implies (and (posp m) (int4p l))
           (divides m (nth 3 (prod4 l (shift-mod-list l m))))))

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
           (int4p (reduce-int4 l p))))

(defthmd sum-squares-reduce-int4
  (implies (and (primep p) (oddp p) (natp m) (> m 1) (< m p)
                (int4p l) (equal (sum-squares l) (* m p)))
	   (let ((r (/ (sum-squares (reduce-int4 l p)) p)))
 	     (and (posp r)
	          (< r m)))))
	      
;; Applying reduce-int4 recursively, we have an int4 with sum of squares p:

(defun int4-prime-aux (l p)
  (declare (xargs :measure (nfix (sum-squares l))))
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
	        (equal (sum-squares (int4-prime-aux l p)) p))))

(defund int4-prime (p)
  (if (equal p 2)
      '(1 1 0 0)
    (int4-prime-aux (int4-init p) p)))

(defthmd sum-squares-int4-prime
  (implies (primep p)
           (and (int4p (int4-prime p))
                (equal (sum-squares (int4-prime p))
	               p))))

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
		          (sum-squares acc))))))

(defund int4-prime-power (p k)
  (int4-prime-power-aux k (int4-prime p) '(1 0 0 0)))

(defthmd sum-squares-int4-prime-power
  (implies (and (primep p) (natp k))
           (and (int4p (int4-prime-power p k))
	        (equal (sum-squares (int4-prime-power p k))
	               (expt p k)))))

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
		       (pow-prod l)))))

(defund int4-nat (n)
  (if (zp n)
      '(0 0 0 0)
    (int4-nat-aux (prime-fact n))))

(defthmd nat-sum-of-4-squares
  (implies (natp n)
           (and (int4p (int4-nat n))
	        (equal (sum-squares (int4-nat n)) n))))

    
  
  

