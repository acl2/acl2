(in-package "DM")

(include-book "euclid")
(include-book "euler")
(include-book "projects/groups/lists" :dir :system)
(include-book "rtl/rel11/lib/basic" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; It is easily shown that if an odd prime p is a sum of 2 squares,
;; then (mod p 4) = 1:

(local-defthmd mod-4-vals
  (implies (integerp x)
           (member (mod x 4) '(0 1 2 3))))

(local-defthmd prime-mod-4-vals
  (implies (and (primep p) (not (equal p 2)))
           (member (mod p 4) '(1 3)))
  :hints (("Goal" :in-theory (enable divides)
                  :use ((:instance primep-no-divisor (d 2))
                        (:instance mod-4-vals (x p))
			(:instance rtl::mod-def (x p) (rtl::y 4))))))

(local-defthmd square-mod-4
  (implies (integerp a)
           (member (mod (* a a) 4)
	           '(0 1)))
  :hints (("Goal" :use ((:instance mod-4-vals (x a))
			(:instance rtl::mod-mod-times (rtl::n 4) (rtl::a a) (rtl::b a))
			(:instance rtl::mod-mod-times (rtl::n 4) (rtl::a a) (rtl::b (mod a 4)))))))

(local-defthmd sum-squares-mod-4
  (implies (and (integerp a) (integerp b))
           (member (mod (+ (* a a) (* b b)) 4)
	           '(0 1 2)))
  :hints (("Goal" :use (square-mod-4
                        (:instance square-mod-4 (a b))
			(:instance rtl::mod-sum (rtl::n 4) (rtl::a (* a a)) (rtl::b (* b b)))
			(:instance rtl::mod-sum (rtl::n 4) (rtl::a (mod (* b b) 4)) (rtl::b (* a a)))))))

(defthm prime-sum-squares
  (implies (and (primep p)
                (natp a)
		(natp b)
		(equal (+ (* a a) (* b b)) p))
	   (or (equal p 2)
	       (equal (mod p 4) 1)))
  :rule-classes ()
  :hints (("Goal" :use (prime-mod-4-vals sum-squares-mod-4))))

;; Our objective is the converse:

;; (defthmd prime-sum-squares-converse
;;   (implies (and (primep p)
;;                 (equal (mod p 4) 1))
;;            (let* ((pair (square-pair p))
;;                   (a (car pair))
;;                   (b (cdr pair)))
;;              (and (natp a)
;;                   (natp b)
;;                   (equal (+ (* a a) (* b b))
;;                          p)))))

;; According to the 1st supplement to the law of quadratic reciprocity, if
;; (mod p 4) = 1, then  -1 is a quadratic residue mod p, i.e., there exists
;; j, 0 < j < p, such that (mod (* j j) p) = mod -1 p).  This j is computed
;; by the function root1:

(defthmd root1-minus-1
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (let ((j (root1 -1 p)))
	     (and (posp j)
	          (< j p)
		  (equal (mod (* j j) p) (mod -1 p)))))
  :hints (("Goal" :use (first-supplement (:instance res-root1 (m -1))))))

;; (sqrt-list p) is a list of all nats n such that (* n n) <= p:

(defun sqrt-list-aux (p n)
  (if (zp n)
      (list 0)
    (if (< p (* n n))
        (sqrt-list-aux p (1- n))
      (cons n (sqrt-list-aux p (1- n))))))

(defund sqrt-list (p)
  (sqrt-list-aux p p))

;; A characterization of the members of (sqrt-list p):

(local-defthmd member-sqrt-list-aux
  (implies (and (posp p) (natp n))
           (iff (member-equal k (sqrt-list-aux p n))
	        (and (natp k)
		     (<= k n)
	             (<= (* k k) p)))))
		     
(defthmd member-sqrt-list
  (implies (posp p)
           (iff (member-equal n (sqrt-list p))
	        (and (natp n)
	             (<= (* n n) p))))
  :hints (("Goal" :in-theory (enable sqrt-list)
                  :use ((:instance member-sqrt-list-aux (n p) (k n))))))

;; It follows from member-sqrt-list that (sqrt-list p) is a dlist:

(local-defthmd dlistp-sqrt-list-aux
  (implies (and (posp p) (natp n))
           (dlistp (sqrt-list-aux p n)))
  :hints (("Subgoal *1/7" :use ((:instance member-sqrt-list-aux (k n) (n (1- n)))))))

(defthmd dlistp-sqrt-list
  (implies (posp p)
           (dlistp (sqrt-list p)))
  :hints (("Goal" :in-theory (enable sqrt-list)
                  :use ((:instance dlistp-sqrt-list-aux (n p))))))

;; It follows from member-sqrt-list that every member of (sqrt-list p) is less than (len (sqrt-list p)):

(local-defun natp-2-induct (k n)
  (if (zp n)
      k
    (list (natp-2-induct k (1- n))
          (natp-2-induct (1- k) (1- n)))))

(local-defthmd member-len-sqrt-list-aux
  (implies (and (posp p) (natp k) (natp n)
                (member-equal k (sqrt-list-aux p n)))
	   (< k (len (sqrt-list-aux p n))))
  :hints (("Goal" :induct (natp-2-induct k n))  
          ("Subgoal *1/2" :use ((:instance member-sqrt-list-aux (k (1- k)) (n (1- n)))))))

(defthmd member-len-sqrt-list
  (implies (and (posp p) (natp k)
                (member-equal k (sqrt-list p)))
	   (< k (len (sqrt-list p))))
  :hints (("Goal" :in-theory (enable sqrt-list)
                  :use ((:instance member-len-sqrt-list-aux (n p))))))

;; Consequently, the length of (sqrt-list p) is greater than the square root of p:

(defthmd len-sqrt-list
  (implies (posp p)
           (> (* (len (sqrt-list p))
	         (len (sqrt-list p)))
	      p))
  :hints (("Goal" :use ((:instance member-len-sqrt-list (k (len (sqrt-list p))))
                        (:instance member-sqrt-list (n (len (sqrt-list p))))))))

;; We define a list of all pairs of members of a list l:

(defun cart-prod (l r)
  (if (consp l)
      (append (conses (car l) r)
	      (cart-prod (cdr l) r))
    ()))

(defund cart-square (l)
  (cart-prod l l))

(local-defthmd member-cart-prod
  (implies (member-equal x (cart-prod l m))
           (and (consp x)
	        (member-equal (car x) l)
		(member-equal (cdr x) m))))

(defthmd member-cart-square
  (implies (member-equal x (cart-square l))
           (and (consp x)
	        (member-equal (car x) l)
		(member-equal (cdr x) l)))
  :hints (("Goal" :in-theory (enable cart-square)
                  :use ((:instance member-cart-prod (m l))))))

;; If l is a dlist, then so is (cart-square l):

(local-defthmd member-car-cart-prod
  (implies (member-equal x (cart-prod l m))
           (member-equal (car x) l)))

(local-defthmd member-conses
  (implies (member-equal z (conses x l))
           (and (equal (car z) x)
	        (member-equal (cdr z) l))))

(local-defthmd member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l) (member-equal x m))))

(local-defthmd dlistp-append-conses
  (implies (and (dlistp (cart-prod l m))
                (dlistp n)
		(not (member-equal x l)))
	   (dlistp (append (conses x n) (cart-prod l m))))
  :hints (("Goal" :induct (dlistp n))
          ("Subgoal *1/1" :in-theory (enable member-append)
	                  :use ((:instance member-conses (z (cons x (car n))) (l (cdr n)))
	                        (:instance member-car-cart-prod (x (cons x (car n))))))))

(local-defthmd dlistp-cart-prod
  (implies (and (dlistp l) (dlistp m))
           (dlistp (cart-prod l m)))
  :hints (("Subgoal *1/2" :use ((:instance dlistp-append-conses (x (car l)) (n m) (l (cdr l)))))))

(defthm dlistp-cart-square
  (implies (dlistp l)
           (dlistp (cart-square l)))
  :hints (("Goal" :in-theory (enable dlistp-cart-prod cart-square))))

;; The length of the list of pairs of members of (sqrt-list p) is greater than p:

(local-defthm len-conses
  (equal (len (conses x l))
         (len l)))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(local-defthm len-cart-prod
  (equal (len (cart-prod l m))
         (* (len l) (len m))))

(local-defthm len-cart-square
  (equal (len (cart-square l))
         (* (len l) (len l)))
  :hints (("Goal" :in-theory (enable cart-square))))

(defthmd len-cart-square-sqrt-list
  (implies (posp p)
           (> (len (cart-square (sqrt-list p)))
	      p))
  :hints (("Goal" :use (len-sqrt-list))))

;; Given an integer j and a list of pairs of integers (a . b), compute the list
;; of values (- a (* j b)):

(defun mod-list (l j p)
  (if (consp l)
      (cons (mod (- (caar l) (* j (cdar l))) p)
            (mod-list (cdr l) j p))
    ()))

(local-defthm len-mod-list
  (equal (len (mod-list l j p))
         (len l)))

(local-defthm true-listp-mod-list
  (true-listp (mod-list l j p)))

(local-defthmd nth-mod-list
  (implies (and (natp k) (< k (len l)))
           (equal (nth k (mod-list l j p))
	          (mod (- (car (nth k l)) (* j (cdr (nth k l)))) p))))

;; We are interested in the following instance of mod-list:

(defund diff-list (p)
  (mod-list (cart-square (sqrt-list p))
            (root1 -1 p)
	    p))

;; Note that the length of this list is that of (cart-square (sqrt-list p)):

(defthmd len-diff-list
  (implies (posp p)
           (and (equal (len (diff-list p)) (len (cart-square (sqrt-list p))))
                (> (len (diff-list p)) p)))
  :hints (("Goal" :in-theory (enable diff-list)
                  :use (len-cart-square-sqrt-list))))

(local-defthm true-listp-diff-list
  (true-listp (diff-list p))
  :hints (("Goal" :in-theory (enable diff-list))))

;;  We have the following formula for the kth member of (diff-list p):

(defthmd nth-diff-list
  (implies (and (posp p) (natp k) (< k (len (cart-square (sqrt-list p)))))
           (equal (nth k (diff-list p))
	          (mod (- (car (nth k (cart-square (sqrt-list p))))
		          (* (root1 -1 p) (cdr (nth k (cart-square (sqrt-list p)))))) p)))
  :hints (("Goal" :in-theory '(diff-list)
                  :use (len-diff-list
		        (:instance nth-mod-list (l (cart-square (sqrt-list p))) (j (root1 -1 p)))))))

;; (diff-list p) is a sublist of the list (nats p) of the first p natural nunbers:

(defun nats (p)
  (if (zp p)
      ()
    (cons (1- p) (nats (1- p)))))

(defthm len-nats
  (implies (natp p)
           (equal (len (nats p)) p)))

(local-defthm member-nats
  (implies (posp p)
           (iff (member-equal x (nats p))
	        (and (natp x)
		     (< x p)))))

(local-defun int-pair-list-p (l)
  (if (consp l)
      (and (consp (car l))
           (integerp (caar l))
	   (integerp (cdar l))
	   (int-pair-list-p (cdr l)))
    t))

(local-defthmd member-cart-square-sqrt-list
  (implies (and (posp p)
                (member-equal x (cart-square (sqrt-list p))))
	   (and (consp x)
	        (natp (car x)) (<= (* (car x) (car x)) p)
		(natp (cdr x)) (<= (* (cdr x) (cdr x)) p)))
  :hints (("Goal" :use ((:instance member-cart-square (l (sqrt-list p)))
                        (:instance member-sqrt-list (n (car x)))
                        (:instance member-sqrt-list (n (cdr x)))))))

(local-defthm int-cart-square-sqrt-list
  (implies (and (posp p)
                (sublistp l (cart-square (sqrt-list p))))
           (int-pair-list-p l))
  :hints (("Subgoal *1/5" :use ((:instance member-cart-square-sqrt-list (x (car l)))))
          ("Subgoal *1/4" :use ((:instance member-cart-square-sqrt-list (x (car l)))))
          ("Subgoal *1/3" :use ((:instance member-cart-square-sqrt-list (x (car l)))))))

(local-defthmd sublistp-mod-list-nats
  (implies (and (int-pair-list-p l)
                (integerp j)
		(posp p))
	   (sublistp (mod-list l j p) (nats p))))

(defthmd sublistp-diff-list-nats
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (sublistp (diff-list p)
	             (nats p)))
  :hints (("Goal" :in-theory (enable diff-list)
                  :use (root1-minus-1
		        (:instance int-cart-square-sqrt-list (l (cart-square (sqrt-list p))))
		        (:instance sublistp-mod-list-nats (l (cart-square (sqrt-list p))) (j (root1 -1 p)))))))

;; By sublistp-<=-len, since (len (diff-list p)) > p = (len (nats p)), the members
;; od (diff-list p) are not distinct:

(defthmd not-dlistp-diff-list
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (not (dlistp (diff-list p))))
  :hints (("Goal" :use (len-diff-list sublistp-diff-list-nats
                        (:instance sublistp-<=-len (l (diff-list p)) (m (nats p)))))))

;; By dcex-lemma, there exist distinct indices m = (dcex1 (diff-list p)) and
;; n = (dcex2 (diff-list p)) such that 0 <= m < n < (len (diff-list p)) and
;; (nth m (diff-list p)) = (nth n (diff-list p)).  We extract the corresponding
;; members of (cart-square (sqrt-list p))::

(defthmd diff-list-diff
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (let ((d1 (dcex1 (diff-list p))) (d2 (dcex2 (diff-list p))))
	     (and (natp d1) (natp d2) (< d1 d2) (< d2 (len (diff-list p)))
	          (equal (nth d1 (diff-list p)) (nth d2 (diff-list p))))))
  :hints (("Goal" :use (not-dlistp-diff-list
                        (:instance dcex-lemma (l (diff-list p)))))))

(defund pair1 (p)
  (nth (dcex1 (diff-list p))
       (cart-square (sqrt-list p))))

(defund pair2 (p)
  (nth (dcex2 (diff-list p))
       (cart-square (sqrt-list p))))

;; Note that these two pairs are distinct.
;; Let (pair1 p) = (a1 . b1) and (pair2 p) = (a2 . b2).  Let j = (root1 -1 p).
;; Then (mod (- a1 (* j b1)) p) = (mod (- a2 (* j b2)) p), which implies
;; (mod (- a1 a2) p) = (mod (* j (- b1 b2)) p).  Let a3 = (- a1 a2) and b3 = (- b1 b2).
;; Since (mod (* j j) p) = (mod -1 p), we have (mod (* a a) p) = (mod (- (* b b)) p),
;; and (+ (* a a) (* b b)) is divisible by p.  But this sum is positive and less than
;; (* 2 p), and therefore equal to p.

(local-defthmd diff-cart-square
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (and (member-equal (pair1 p) (cart-square (sqrt-list p)))
	        (member-equal (pair2 p) (cart-square (sqrt-list p)))
		(not (equal (pair1 p) (pair2 p)))))
  :hints (("Goal" :in-theory (enable pair1 pair2)
                  :use (len-diff-list diff-list-diff
                        (:instance nth-dlist-distinct (l (cart-square (sqrt-list p)))
			                              (i (dcex1 (diff-list p)))
						      (j (dcex2 (diff-list p))))))))

(local-defthmd equal-cart-square
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (mod (- (car (pair1 p)) (* (root1 -1 p) (cdr (pair1 p)))) p)
	          (mod (- (car (pair2 p)) (* (root1 -1 p) (cdr (pair2 p)))) p)))
  :hints (("Goal" :in-theory '(pair1 pair2 posp)
                  :use (len-diff-list diff-list-diff primep-gt-1
			(:instance nth-diff-list (k (dcex1 (diff-list p))))
			(:instance nth-diff-list (k (dcex2 (diff-list p))))))))

(defund a1 (p) (car (pair1 p)))
(defund b1 (p) (cdr (pair1 p)))
(defund a2 (p) (car (pair2 p)))
(defund b2 (p) (cdr (pair2 p)))

(local-defthmd a-b-bounds
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (and (natp (a1 p)) (<= (* (a1 p) (a1 p)) p)
	        (natp (b1 p)) (<= (* (b1 p) (b1 p)) p)
	        (natp (a2 p)) (<= (* (a2 p) (a2 p)) p)
	        (natp (b2 p)) (<= (* (b2 p) (b2 p)) p)
		(not (and (equal (a1 p) (a2 p)) (equal (b1 p) (b2 p))))))
  :hints (("Goal" :in-theory '(a1 a2 b1 b2 posp)
                  :use (diff-cart-square primep-gt-1
		        (:instance member-cart-square-sqrt-list (x (pair1 p)))
		        (:instance member-cart-square-sqrt-list (x (pair2 p)))))))

(local-defthmd mod-a-b-1
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (equal (mod (- (a1 p) (* (root1 -1 p) (b1 p))) p)
	          (mod (- (a2 p) (* (root1 -1 p) (b2 p))) p)))
  :hints (("Goal" :in-theory '(a1 a2 b1 b2 posp)
                  :use (diff-cart-square equal-cart-square primep-gt-1
		        (:instance member-cart-square-sqrt-list (x (pair1 p)))
		        (:instance member-cart-square-sqrt-list (x (pair2 p)))))))

(local-defthmd mod-a-b-2
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (integerp (/ (- (- (a1 p) (a2 p))
	                   (* (root1 -1 p) (- (b1 p) (b2 p))))
			p)))
  :hints (("Goal" :use (a-b-bounds mod-a-b-1 root1-minus-1  
                        (:instance rtl::mod-equal-int (rtl::n p)
			                              (rtl::a (- (a1 p) (* (root1 -1 p) (b1 p))))
						      (rtl::b (- (a2 p) (* (root1 -1 p) (b2 p)))))))))

(local-defthmd mod-a-b-3
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (mod (- (a1 p) (a2 p)) p)
	          (mod (* (root1 -1 p) (- (b1 p) (b2 p))) p)))		  
  :hints (("Goal" :use (a-b-bounds mod-a-b-2 root1-minus-1
                        (:instance rtl::mod-equal-int-reverse (rtl::n p)
                                                              (rtl::a (- (a1 p) (a2 p)))
                                                              (rtl::b (* (root1 -1 p) (- (b1 p) (b2 p)))))))))

(defund a3 (p) (- (a1 p) (a2 p)))
(defund b3 (p) (- (b1 p) (b2 p)))

(local-defthmd a-b-not-zero
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (not (and (equal (a3 p) 0) (equal (b3 p) 0))))
  :hints (("Goal" :in-theory (enable a3 b3)
                  :use (a-b-bounds))))

(local-defthmd mod-a-b-4
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (mod (a3 p) p)
	          (mod (* (root1 -1 p) (b3 p)) p)))
  :hints (("Goal" :use (mod-a-b-3) :in-theory '(a3 b3))))

(local-defthmd a-b-square-bounds-1
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (and (integerp (a3 p)) (<= (abs (a3 p)) (max (a1 p) (a2 p)))
	        (integerp (b3 p)) (<= (abs (b3 p)) (max (b1 p) (b2 p)))))
  :hints (("Goal" :in-theory (enable a3 b3)
                  :use (a-b-bounds))))

(local-defthmd a-b-square-bounds-2
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (and (integerp (a3 p)) (<= (* (a3 p) (a3 p)) p)
	        (integerp (b3 p)) (<= (* (b3 p) (b3 p)) p)))
  :hints (("Goal" :nonlinearp t
                  :use (a-b-bounds a-b-square-bounds-1))))

(local-defthmd a-b-square-bounds
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (and (integerp (a3 p)) (< (* (a3 p) (a3 p)) p)
	        (integerp (b3 p)) (< (* (b3 p) (b3 p)) p)))
  :hints (("Goal" :in-theory (enable divides)
                  :use (a-b-square-bounds-2
		        (:instance euclid (a (a3 p)) (b (a3 p)))
		        (:instance euclid (a (b3 p)) (b (b3 p)))))))

(local-defthm int-a3
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (integerp (a3 p)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (a-b-square-bounds-1))))

(local-defthm int-b3
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (integerp (b3 p)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (a-b-square-bounds-1))))

(local-defthmd mod-a-b-5
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (mod (* (a3 p) (a3 p)) p)
	          (mod (* (root1 -1 p) (root1 -1 p) (b3 p) (b3 p)) p)))
  :hints (("Goal" :use (mod-a-b-4
                        (:instance rtl::mod-times-mod (rtl::n p) (rtl::a (a3 p)) (rtl::b (* (root1 -1 p) (b3 p))) (rtl::c (a3 p)))
                        (:instance rtl::mod-times-mod (rtl::n p) (rtl::a (a3 p)) (rtl::b (* (root1 -1 p) (b3 p))) (rtl::c (* (root1 -1 p) (b3 p))))))))

(local-defthmd mod-a-b-6
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (mod (* (a3 p) (a3 p)) p)
	          (mod (- (* (b3 p) (b3 p))) p)))
  :hints (("Goal" :use (mod-a-b-5 root1-minus-1
                        (:instance rtl::mod-mod-times (rtl::n p) (rtl::a (* (root1 -1 p) (root1 -1 p))) (rtl::b (* (b3 p) (b3 p))))))))

(local-defthmd mod-a-b-7
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (integerp (/ (+ (* (a3 p) (a3 p)) (* (b3 p) (b3 p)))
	                p)))
  :hints (("Goal" :use (mod-a-b-6
                        (:instance rtl::mod-equal-int (rtl::n p) (rtl::a (* (a3 p) (a3 p))) (rtl::b (- (* (b3 p) (b3 p)))))))))

;; This is getting ridiculous.

(local-defthm mod-a-b-8
  (implies (and (posp n) (< n 2))
           (equal n 1))
  :rule-classes ())

(local-defthm mod-a-b-9
  (implies (and (primep p) (posp n) (< n (* 2 p)) (integerp (/ n p)))
           (equal n p))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (:instance mod-a-b-8 (n (/ n p))))))

(local-defthmd mod-a-b-10
  (implies (and (integerp x) (not (equal x 0)))
           (> (* x x) 0))
  :hints (("Goal" :cases ((> x 0)))))
           
(local-defthmd mod-a-b-11
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (posp (+ (* (a3 p) (a3 p)) (* (b3 p) (b3 p)))))
  :hints (("Goal" :use (a-b-not-zero (:instance mod-a-b-10 (x (a3 p))) (:instance mod-a-b-10 (x (b3 p)))))))

(defthmd sum-squares-a-b
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (+ (* (a3 p) (a3 p)) (* (b3 p) (b3 p)))
	          p))
  :hints (("Goal" :use (mod-a-b-7 a-b-not-zero a-b-square-bounds mod-a-b-11
                        (:instance mod-a-b-9 (n (+ (* (a3 p) (a3 p)) (* (b3 p) (b3 p)))))))))

;; Thus, we define (square-pair p) to consist of the absolute values of a3 and b3:

(defun square-pair (p)
  (cons (abs (a3 p)) (abs (b3 p))))

;; Note that this pair is readily computable:

;; DM !>(square-pair 937)
;; (24 . 19)
;; DM !>(+ (* 24 24) (* 19 19))
;; 937

;; The desired result follows from sum-squares-a-b:

(defthmd prime-sum-squares-converse
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (let* ((pair (square-pair p))
	          (a (car pair))
		  (b (cdr pair)))
	     (and (natp a)
	          (natp b)
		  (equal (+ (* a a) (* b b))
		         p))))
  :hints (("Goal" :use (sum-squares-a-b))))
