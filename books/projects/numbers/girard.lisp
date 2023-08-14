(in-package "DM")

(include-book "euclid")
(include-book "euler")
(include-book "projects/groups/lists" :dir :system)
(local (include-book "support/girard"))

;; It is easily shown that if an odd prime p is a sum of 2 squares,
;; then (mod p 4) = 1:

(defthm prime-sum-squares
  (implies (and (primep p)
                (natp a)
		(natp b)
		(equal (+ (* a a) (* b b)) p))
	   (or (equal p 2)
	       (equal (mod p 4) 1)))
  :rule-classes ())

;; Our objective is the converse, which was first observed by Girard in 1625.  Thus, given a 
;; prime p with (mod p 4) = 1, we shall construct a pair of natural numbers a and b such that
;; p = (+ (* a a) (* b b)):

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

;; According to the 1st supplement to the law of quadratic reciprocity (see euler.lisp),
;; if (mod p 4) = 1, then  -1 is a quadratic residue mod p, i.e., there exists j such that
;; (mod (* j j) p) = mod -1 p).  This j is computed by the function root1:

(defthmd root1-minus-1
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (let ((j (root1 -1 p)))
	     (and (posp j)
	          (< j p)
		  (equal (mod (* j j) p) (mod -1 p))))))

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

(defthmd member-sqrt-list
  (implies (posp p)
           (iff (member-equal n (sqrt-list p))
	        (and (natp n)
	             (<= (* n n) p)))))

;; Note that (sqrt-list p) is a dlist:

(defthmd dlistp-sqrt-list
  (implies (posp p)
           (dlistp (sqrt-list p))))

;; It follows from member-sqrt-list that every member of (sqrt-list p) is less than
;; (len (sqrt-list p)):

(defthmd member-len-sqrt-list
  (implies (and (posp p) (natp k)
                (member-equal k (sqrt-list p)))
	   (< k (len (sqrt-list p)))))

;; Consequently, the length of (sqrt-list p) is greater than the square root of p:

(defthmd len-sqrt-list
  (implies (posp p)
           (> (* (len (sqrt-list p))
	         (len (sqrt-list p)))
	      p)))

;; We define a list of all pairs of members of a list l:

(defun cart-prod (l r)
  (if (consp l)
      (append (conses (car l) r)
              (cart-prod (cdr l) r))
    ()))

(defund cart-square (l)
  (cart-prod l l))

(defthmd member-cart-square
  (implies (member-equal x (cart-square l))
           (and (consp x)
	        (member-equal (car x) l)
		(member-equal (cdr x) l))))

;; If l is a dlist, then so is (cart-square l):

(defthm dlistp-cart-square
  (implies (dlistp l)
           (dlistp (cart-square l))))

;; The length of the list of pairs of members of (sqrt-list p) is greater than p:

(defthmd len-cart-square-sqrt-list
  (implies (posp p)
           (> (len (cart-square (sqrt-list p)))
	      p)))

;; Given an integer j and a list of pairs of integers (a . b), compute the list of
;; values (- a (* j b)):

(defun mod-list (l j p)
  (if (consp l)
      (cons (mod (- (caar l) (* j (cdar l))) p)
            (mod-list (cdr l) j p))
    ()))

;; We are interested in the following instance of mod-list:

(defund diff-list (p)
  (mod-list (cart-square (sqrt-list p))
            (root1 -1 p)
	    p))

;; Note that the length of this list is that of (cart-square (sqrt-list p)):

(defthmd len-diff-list
  (implies (posp p)
           (and (equal (len (diff-list p)) (len (cart-square (sqrt-list p))))
                (> (len (diff-list p)) p))))

;;  We have the following formula for the kth member of (diff-list p):

(defthmd nth-diff-list
  (implies (and (posp p) (natp k) (< k (len (cart-square (sqrt-list p)))))
           (equal (nth k (diff-list p))
	          (mod (- (car (nth k (cart-square (sqrt-list p))))
		          (* (root1 -1 p) (cdr (nth k (cart-square (sqrt-list p))))))
		       p))))

;; (diff-list p) is a sublist of the list (nats p) of the first p natural nunbers:

(defun nats (p)
  (if (zp p)
      ()
    (cons (1- p) (nats (1- p)))))

(defthm len-nats
  (implies (natp p)
           (equal (len (nats p)) p)))

(defthmd sublistp-diff-list-nats
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (sublistp (diff-list p)
	             (nats p))))

;; By sublistp-<=-len, since (len (diff-list p)) > p = (len (nats p)), the members of
;; (diff-list p) are not distinct:

(defthmd not-dlistp-diff-list
  (implies (and (primep p)
                (equal (mod p 4) 1))
           (not (dlistp (diff-list p)))))

;; By dcex-lemma, there exist distinct indices m = (dcex1 (diff-list p)) and
;; n = (dcex2 (diff-list p)) such that 0 <= m < n < (len (diff-list p)) and
;; (nth m (diff-list p)) = (nth n (diff-list p)).  We extract the corresponding
;; members of (cart-square (sqrt-list p))::

(defthmd diff-list-diff
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (let ((d1 (dcex1 (diff-list p))) (d2 (dcex2 (diff-list p))))
	     (and (natp d1) (natp d2) (< d1 d2) (< d2 (len (diff-list p)))
	          (equal (nth d1 (diff-list p)) (nth d2 (diff-list p)))))))

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
;; Since (mod (* j j) p) = (mod -1 p), we have (mod (* a3 a3) p) = (mod (- (* b3 b3)) p),
;; and (+ (* a3 a3) (* b3 b3)) is divisible by p.  But this sum is positive and less than
;; (* 2 p), and therefore equal to p.

(defund a1 (p) (car (pair1 p)))
(defund b1 (p) (cdr (pair1 p)))
(defund a2 (p) (car (pair2 p)))
(defund b2 (p) (cdr (pair2 p)))

(defund a3 (p) (- (a1 p) (a2 p)))
(defund b3 (p) (- (b1 p) (b2 p)))

(defthmd sum-squares-a-b
  (implies (and (primep p)
                (equal (mod p 4) 1))
	   (equal (+ (* (a3 p) (a3 p)) (* (b3 p) (b3 p)))
	          p)))

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
		         p)))))
