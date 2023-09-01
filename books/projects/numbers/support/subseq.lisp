(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(include-book "divisors")

;; A subsequence of a dlist:

(defun subseqp (l m)
  (if (consp l)
      (if (consp m)
	  (if (equal (car l) (car m))
	      (subseqp (cdr l) (cdr m))
	    (subseqp l (cdr m)))
	())
    (null l)))

;; A list of rationals:

(defun rat-listp (l)
  (if (consp l)
      (and (rationalp (car l))
	   (rat-listp (cdr l)))
    (null l)))

;; Ascending and descending lists of rationals:

(defun ascendingp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (< (car l) (cadr l))
	   (ascendingp (cdr l)))
    t))

(defun descendingp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (> (car l) (cadr l))
	   (descendingp (cdr l)))
    t))

;; Our objective is to prove that if l is a dlist of rationals of length greater
;; than (a - 1)(b - 1), where a and b are positive integers, then l has either an
;; ascending subsequence of length a or a descending subsequence of length b.  The
;; proof is based on a pair of functions that produce the longest ascending and
;; descending subsequences of l:

;;(defthm asc-desc-subseqp
;;  (implies (and (rat-listp l)
;;                (dlistp l)
;;                (posp a)
;;                (posp b)
;;                (> (len l) (* (1- a) (1- b))))
;;           (let ((asc (longest-ascending-subseq l))
;;                 (desc (longest-descending-subseq l)))
;;             (and (subseqp asc l)
;;                  (ascendingp asc)
;;                  (subseqp desc l)
;;                  (descendingp desc)
;;                  (or (>= (len asc) a)
;;                      (>= (len desc) b))))))

;; A list of all ascending subsequences of l with every member greater than x:

(defun ascending-subseqs-aux (x l)
  (if (consp l)
      (if (< x (car l))
	  (append (conses (car l) (ascending-subseqs-aux (car l) (cdr l)))
		  (ascending-subseqs-aux x (cdr l)))
	(ascending-subseqs-aux x (cdr l)))
    (list ())))

;; A list of all ascending subsequences of l:

(defun ascending-subseqs (l)
  (if (consp l)
      (append (conses (car l) (ascending-subseqs-aux (car l) (cdr l)))
	      (ascending-subseqs (cdr l)))
    (list ())))

(local-defthm member-append
  (iff (member-equal x (append l m))
       (or (member-equal x l)
           (member-equal x m))))

(local-defthm car-member-conses
  (iff (member-equal y (conses x l))
       (and (consp y) (equal (car y) x) (member-equal (cdr y) l))))

(local-defthmd subseqp-member-car
  (implies (and (consp s) (subseqp s l))
           (member (car s) l)))

(local-defthm subseqp-dlistp
  (implies (and (subseqp s l) (dlistp l)) (dlistp s)))

(local-defun ascending-subseqs-induct (s x l)
  (if (consp l)
      (list (ascending-subseqs-induct s x (cdr l))
            ;(ascending-subseqs-induct (cdr s) x (cdr l))
            (ascending-subseqs-induct (cdr s) (car l) (cdr l)))
    (list s x l)))

(local-defthmd ascending-subseqs-1
  (implies (and (rat-listp l) (dlistp l) (rationalp x) (member-equal s (ascending-subseqs-aux x l)))
           (and (subseqp s l) (ascendingp (cons x s))))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance subseqp-member-car (l (cdr l)))))))

(local-defthmd ascending-subseqs-2
  (implies (and (rat-listp l) (dlistp l) (rationalp x) (subseqp s l) (ascendingp (cons x s)))
           (member-equal s (ascending-subseqs-aux x l)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))))

(local-defthmd ascending-subseqs-3
  (implies (and (rat-listp l) (dlistp l) (member-equal s (ascending-subseqs l)))
	   (and (subseqp s l) (ascendingp s)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance subseqp-member-car (l (cdr l)))
	                        (:instance ascending-subseqs-1 (s (cdr s)) (x (car s)) (l (cdr l)))))))

(local-defthmd ascending-subseqs-4
  (implies (and (rat-listp l) (dlistp l) (subseqp s l) (ascendingp s))
           (member-equal s (ascending-subseqs l)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance ascending-subseqs-2 (s (cdr s)) (x (car s)) (l (cdr l)))))))

(defthmd member-ascending-subseqs
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (ascending-subseqs l))
	        (and  (subseqp s l) (ascendingp s))))
  :hints (("Goal" :use (ascending-subseqs-3 ascending-subseqs-4))))

;; A list of all descending subsequences of l with every member less than x:

(defun descending-subseqs-aux (x l)
  (if (consp l)
      (if (> x (car l))
	  (append (conses (car l) (descending-subseqs-aux (car l) (cdr l)))
		  (descending-subseqs-aux x (cdr l)))
	(descending-subseqs-aux x (cdr l)))
    (list ())))

;; A list of all descending subsequences of l:

(defun descending-subseqs (l)
  (if (consp l)
      (append (conses (car l) (descending-subseqs-aux (car l) (cdr l)))
	      (descending-subseqs (cdr l)))
    (list ())))

(local-defthmd descending-subseqs-1
  (implies (and (rat-listp l) (dlistp l) (rationalp x) (member-equal s (descending-subseqs-aux x l)))
           (and (subseqp s l) (descendingp (cons x s))))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance subseqp-member-car (l (cdr l)))))))

(local-defthmd descending-subseqs-2
  (implies (and (rat-listp l) (dlistp l) (rationalp x) (subseqp s l) (descendingp (cons x s)))
           (member-equal s (descending-subseqs-aux x l)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))))

(local-defthmd descending-subseqs-3
  (implies (and (rat-listp l) (dlistp l) (member-equal s (descending-subseqs l)))
	   (and (subseqp s l) (descendingp s)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance subseqp-member-car (l (cdr l)))
	                        (:instance descending-subseqs-1 (s (cdr s)) (x (car s)) (l (cdr l)))))))

(local-defthmd descending-subseqs-4
  (implies (and (rat-listp l) (dlistp l) (subseqp s l) (descendingp s))
           (member-equal s (descending-subseqs l)))
  :hints (("Goal" :induct (ascending-subseqs-induct s x l))
          ("Subgoal *1/1" :use ((:instance descending-subseqs-2 (s (cdr s)) (x (car s)) (l (cdr l)))))))

(defthmd member-descending-subseqs
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (descending-subseqs l))
	        (and  (subseqp s l) (descendingp s))))
  :hints (("Goal" :use (descending-subseqs-3 descending-subseqs-4))))

;; The longest member of a lists of lists:

(defun longest (l)
  (if (and (consp l) (consp (cdr l)))
      (let ((m (longest (cdr l))))
	(if (< (len (car l)) (len m))
	    m
	  (car l)))
    (car l)))

(defthm member-longest
  (implies (consp l)
           (member-equal (longest l) l)))

(defthmd longest-longest
  (implies (member-equal s l)
           (>= (len (longest l)) (len s))))

;; The longest ascending subsequence of l:

(defund longest-ascending-subseq (l)
  (longest (ascending-subseqs l)))

(defthmd longest-ascending-longest
  (implies (and (rat-listp l) (dlistp l))
           (let ((m (longest-ascending-subseq l)))
	     (and (subseqp m l)
	          (ascendingp m)
		  (implies (and (subseqp s l) (ascendingp s))
		           (>= (len m) (len s))))))
  :hints (("Goal" :in-theory (enable longest-ascending-subseq )
                  :use (member-ascending-subseqs
		        (:instance longest-longest (l (ascending-subseqs l)))		  
		        (:instance member-ascending-subseqs (s (longest-ascending-subseq l)))))))

;; The longest descending subsequence of l:

(defund longest-descending-subseq (l)
  (longest (descending-subseqs l)))

(defthmd longest-descending-longest
  (implies (and (rat-listp l) (dlistp l))
           (let ((m (longest-descending-subseq l)))
	     (and (subseqp m l)
	          (descendingp m)
		  (implies (and (subseqp s l) (descendingp s))
		           (>= (len m) (len s))))))
  :hints (("Goal" :in-theory (enable longest-descending-subseq )
                  :use (member-descending-subseqs
		        (:instance longest-longest (l (descending-subseqs l)))		  
		        (:instance member-descending-subseqs (s (longest-descending-subseq l)))))))

;; Given a mewmber x of l, construct a list of all axcending subsequences of l
;; that end with x:


(defun lists-ending-with (x l)
  (if (consp l)
      (if (and (consp (car l)) (equal (car (last (car l))) x))
	  (cons (car l) (lists-ending-with x (cdr l)))
        (lists-ending-with x (cdr l)))
    ()))

(local-defun cdr-induct (l)
  (if (consp l)
      (list (cdr-induct (cdr l)))
    (list l)))

(local-defthmd member-lists-ending-with
  (iff (member-equal s (lists-ending-with x l))
       (and (member-equal s l)
            (consp s)
	    (equal (car (last s)) x)))
  :hints (("Goal" :induct (cdr-induct l))))

(defund ascending-subseqs-ending-with (x l)
  (lists-ending-with x (ascending-subseqs l)))

(defthmd member-ascending-subseqs-ending-with
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (ascending-subseqs-ending-with x l))
	        (and (consp s)
	             (equal (car (last s)) x)
		     (subseqp s l)
		     (ascendingp s))))
  :hints (("Goal" :in-theory (enable ascending-subseqs-ending-with)
                  :use (member-ascending-subseqs
                        (:instance member-lists-ending-with (l (ascending-subseqs l)))))))

;; A list of all descending subsequences of l that end with x:

(defund descending-subseqs-ending-with (x l)
  (lists-ending-with x (descending-subseqs l)))

(defthmd member-descending-subseqs-ending-with
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (descending-subseqs-ending-with x l))
	        (and (consp s)
	             (equal (car (last s)) x)
		     (subseqp s l)
		     (descendingp s))))
  :hints (("Goal" :in-theory (enable descending-subseqs-ending-with)
                  :use (member-descending-subseqs
                        (:instance member-lists-ending-with (l (descending-subseqs l)))))))

(local-defthm subseq-len-1
  (implies (member-equal x l)
           (and (ascendingp (list x))
	        (descendingp (list x))
	        (subseqp (list x) l))))

(local-defthm consp-ascending-subseqs-ending-with
  (implies (and (rat-listp l) (dlistp l) (member x l))
           (and (consp (ascending-subseqs-ending-with x l))
                (consp (descending-subseqs-ending-with x l))))
  :hints (("Goal" :in-theory (enable ascending-subseqs-ending-with descending-subseqs-ending-with)
                  :use (subseq-len-1
                        (:instance member-lists-ending-with (s (list x)) (l (ascending-subseqs l)))
                        (:instance member-lists-ending-with (s (list x)) (l (descending-subseqs l)))
			(:instance member-ascending-subseqs (s (list x)))
			(:instance member-descending-subseqs (s (list x)))))))

;; An function from the members of l to pairs of positive integers:

(defund max-lens (x l)
  (cons (len (longest (ascending-subseqs-ending-with x l)))
        (len (longest (descending-subseqs-ending-with x l)))))

;; Suppose x and y are distinct members of l with (index x l) < (index y l).  If x < y,
;; then the longest ascending subseqhence of l that ends with x may be extended to y.
;; Thus, there is a longer longest ascending subseqence of l that ends with y:

(local-defthmd ascendingp-append
  (implies (and (ascendingp s1)
                (ascendingp s2)
		(< (car (last s1)) (car s2)))
	   (ascendingp (append s1 s2))))

(local-defthmd descendingp-append
  (implies (and (descendingp s1)
                (descendingp s2)
		(> (car (last s1)) (car s2)))
	   (descendingp (append s1 s2))))

(local-defthmd member-last
  (implies (consp l)
           (member-equal (car (last l)) l)))

(local-defthm subseqp-sublistp
  (implies (subseqp s l)
           (sublistp s l))
  :hints (("Goal" :induct (subseqp s l))))

(local-defthm subseqp-append
  (implies (and (consp s)
                (subseqp s l)
		(dlistp l)
                (member-equal y l)
		(> (index y l) (index (car (last s)) l)))
	   (subseqp (append s (list y)) l))
  :hints (("Subgoal *1/10" :use ((:instance member-sublist (x (car l)) (l s) (m (cdr l)))
			         (:instance member-last (l s))))
          ("Subgoal *1/5" :in-theory (disable member-sublist)
	                    :use ((:instance member-sublist (x (car l)) (l (cdr s)) (m (cdr l)))
			        (:instance member-last (l (cdr s)))))))

(local-defthm last-append
  (implies (consp m)
           (equal (last (append l m))
	          (last m))))

(local-defthm len-append
  (equal (len (append l m))
         (+ (len l) (len m))))

(defthmd diff-longest-ascending
  (implies (and (rat-listp l) (dlistp l) (member-equal x l) (member-equal y l)
                (< (index x l) (index y l)) (< x y))
	   (< (len (longest (ascending-subseqs-ending-with x l)))
	      (len (longest (ascending-subseqs-ending-with y l)))))
  :hints (("Goal" :use ((:instance subseqp-append (s (longest (ascending-subseqs-ending-with x l))))
                        (:instance member-ascending-subseqs-ending-with (x y) (s (list y)))
                        (:instance member-ascending-subseqs-ending-with (s (longest (ascending-subseqs-ending-with x l))))
			(:instance ascendingp-append (s1 (longest (ascending-subseqs-ending-with x l))) (s2 (list y)))
			(:instance member-ascending-subseqs-ending-with (s (append (longest (ascending-subseqs-ending-with x l))
			                                                           (list y)))
								        (x y))
			(:instance longest-longest (l (ascending-subseqs-ending-with y l))
			                           (s (append (longest (ascending-subseqs-ending-with x l)) (list y))))))))

;; On the other hand, if x < y, then the longest descending subseqhence of l that ends
;; with x may be extended to y. Thus, there is a longer longest descending subseqhence of
;; l that ends with y:

(defthmd diff-longest-descending
  (implies (and (rat-listp l) (dlistp l) (member-equal x l) (member-equal y l)
                (< (index x l) (index y l)) (> x y))
	   (< (len (longest (descending-subseqs-ending-with x l)))
	      (len (longest (descending-subseqs-ending-with y l)))))
  :hints (("Goal" :use ((:instance subseqp-append (s (longest (descending-subseqs-ending-with x l))))
                        (:instance member-descending-subseqs-ending-with (x y) (s (list y)))
                        (:instance member-descending-subseqs-ending-with (s (longest (descending-subseqs-ending-with x l))))
			(:instance descendingp-append (s1 (longest (descending-subseqs-ending-with x l))) (s2 (list y)))
			(:instance member-descending-subseqs-ending-with (s (append (longest (descending-subseqs-ending-with x l))
			                                                           (list y)))
								        (x y))
			(:instance longest-longest (l (descending-subseqs-ending-with y l))
			                           (s (append (longest (descending-subseqs-ending-with x l)) (list y))))))))

;; Consequently, max-lens is an injection:

(local-defthmd index-1-1
  (implies (and (dlistp l) (member-equal x l) (member-equal y l) (not (equal x y)))
           (not (equal (index x l) (index y l)))))

(local-defthmd member-rat-list
  (implies (and (rat-listp l) (member-equal x l))
           (rationalp x)))
                        
(defthmd max-lens-1-1
  (implies (and (rat-listp l) (dlistp l) (member-equal x l) (member-equal y l) (not (equal x y)))
           (not (equal (max-lens x l) (max-lens y l))))
  :hints (("Goal" :in-theory (enable max-lens)
                  :use (member-rat-list index-1-1 diff-longest-ascending diff-longest-descending
		        (:instance member-rat-list (x y))
		        (:instance diff-longest-ascending (x y) (y x))
		        (:instance diff-longest-descending (x y) (y x))))))

(local-defthmd longest-ascending-range
   (implies (and (rat-listp l) (dlistp l) (member-equal x l))
            (let ((m (len (longest (ascending-subseqs-ending-with x l)))))
	      (and (posp m) (<= m (len (longest-ascending-subseq l))))))
  :hints (("Goal" :in-theory (enable longest-ascending-subseq)
                  :use ((:instance member-ascending-subseqs-ending-with (s (longest (ascending-subseqs-ending-with x l))))
                        (:instance member-ascending-subseqs (s (longest (ascending-subseqs-ending-with x l))))
                        (:instance longest-longest (l (ascending-subseqs l)) (s (longest (ascending-subseqs-ending-with x l))))
                        (:instance longest-longest (l (ascending-subseqs-ending-with x l)) (s (list x)))
			(:instance member-ascending-subseqs-ending-with (s (list x)))))))

(local-defthmd longest-descending-range
   (implies (and (rat-listp l) (dlistp l) (member-equal x l))
            (let ((m (len (longest (descending-subseqs-ending-with x l)))))
	      (and (posp m) (<= m (len (longest-descending-subseq l))))))
  :hints (("Goal" :in-theory (enable longest-descending-subseq)
                  :use ((:instance member-descending-subseqs-ending-with (s (longest (descending-subseqs-ending-with x l))))
                        (:instance member-descending-subseqs (s (longest (descending-subseqs-ending-with x l))))
                        (:instance longest-longest (l (descending-subseqs l)) (s (longest (descending-subseqs-ending-with x l))))
                        (:instance longest-longest (l (descending-subseqs-ending-with x l)) (s (list x)))
			(:instance member-descending-subseqs-ending-with (s (list x)))))))

;; A list of the first n positive integers:

(defun positives (n)
  (if (zp n)
      ()
    (cons n (positives (1- n)))))

(defthm len-positives
  (implies (natp n)
           (equal (len (positives n))
	          n)))

(defthm member-positives
  (implies (natp n)
           (iff (member-equal x (positives n))
	        (and (posp x) (<= x n)))))

;; For naturals a and b, if (len (longest-ascending-subseq l)) <= a and
;; (len (longest-descending-subseq l)) <= b, then for every meber x of l, (max-lens x l)
;; belongs to the Cartesian product of (positives a) and (positives b):

(defthmd max-lens-cart-prod
   (implies (and (rat-listp l) (dlistp l) (member-equal x l)
                 (natp a) (<= (len (longest-ascending-subseq l)) a)
                 (natp b) (<= (len (longest-descending-subseq l)) b))
            (member-equal (max-lens x l)
	                  (cart-prod (positives a) (positives b))))
  :hints (("Goal" :in-theory (enable max-lens)
                  :use (longest-ascending-range longest-descending-range
		        (:instance member-cart-prod (l (positives a)) (r (positives b)) (x (max-lens x l)))))))

;; It follows that (len l) is at most the order of that Cartesian product:

(local-defun max-lens-image (p l)
  (if (consp p)
      (cons (max-lens (car p) l) (max-lens-image (cdr p) l))
    ()))

(local-defun max-lens-preimage (x p l)
  (if (consp p)
      (if (equal (max-lens (car p) l) x)
          (car p)
	(max-lens-preimage x (cdr p) l))
    ()))

(local-defthmd preimage-image
  (implies (member-equal x (max-lens-image p l))
           (and (member-equal (max-lens-preimage x p l) p)
	        (equal (max-lens (max-lens-preimage x p l) l) x))))

(local-defthmd dlistp-image
  (implies (and (rat-listp l) (dlistp l)
                (natp a) (<= (len (longest-ascending-subseq l)) a)
                (natp b) (<= (len (longest-descending-subseq l)) b)
		(dlistp p) (sublistp p l))
           (and (dlistp (max-lens-image p l))
	        (sublistp (max-lens-image p l) (cart-prod (positives a) (positives b)))))		
  :hints (("Subgoal *1/1" :use ((:instance preimage-image (x (max-lens (car p) l)) (p (cdr p)))
                                (:instance max-lens-cart-prod (x (car p)))  
	                        (:instance max-lens-1-1 (x (car p)) (y (max-lens-preimage (max-lens (car p) l) (cdr p) l)))))))

(local-defthm len-max-lens-image
  (equal (len (max-lens-image p l))
         (len p)))

(defthmd len-l-bound
  (implies (and (rat-listp l) (dlistp l)
                (natp a) (<= (len (longest-ascending-subseq l)) a)
                (natp b) (<= (len (longest-descending-subseq l)) b))
           (<= (len l) (* a b)))
  :hints (("Goal" :use ((:instance dlistp-image (p l))
                        (:instance sublistp-<=-len (l (max-lens-image l l)) (m (cart-prod (positives a) (positives b))))))))

;; The desired result follows:
  
(defthm asc-desc-subseqp
  (implies (and (rat-listp l)
		(dlistp l)
		(posp a)
		(posp b)
		(> (len l) (* (1- a) (1- b))))
	   (let ((asc (longest-ascending-subseq l))
		 (desc (longest-descending-subseq l)))
	     (and (subseqp asc l)
		  (ascendingp asc)
		  (subseqp desc l)
		  (descendingp desc)
		  (or (>= (len asc) a)
		      (>= (len desc) b)))))
  :hints (("Goal" :use (longest-ascending-longest longest-descending-longest
                        (:instance len-l-bound (a (1- a)) (b (1- b)))))))
