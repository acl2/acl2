(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(include-book "divisors")
(local (include-book "support/subseq"))

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

(defthmd member-ascending-subseqs
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (ascending-subseqs l))
	        (and  (subseqp s l) (ascendingp s)))))

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

(defthmd member-descending-subseqs
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (descending-subseqs l))
	        (and  (subseqp s l) (descendingp s)))))

;; The longest member of a lists of lists:

(defun longest (l)
  (if (and (consp l) (consp (cdr l)))
      (let ((m (longest (cdr l))))
	(if (< (len (car l)) (len m))
	    m
	  (car l)))
    (car l)))

;; The longest ascending subsequence of l:

(defund longest-ascending-subseq (l)
  (longest (ascending-subseqs l)))

(defthmd longest-ascending-longest
  (implies (and (rat-listp l) (dlistp l))
           (let ((m (longest-ascending-subseq l)))
	     (and (subseqp m l)
	          (ascendingp m)
		  (implies (and (subseqp s l) (ascendingp s))
		           (>= (len m) (len s)))))))

;; The longest descending subsequence of l:

(defund longest-descending-subseq (l)
  (longest (descending-subseqs l)))

(defthmd longest-descending-longest
  (implies (and (rat-listp l) (dlistp l))
           (let ((m (longest-descending-subseq l)))
	     (and (subseqp m l)
	          (descendingp m)
		  (implies (and (subseqp s l) (descendingp s))
		           (>= (len m) (len s)))))))

;; Given a mewmber x of l, construct a list of all ascending subsequences of l
;; that end with x:

(defun lists-ending-with (x l)
  (if (consp l)
      (if (and (consp (car l)) (equal (car (last (car l))) x))
	  (cons (car l) (lists-ending-with x (cdr l)))
        (lists-ending-with x (cdr l)))
    ()))

(defund ascending-subseqs-ending-with (x l)
  (lists-ending-with x (ascending-subseqs l)))

(defthmd member-ascending-subseqs-ending-with
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (ascending-subseqs-ending-with x l))
	        (and (consp s)
	             (equal (car (last s)) x)
		     (subseqp s l)
		     (ascendingp s)))))

;; A list of all descending subsequences of l that end with x:

(defund descending-subseqs-ending-with (x l)
  (lists-ending-with x (descending-subseqs l)))

(defthmd member-descending-subseqs-ending-with
  (implies (and (rat-listp l) (dlistp l))
           (iff (member-equal s (descending-subseqs-ending-with x l))
	        (and (consp s)
	             (equal (car (last s)) x)
		     (subseqp s l)
		     (descendingp s)))))

;; An function from the members of l to pairs of positive integers:

(defund max-lens (x l)
  (cons (len (longest (ascending-subseqs-ending-with x l)))
        (len (longest (descending-subseqs-ending-with x l)))))

;; Suppose x and y are distinct members of l with (index x l) < (index y l).  If x < y,
;; then the longest ascending subseqhence of l that ends with x may be extended to y.
;; Thus, there is a longer ascending subseqence of l that ends with y:

(defthmd diff-longest-ascending
  (implies (and (rat-listp l) (dlistp l) (member-equal x l) (member-equal y l)
                (< (index x l) (index y l)) (< x y))
	   (< (len (longest (ascending-subseqs-ending-with x l)))
	      (len (longest (ascending-subseqs-ending-with y l))))))

;; On the other hand, if x > y, then the longest descending subseqhence of l that ends
;; with x may be extended to y. Thus, there is a longer descending subseqhence of l that
;; ends with y:

(defthmd diff-longest-descending
  (implies (and (rat-listp l) (dlistp l) (member-equal x l) (member-equal y l)
                (< (index x l) (index y l)) (> x y))
	   (< (len (longest (descending-subseqs-ending-with x l)))
	      (len (longest (descending-subseqs-ending-with y l))))))

;; Consequently, max-lens is an injection:

(defthmd max-lens-1-1
  (implies (and (rat-listp l) (dlistp l)
		(member-equal x l) (member-equal y l) (not (equal x y)))
           (not (equal (max-lens x l) (max-lens y l)))))

;; A list of the first n positive integers:

(defun positives (n)
  (if (zp n)
      ()
    (cons n (positives (1- n)))))

;; For naturals a and b, if (len (longest-ascending-subseq l)) <= a and
;; (len (longest-descending-subseq l)) <= b, then for every meber x of l, (max-lens x l)
;; belongs to the Cartesian product of (positives a) and (positives b):

(defthmd max-lens-cart-prod
   (implies (and (rat-listp l) (dlistp l) (member-equal x l)
                 (natp a) (<= (len (longest-ascending-subseq l)) a)
                 (natp b) (<= (len (longest-descending-subseq l)) b))
            (member-equal (max-lens x l)
	                  (cart-prod (positives a) (positives b)))))

;; It follows that (len l) is at most the length of that Cartesian product:

(defthmd len-l-bound
  (implies (and (rat-listp l) (dlistp l)
                (natp a) (<= (len (longest-ascending-subseq l)) a)
                (natp b) (<= (len (longest-descending-subseq l)) b))
           (<= (len l) (* a b))))

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
		      (>= (len desc) b))))))
