(in-package "DM")

(include-book "projects/groups/lists" :dir :system) ;for properties of permutations
(include-book "projects/groups/cauchy" :dir :system) ;for properties of powers of 2
(local (include-book "support/partitions"))

;; A partition of a positive integer n is a list of positive integers the sum of which is n:

(defun sum-list (l)
  (if (consp l)
      (+ (car l) (sum-list (cdr l)))
    0))

(defun pos-listp (l)
  (if (consp l)
      (and (posp (car l))
           (pos-listp (cdr l)))
    (null l)))

(defun partp (l n)
  (and (pos-listp l)
       (equal (sum-list l) n)))

;; We consider two sets of partitions.  The first consists of those that contain only odd
;; integers.  We shall refer to these as "odd partitions":

(defun odd-listp (l)
  (if (consp l)
      (and (oddp (car l))
	   (odd-listp (cdr l)))
    (null l)))

(defun odd-partp (l n)
  (and (partp l n)
       (odd-listp l)))

;; The second set consists of those partitions with pairwise distinct members.  We shall
;; refer to these as "distinct partitions":

(defun dis-partp (l n)
  (and (partp l n)
       (dlistp l)))

;; Two partitions are considered equivalent if one is a permutation of the other.  Note
;; that each of the sets of partitions of interest consists of a union of equivalence classes:

(defthmd odd-partp-inv
  (implies (and (posp n) (pos-listp l) (pos-listp m) (odd-partp l n) (permutationp m l))
           (odd-partp m n)))

(defthmd dis-partp-inv
  (implies (and (posp n) (pos-listp l) (pos-listp m) (dis-partp l n) (permutationp m l))
           (dis-partp m n)))

;; Euler's partition theorem states that the number of equivalence classes of odd
;; partitions of n is equal to the number of equivalence classes of distinct partitions of n.

;; How do we count these equivalence classes?  For each of the two sets of partitions, we 
;; shall construct a dlist of partitions belonging to the set and prove the following two
;; properties:
;;   (1) No member of the list is a permutation of another;
;;   (2) Every element of the set is a permutation of some member of the list.
;; We may then conclude that the number of equivalence classes is the length of the list,
;; and we need only show that the two lists have the same length.

;; For the odd partitions, our list will consist of all odd sorted partitions of n, i.e.,
;; those that are monotonically increasing with respect to the usual ordering of the
;; integers.  For distinct partitions, we shall do something similar, but it will be 
;; convenient to use a different ordering of the positive integers.  We must show that (1) 
;; and (2) hold for each list.  In fact, we shall prove a general result:  Let t<= be a total 
;; order on the positive integers and let pred be a predicate that characterizes a set of 
;; lists of positive integers and is invariant under permutation.  If predl is a dlist 
;; consisting of all lists of positive integers that satisfy pred and are sorted with respect 
;; to t<=, then predl satisfies (1) and (2).

;; For this we use encapsulation and functional instantiation.


;;------------------------------------------------------------------------------------------------

;; The function t<= is constrained to be a total order of the positive integers:

(encapsulate (((t<= * *) => *))
  (local (defun t<= (x y) (<= x y)))
  (defthmd t<=-reflex
    (implies (posp x) (t<= x x)))
  (defthmd t<=-assoc
    (implies (and (posp x) (posp y) (posp z) (t<= x y) (t<= y z))
             (t<= x z)))
  (defthm t<=-antisym
    (implies (and (posp x) (posp y) (t<= x y) (t<= y x))
             (equal x y))
    :rule-classes ())
  (defthmd t<=-total
    (implies (and (posp x) (posp y))
             (or (t<= x y) (t<= y x)))))

;; A list is sorted with respect to t<= if it satisfies the following:

(defun tsortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (t<= (car l) (cadr l))
           (tsortedp (cdr l)))
    t))

;; A second encapsulation constrains pred and predl:

(encapsulate (((pred *) => *) ((predl) => *))

  ;; pred is a predicate on lists of positives that is invariant under permutation:
  
  (local (defun pred (l) (declare (ignore l)) ()))
  
  (defthmd pred-inv
    (implies (and (pos-listp l) (pos-listp m) (pred l) (permutationp m l))
             (pred m)))

  ;; (predl) is a dlist consisting of all ordered lists that satisfy pred:
  
  (local (defun predl () ()))
  
  (defthmd dlistp-predl
    (dlistp (predl)))
    
  (defthmd member-predl
    (iff (member-equal l (predl))
         (and (pos-listp l) (tsortedp l) (pred l)))))

;; We derive results corresponding to (1) and (2) above.

;; (1) No member of (predl) is a permutation of another:

(defthm predl-perm-equal
  (implies (and (member-equal l (predl))
                (member-equal m (predl))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

;; (2) Every list that satisfies pred is a permutation of some member of (predl):

;; This requires a witness function.  We use the following sorting function, which produces
;; a sorted permutation of its argument.  It is based on an auxiliary function that finds
;; the least member of a list:

(defun tleast-aux (x l)
  (if (consp l)
      (if (t<= x (car l))
          (tleast-aux x (cdr l))
	(tleast-aux (car l) (cdr l)))
    x))

(defun tleast (l)
  (tleast-aux (car l) (cdr l)))

(defun tsort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (tleast l) l))
      (cons (tleast l)
            (tsort (remove1 (tleast l) l)))
    ()))

(defthmd perm-tsort
  (implies (pos-listp l)
           (permutationp (tsort l) l)))

(defthmd tsortedp-tsort
  (implies (pos-listp l)
           (and (pos-listp (tsort l))
                (tsortedp (tsort l)))))

(defthmd perm-predl
  (implies (and (pos-listp l) (pred l))
           (and (member-equal (tsort l) (predl))
	        (permutationp (tsort l) l))))

;; We shall functionally instantiate predl-perm-equal and perm-predl twice, first for the 
;; odd partitions of n and then the distinct partitions of n.


;;------------------------------------------------------------------------------------------------

;; For the odd partitions, we substitute the standard order <= for t<=.  The predicate and the
;; sorting function corresponding to tsorted and tsort are defined as follows:

(defun sortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (<= (car l) (cadr l))
	   (sortedp (cdr l)))
    t))

(defun least-aux (x l)
  (if (consp l)
      (if (<= x (car l))
          (least-aux x (cdr l))
	(least-aux (car l) (cdr l)))
    x))

(defun least (l)
  (least-aux (car l) (cdr l)))

(defun sort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (least l) l))
      (cons (least l)
            (sort (remove1 (least l) l)))
    ()))

;; The predicate corresponding to pred is (lambda (l) (odd-partp l n)).  Corresponding to the list
;; predl,  we construct a list of all sorted odd partitions of n.  This is based on an auxiliary
;; function that constructs, for given odd k, a list of all sorted odd partitions l of n with
;; (car l) >= k:

(defun odd-parts-aux (n k)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (posp n) (posp k))
      (if (= k n)
	  (list (list n))
	(if (< k n)
            (append (conses k (odd-parts-aux (- n k) k))
                    (odd-parts-aux n (+ k 2)))
	  ()))
    ()))

(defun odd-parts (n) (odd-parts-aux n 1))

;; Since <= is known to be a total order and we have already proved odd-partp-inv, we need only
;; derive the properties corresponding to dlistp-predl and member-predl:

(defthmd dlistp-odd-parts
  (implies (posp n)
	   (dlistp (odd-parts n))))

(defthmd member-odd-parts
  (implies (posp n)
           (iff (member-equal l (odd-parts n))
	        (and (odd-partp l n)
		     (sortedp l)))))

;; In particular, (odd-parts n) is a list of odd partitions:

(defthmd odd-partp-odd-parts
  (implies (and (posp n) (member-equal l (odd-parts n)))
	   (odd-partp l n)))


;; The desired results follow by functional instantiation of predl-perm-equal and perm-predl:

(defthm odd-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (odd-parts n))
		(member-equal m (odd-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

(defthmd perm-odd-parts
  (implies (and (posp n)
                (odd-partp l n))
	   (and (member-equal (sort l) (odd-parts n))
	        (permutationp (sort l) l))))
		

;;------------------------------------------------------------------------------------------------

;; To address the distinct partitions of n, We define a total order d<= on the positive integers
;; based on the representation of an integer as the product of a power of 2 and an odd integer:

(defun pow2 (n)
  (if (and (posp n) (evenp n))
      (* 2 (pow2 (/ n 2)))
    1))

(defun oddf (n)
  (/ n (pow2 n)))

(defthm pow2-power-2
  (implies (posp n)
           (powerp (pow2 n) 2)))

(defthmd oddp-oddf
  (implies (posp n)
           (oddp (oddf n))))

(defun d<= (x y)
  (or (< (oddf x) (oddf y))
      (and (= (oddf x) (oddf y))
	   (<= x y))))

;; d<= is trivially verified to be a total order on the positive integers:

(defthmd d<=-reflex
  (implies (posp x) (d<= x x)))

(defthmd d<=-assoc
  (implies (and (posp x) (posp y) (posp z) (d<= x y) (d<= y z))
           (d<= x z)))

(defthm d<=-antisym
  (implies (and (posp x) (posp y) (d<= x y) (d<= y x))
           (equal x y))
  :rule-classes ())

(defthmd d<=-total
  (implies (and (posp x) (posp y))
           (or (d<= x y) (d<= y x))))

;; A recognizer of sorted lists with respect to d<=:

(defun dsortedp (l)
  (if (and (consp l) (consp (cdr l)))
      (and (d<= (car l) (cadr l))
           (dsortedp (cdr l)))
    t))

;; The sorting function:

(defun dleast-aux (x l)
  (if (consp l)
      (if (d<= x (car l))
          (dleast-aux x (cdr l))
	(dleast-aux (car l) (cdr l)))
    x))

(defun dleast (l)
  (dleast-aux (car l) (cdr l)))

(defun dsort (l)
  (declare (xargs :measure (len l)))
  (if (and (consp l) (pos-listp l) (member-equal (dleast l) l))
      (cons (dleast l)
            (dsort (remove1 (dleast l) l)))
    ()))

;; We shall construct a dlist (dis-parts n) consisting of the distinct partitions of n that 
;; are sorted with respect to d<=, based on a function odd2dis that converts an odd partition 
;; to a distinct partition.  This function is in turn based on a decomposition of a sorted 
;; odd partition l as the appending of 2 lists: (1) the initial segment of l consisting of 
;; all occurrences of (car l) and (2) the remaining tail:

(defun copies (k n)
  (if (posp k)
      (cons n (copies (1- k) n))
    ()))

(defun count-init (x l)
  (if (and (consp l) (= x (car l)))
      (1+ (count-init x (cdr l)))
    0))

(defthmd odd-part-decomp
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (let* ((x (car l))
	          (cnt (count-init x l))
		  (tail (nthcdr cnt l)))
	     (and (equal (append (copies cnt x) tail) l)
	          (posp cnt)
		  (<= (* cnt x) n)
		  (odd-partp tail (- n (* cnt x)))
		  (sortedp tail)
		  (or (null tail) (> (car tail) x))))))

;; The function odd2dis also depends on the decomposition of a natural number n as a sum of
;; powers of 2:

(defun bin-decomp-aux (n k)
  (if (zp n)
      ()
    (if (evenp n)
	(bin-decomp-aux (ash n -1) (1+ k))
      (cons (ash 1 k) (bin-decomp-aux (ash n -1) (1+ k))))))

(defun bin-decomp (n)
  (bin-decomp-aux n 0))

;; (bin-decomp n) is the unique sorted dlist of powers of 2 that sums to n:

(defun pow2-listp (l)
  (if (consp l)
      (and (powerp (car l) 2)
           (pow2-listp (cdr l)))
    (null l)))

(defthmd bin-decomp-properties
  (implies (posp n)
           (let ((l (bin-decomp n)))
	     (and (pow2-listp l)
	          (sortedp l)
		  (dlistp l)
		  (equal (sum-list l) n)))))
                          
(defthmd bin-decomp-unique
  (implies (and (consp l)
                (pow2-listp l)
	        (sortedp l)
	        (dlistp l))
           (equal (bin-decomp (sum-list l))
	          l)))

;; (odd2dis l) is computed by appending 2 lists.  The first is computed by multiplying (car l)
;; by each component of the binary decomposition of the number of occurrences of (car l):

(defun prods (l n)
  (if (consp l)
      (cons (* (car l) n) (prods (cdr l) n))
    ()))

(defund odd2dis-prefix (l)
  (prods (bin-decomp (count-init (car l) l)) (car l)))

;; The second is computed by applying odd2dis recursively to the rest of l:

(defun odd2dis (l)
  (if (consp l)
      (append (odd2dis-prefix l)
              (odd2dis (nthcdr (count-init (car l) l) l)))
    ()))

;; We construct a list of distinct partitions by applying odd2dis to each member of
;; (odd-parts n):

(defun odd2dis-list (l)
  (if (consp l)
      (cons (odd2dis (car l)) (odd2dis-list (cdr l)))
    ()))

(defun dis-parts (n)
  (odd2dis-list (odd-parts n)))

;; Clearly, (odd-parts n) and (dis-parts n) have the same length:

(defthm len-odd2dis-list
  (equal (len (odd2dis-list l))
	 (len l)))

(defthm len-dis-parts
  (equal (len (dis-parts n))
	 (len (odd-parts n))))


;;------------------------------------------------------------------------------------------------

;; We must derive the properties of (dis-parts n) corresponding to dlistp-predl and member-predl,
;; i.e., we must show that (dis-parts n) is a dlist consisting of all ordered distinct partitions
;; of n.  To this end, we define the inverse of odd2dis, which converts a sorted distinct partition
;; of n to a sorted odd partition of n.  This is based on a decomposition of a sorted distinct
;; partition as the appending of 2 lists: (1) the initial segment consisting of all members with
;; minimal odd component and (2) the remaining tail:

(defun oddf-init-aux (x l)
  (if (consp l)
      (if (= (oddf (car l)) x)
          (cons (car l) (oddf-init-aux x (cdr l)))
	())
    ()))

(defun oddf-init (l)
  (oddf-init-aux (oddf (car l)) l))		 

(defun all-oddf-p (x l)
  (if (consp l)
      (and (= (oddf (car l)) x)
           (all-oddf-p x (cdr l)))
    t))

(defthmd dis-part-decomp
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (let* ((x (oddf (car l)))
	          (prefix (oddf-init l))
		  (sum (sum-list prefix))
		  (tail (nthcdr (len prefix) l)))
	     (and (equal (append prefix tail) l)
	          (consp prefix)
	          (dis-partp prefix sum)
	          (all-oddf-p x prefix)
	          (<= sum n)
		  (dis-partp tail (- n (sum-list prefix)))
		  (dsortedp tail)
		  (or (null tail) (> (oddf (car tail)) x))))))

;; (dis2odd l) is computed by appending 2 lists.  The first is computed by converting
;; (oddf-init l) to a list of copies of (oddf (car l)):

(defund dis2odd-prefix (l)
  (copies (/ (sum-list (oddf-init l)) (oddf (car l)))
	  (oddf (car l))))

;; The second is computed by applying dis2odd recursively to the rest of l:

(defun dis2odd (l)
  (if (consp l)
      (append (dis2odd-prefix l)
	      (dis2odd (nthcdr (len (oddf-init l)) l)))
    ()))


;;------------------------------------------------------------------------------------------------

;; Let l be a sorted odd partition of n and let m = (odd2dis m).  We shall show that m is a sorted
;; distinct partition of n and (dis2odd m) = l.  This will imply that (dis-parts n) is a dlist.

;; The following properties of (odd2dis-prefix l) follow from bin-decomp-properties and
;; odd-part-decomp:

(defthmd pos-listp-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (and (consp (odd2dis-prefix l))
                (pos-listp (odd2dis-prefix l)))))

(defthmd all-oddf-p-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (all-oddf-p (car l) (odd2dis-prefix l))))

(defthmd sortedp-dlist-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (and (sortedp (odd2dis-prefix l))
	        (dlistp (odd2dis-prefix l)))))

(defthmd sum-list-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (sum-list (odd2dis-prefix l))
	          (* (car l) (count-init (car l) l)))))

(defthmd oddf-car-prefix
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (oddf (car (odd2dis-prefix l)))
	          (car l))))

;; An immediate consequence of the last result:

(defthmd oddf-car-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
           (equal (oddf (car (odd2dis l)))
	          (car l))))

;; Let tail = (nthcdr (count-init (car l) l) l).  We shall prove by induction that

;;     m = (append (odd2dis-prefix l) (odd2dis tail))

;; is a sorted distinct partition of n.  Thus, we may assume that (odd2dis tail) is a sorted
;; distince partition of (sum-list tail).  According to odd-part-decomp and sum-list-prefix,

;;     (sum-list m) = (sum-list (odd2dis-prefix l)) + (sum-list tail) = n,

;; and it follows from pos-listp-prefix that m is a partition of n.  By oddf-car-odd2dis
;; and odd-part-decomp, (oddf (car (odd2dis tail))) = (car tail) > (car l), and it follows
;; from all-oddf-p-prefix and sortedp-dlist-prefix that m is a sorted dlist.  This completes
;; the induction:

(defthmd dis-partp-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (and (dis-partp (odd2dis l) n)
	        (dsortedp (odd2dis l)))))

;; We use the same induction scheme to prove that (dis2odd m) = l.  It follows from observations
;; above that (oddf-init m) = (odd2dis-prefix l).  By bin-decomp-properties,

;;     (sum-list (odd-init m)) = (sum-list (odd2dis-prefix l))
;;                             = (* (car l) (count-init (car l)))
;;                             = (* (oddf (car m)) (count-init (car l))).

;; Consequently, (dis2odd m) = (copies (count-init (car l)) (car l)).  The result follows from
;; the inductive hypothesis that (dis2odd (odd2dis tail)) = tail:

(defthmd dis2odd-odd2dis
  (implies (and (posp n) (odd-partp l n) (sortedp l))
	   (equal (dis2odd (odd2dis l))
	          l)))

;; It follows that odd2dis is an injection on (odd-parts n), which implies that (dis-parts n)
;; is a dlist:

(defthm odd2dis-1-1
  (implies (and (posp n) (odd-partp l n) (sortedp l) (odd-partp m n) (sortedp m)
                (equal (odd2dis l) (odd2dis m)))
           (equal l m))
  :rule-classes ())

(defthmd dlistp-dis-parts
  (implies (posp n)
	   (dlistp (dis-parts n))))
	   

;;------------------------------------------------------------------------------------------------

;; Now let l be a sorted distinct partition of n and let m = (dis2odd l).  We shall show that m is 
;; a sorted odd partition of n and (odd2dis m) = l.  This implies that l belongs to (dis-parts n).

;; We define the list of pow2 components of a list of positive integers:

(defun pow2-list (l)
  (if (consp l)
      (cons (pow2 (car l)) (pow2-list (cdr l)))
    ()))

;; (oddf-init l) may be expressed as follows:

(defthmd prods-pow2-list-oddf-init
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (prods (pow2-list (oddf-init l)) (oddf (car l)))
	          (oddf-init l))))

;; (dis2odd-prefix l) may be characterized as follows:

(defthmd dis2odd-prefix-rewrite
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (dis2odd-prefix l)
	          (copies (sum-list (pow2-list (oddf-init l))) (oddf (car l))))))

;; This yields the following expression for (car (dis2odd l)):
  
(defthmd car-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (car (dis2odd l)) (oddf (car l)))))

;; To prove that m is a sorted odd partition, let tail = (nthcdr (len (oddf-init l)) l).  Then
;; (dis2odd l) = (append (dis2odd-prefix l) (dis2odd tail)).  By dis-part-decomp, tail is a sorted
;; distinct partition of n - (sum-list (oddf-init l)).  By induction, we may assume that
;; (dis2odd tail) is a sorted odd partition n - (sum-list (oddf-init l)).  Clearly, (dis2odd-prefix l)
;; is a sorted odd partition of

;;     (* (oddf (car l)) (sum-list (pow2-list (oddf-init l)))) = (sum-list (oddf-init l)).

;; It follows that m is an odd partition of n.  By car-dis2odd,

;;     (car (dis2odd tail)) = (oddf (car tail)) > (oddf (car l)).

;; This implies that m is sorted and completes the proof:

(defthmd odd-partp-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (and (odd-partp (dis2odd l) n)
	        (sortedp (dis2odd l)))))

;; To prove that (odd2dis m) = l, first note that since (pow2-list (oddf-init l) is a sorted
;; dlist of powers of 2, the following is a consequence of bin-decomp-unique:

(defthmd bin-decomp-count-init-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (bin-decomp (sum-list (pow2-list (oddf-init l))))
	          (pow2-list (oddf-init l)))))

;; The following is a consequence of dis2odd-prefix-rewrite:

(defthmd count-init-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (count-init (car (dis2odd l)) (dis2odd l))
	          (sum-list (pow2-list (oddf-init l))))))

;; Combine count-init-dis2odd with prods-pow2-list-oddf-init:

(defthmd odd2dis-prefix-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (odd2dis-prefix (dis2odd l))
	          (oddf-init l))))

;; The desired follows by induction:

(defthmd odd2dis-dis2odd
  (implies (and (posp n) (dis-partp l n) (dsortedp l))
           (equal (odd2dis (dis2odd l))
	          l)))

;; Combine odd2dis-dis2odd and dis-partp-odd2dis:

(defthmd member-dis-parts
  (implies (posp n)
           (iff (member-equal l (dis-parts n))
	        (and (dis-partp l n)
		     (dsortedp l)))))

;; In particular, (dis-parts n) is a list of distinct partitions:

(defthmd dis-partp-dis-parts
  (implies (and (posp n) (member-equal l (dis-parts n)))
	   (dis-partp l n)))


;;------------------------------------------------------------------------------------------------

;; The desired results follow from dlistp-dis-parts and member-dis-parts by functional instantiation
;; of predl-perm-equal and perm-predl:

(defthm dis-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (dis-parts n))
		(member-equal m (dis-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

(defthmd perm-dis-parts
  (implies (and (posp n)
                (dis-partp l n))
	   (and (member-equal (dsort l) (dis-parts n))
	        (permutationp (dsort l) l))))


;;------------------------------------------------------------------------------------------------

;; In summary, we have established the following properties of the list (odd-parts n).

;; (odd-parts n) is a dlist of odd partitions of n:

(defthmd dlistp-odd-parts
  (implies (posp n)
	   (dlistp (odd-parts n))))

(defthmd odd-partp-odd-parts
  (implies (and (posp n) (member-equal l (odd-parts n)))
	   (odd-partp l n)))

;; No 2 members of (odd-parts n) are equivalent:

(defthm odd-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (odd-parts n))
		(member-equal m (odd-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

;; Every odd partition of n is equivalent to e member of (odd-parts n):

(defthmd perm-odd-parts
  (implies (and (posp n)
                (odd-partp l n))
	   (and (member-equal (sort l) (odd-parts n))
	        (permutationp (sort l) l))))

;; Thus, the number of equivalence classes of odd partitions of n is (len (odd-parts n)).

;; We have also established the analogous properties of the list (dis-parts n):

(defthmd dlistp-dis-parts
  (implies (posp n)
	   (dlistp (dis-parts n))))

(defthmd dis-partp-dis-parts
  (implies (and (posp n) (member-equal l (dis-parts n)))
	   (dis-partp l n)))

(defthm dis-parts-perm-equal
  (implies (and (posp n)
                (member-equal l (dis-parts n))
		(member-equal m (dis-parts n))
		(permutationp l m))
	   (equal l m))
  :rule-classes ())

(defthmd perm-dis-parts
  (implies (and (posp n)
                (dis-partp l n))
	   (and (member-equal (dsort l) (dis-parts n))
	        (permutationp (dsort l) l))))

;; Thus, the number of equivalence classes of distinct partitions of n is (len (dis-parts n)).

;; We have also proved that these 2 lists have the same length:

(defthm len-dis-parts
  (equal (len (dis-parts n))
	 (len (odd-parts n))))

;; Thus, the number of equivalence classes of odd partitions of n is equal to the number
;; of equivalence classes of distinct partitions of n.
