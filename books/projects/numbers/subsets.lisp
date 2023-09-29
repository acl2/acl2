(in-package "DM")

(include-book "projects/groups/lists" :dir :system)
(local (include-book "support/subsets"))

;; Let l be a dlist of length n.  Then l represents a set of order n, the elements
;; of which are the members of l. In this context, 2 dlists are considered equivalent
;; if they represent the same set, i.e., one is a permutation of the other.

;; We have 2 objectives (1) Compute the number of subsets of (the set represented
;; by) l as a function of n; (2) compute the number of such subsets of a given order
;; k <= n.  For this purpose, we define the following list of sublists of l:

(defun subsets (l)
  (if (consp l)
      (let ((s (subsets (cdr l))))
	(append s (conses (car l) s)))
    (list ())))

;; NIL is a subset of every l:

(defthm member-nil-subsets
  (member-equal () (subsets l)))

;; Every subset is a true list:

(defthm true-listp-subset
  (implies (member-equal s (subsets l))
           (true-listp s)))

;; A true list is a subset of itself:

(defthm subset-self
  (implies (true-listp l)
	   (member-equal l (subsets l))))

;; Every member of (subsets l) is a sublist of l and a dlist:

(defthm sublistp-subset
  (implies (and (dlistp l) (member-equal s (subsets l)))
	   (sublistp s l)))

(defthmd len-subset-bound
  (implies (member-equal s (subsets l))
	   (<= (len s) (len l))))

(defthm dlistp-subset
  (implies (and (dlistp l) (member-equal s (subsets l)))
	   (dlistp s)))

;; (subsets l) is itself a dlist:

(defthm dlistp-subsets
  (implies (dlistp l) (dlistp (subsets l))))

;; If s is a subset of l, then the subsets of s are the subsets of l that are
;; sublists of s:

(defthmd subset-subset
  (implies (and (dlistp l)
                (member-equal s (subsets l)))
	   (iff (member-equal x (subsets s))
	        (and (member-equal x (subsets l))
		     (sublistp x s)))))

;; No member of l is a permutation of another, i.e., distinct members of l
;; represent distinct subsets:

(defthm perm-subset-equal
  (implies (and (dlistp l)
                (member-equal s (subsets l))
		(member-equal r (subsets l))
		(permutationp r s))
	   (equal r s))
  :rule-classes ())

;; Moreover, every dlist sublist of l is a permutation of some member of
;; (subsets l):

(defun find-subset (s l)
  (if (consp l)
      (if (member-equal (car l) s)
	  (cons (car l) (find-subset (remove1-equal (car l) s) (cdr l)))
	(find-subset s (cdr l)))
    ()))

(defthm member-find-subset-subsets
  (member-equal (find-subset s l)
                (subsets l)))

(defthm perm-find-subset
  (implies (and (dlistp l) (dlistp s) (sublistp s l))
	   (permutationp (find-subset s l) s)))

;; Thus, the number of subsets of l is (len (subsets l), which is easily
;; shown to be 2^n:

(defthm len-subsets
  (equal (len (subsets l))
         (expt 2 (len l))))

;; Next we consider the sublist of (subsets l) consisting of all lists
;; of a given length k:

(defun subsets-of-order-aux (k l)
  (if (consp l)
      (if (equal (len (car l)) k)
	  (cons (car l) (subsets-of-order-aux k (cdr l)))
	(subsets-of-order-aux k (cdr l)))
    ()))

(defund subsets-of-order (k l)
  (subsets-of-order-aux k (subsets l)))

(defthm member-subsets-of-order
  (iff (member-equal x (subsets-of-order k l))
       (and (member-equal x (subsets l))
            (equal (len x) k))))

(defthmd no-subsets-of-order>len
  (implies (and (natp k) (> k (len l)))
           (equal (subsets-of-order k l)
	          ())))

;; (subsets-of-order k l) is a dlist, and therefore, (len (subsets-of-order k l))
;; is the number of subsets of l of order k:

(defthm dlistp-subsets-of-order
  (implies (dlistp l)
	   (dlistp (subsets-of-order k l))))

;; We shall prove by induction that (len (subsets-of-order k l)) is the binomial
;; coefficient, (choose n k) = n!/(k!(n - k)!):

(defund choose (n k)
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (/ (fact n)
	 (* (fact k) (fact (- n k))))
    0))

;; To this end, we split (subsets-of-order k l) into 2 sublists, consisting of the
;; subsets that contain (car l) and the subsets that do not contain (car l):

(defthmd member-conses-subsets-of-order
  (implies (and (dlistp l) (consp l) (posp k))
           (iff (member-equal x (conses (car l) (subsets-of-order (1- k) (cdr l))))
	        (and (member-equal x (subsets-of-order k l))
		     (member-equal (car l) x)))))

(defthmd member-cdr-subsets-of-order
  (implies (and (dlistp l) (natp k))
           (iff (member-equal x (subsets-of-order k (cdr l)))
	        (and (member-equal x (subsets-of-order k l))
		     (not (member-equal (car l) x))))))

(defthmd member-subsets-of-order-append
  (implies (and (dlistp l) (consp l) (posp k))
           (iff (member-equal x (subsets-of-order k l))
	        (member-equal x (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		                        (subsets-of-order k (cdr l)))))))

;; Appending these 2 sublists yields a dlist:

(defthmd dlistp-append-subsets-of-order
  (implies (and (dlistp l) (consp l) (posp k))
           (dlistp (append (conses (car l) (subsets-of-order (1- k) (cdr l)))
		           (subsets-of-order k (cdr l))))))

;; It foll0ows that (len (subsets-of-order k l)) is the sum of the lengths of
;; these sublists:

(defthmd subsets-of-order-plus
  (implies (and (dlistp l) (consp l) (posp k))
           (equal (len (subsets-of-order k l))
	          (+ (len (subsets-of-order (1- k) (cdr l)))
		     (len (subsets-of-order k (cdr l)))))))

;; Since NIL is the only subset of l of order 0, the case k = 0 is trivial:

(defthm subsets-of-order-0
  (implies (dlistp l)
           (equal (len (subsets-of-order 0 l)) 1)))

;; Similarly, since l is the only subset of l of length n, the case k = n is trivial:

(defthm subsets-of-order-len
  (implies (dlistp l)
           (equal (len (subsets-of-order (len l) l)) 1)))

;; In the remaining case, the formula follows from subsets-of-order-plus by induction:

;;   (len (subsets-of-order k l)) = (n-1)!/((k-1)!(n-k)!) + (n-1)!/(k!(n-k+1)!)
;;                                = (k(n-1)!)/(k!(n-k)!) + ((n-k)(n- 1)!)/(k!(n-k)!)
;;                                = ((k+n-k)(n-1)!)/(k!(n-k)!)
;;                                = n!/(k!(n-k)!)
;;                                = (choose (len l) k).

(defthm len-subsets-of-order
  (implies (and (dlistp l) (natp k))
	   (equal (len (subsets-of-order k l))
		  (choose (len l) k))))
