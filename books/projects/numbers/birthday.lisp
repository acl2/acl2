(in-package "DM")

(include-book "projects/groups/groups" :dir :system)
(local (include-book "support/birthday"))

;; Given a random set of k people, what is the probability that at least one pair of them
;; have the same birthday?  What is the smallest k for which this probability is greater
;; than 1/2?

;; An assignment of birthdays to k people will be represented as a list of dates of length
;; k, where a date is represented as a natural number less than 365.  (As a simplification
;; of the problem, we shall pretend that there are no leap years.)  We shall construct a
;; list of all possible birthday assignments and a sublist consisting of the assignmemts
;; that contain duplicates.  The desired probability is the ratio of the lengths of these
;; lists.

;; Given a list m of distinct members (a "dlist") and a sublist l that is also a dlist,
;; (lists l m k) is a list of all sublists of m of length k that begin with a member of l:

(defun lists (l m k)
  (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
  (if (posp k)
      (if (consp l)
          (append (conses (car l) (lists m m (1- k)))
                  (lists (cdr l) m k))
  	())
    (list ())))

(defthmd member-lists
  (implies (and (sublistp l m) (natp k))
           (iff (member-equal x (lists l m k))
		(and (true-listp x)
		     (or (zp k) (member-equal (car x) l))
		     (sublistp x m)
		     (equal (len x) k)))))

;; (lists l m k) is itself a dlist:

(defthm dlistp-lists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k))
	   (dlistp (lists l m k))))

;; We shall represent the nth day of the year by n, where 0 <= n < 365.  (To simplify
;; matters, we pretend that there are no leap years.)  If l = m = (ninit 365), the list of
;; the first 365 naturals, then we have a dlist of all possible birthday assignments to a
;; group of k people:

(defund birthday-lists (k)
  (lists (ninit 365) (ninit 365) k))

;; The following 2 lemmas ensure that the number of possible birthday assignments is the
;; length of this list

(defthmd member-birthday-lists
  (implies (natp k)
	   (iff (member-equal x (birthday-lists k))
		(and (true-listp x)
		     (sublistp x (ninit 365))
		     (equal (len x) k)))))

(defthmd dlistp-birthday-lists
  (implies (natp k)
	   (dlistp (birthday-lists k))))

;; We are interested birthday assignments that contain duplicates.  First we define the
;; sublist of (lists l m k) consisting of all dlists:

(defun dlists (l m k)
  (declare (xargs :measure (list (acl2-count k) (acl2-count l))))
  (if (posp k)
      (if (consp l)
          (append (conses (car l)
                          (dlists (remove1-equal (car l) m)
	                          (remove1-equal (car l) m)
		                  (1- k)))
		  (dlists (cdr l) m k))
  	())
    (list ())))
      
(defthm member-dlists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (iff (member-equal x (dlists l m k))
		(and (true-listp x)
		     (or (zp k) (member-equal (car x) l))
		     (sublistp x m)
		     (equal (len x) k)
		     (dlistp x)))))

(defthmd member-dlists-lists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (iff (member-equal x (dlists l m k))
		(and (member-equal x (lists l m k))
		     (dlistp x)))))

;; (dlists l m k) is also a dlist and a sublist of (lists l m k):

(defthm dlistp-dlists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k))
	   (dlistp (dlists l m k))))

(defthmd sublistp-dlists
  (implies (and (sublistp l m) (dlistp l) (dlistp m) (natp k))
           (sublistp (dlists l m k) (lists l m k))))

;; (dlists (ninit 365) (ninit 365) k) is a  dlist of all birthday assigments that are
;; dlists:

(defthmd sublistp-birthday-lists
  (implies (natp k)
	   (sublistp (dlists (ninit 365) (ninit 365) k)
		     (birthday-lists k))))

(defthm dlistp-dlists-ninit
  (implies (natp k)
           (dlistp (dlists (ninit 365) (ninit 365) k))))

;; We are interested in the complement of that list:

(defund birthday-lists-with-repetition (k)
  (set-difference-equal (birthday-lists k)
			(dlists (ninit 365) (ninit 365) k)))

;; The following 2 lemmas ensure that the number of possible birthday assignments with
;; repetitions is the length of this list:

(defthmd member-birthday-lists-with-repetition
  (implies (natp k)
	   (iff (member-equal x (birthday-lists-with-repetition k))
		(and (member-equal x (birthday-lists k))
		     (not (dlistp x))))))

(defthm dlistp-birthday-lists-with-repetition
  (implies (natp k)
	   (dlistp (birthday-lists-with-repetition k))))

;; The length of (birthday-lists k):

(defthm len-lists
  (implies (and (sublistp l m) (natp k))
	   (equal (len (lists l m k))
		  (if (posp k)
		      (* (len l)
		         (expt (len m) (1- k)))
		    1))))

(defthm len-birthday-lists
  (implies (natp k)
	   (equal (len (birthday-lists k))
		  (expt 365 k))))

;; The length of (birthday-lists-with-repetition k):

(defthm len-dlists
  (implies (and (dlistp l) (dlistp m) (sublistp l m) (natp k) (<= k (len m)))
	   (equal (len (dlists l m k))
		  (if (posp k)
		      (* (len l)
		         (/ (fact (1- (len m)))
			    (fact (- (len m) k))))
		    1))))

(defthm len-dlists-ninit-365
  (implies (and (natp k) (<= k 365))
	   (equal (len (dlists (ninit 365) (ninit 365) k))
	          (/ (fact 365) (fact (- 365 k))))))

(defthm len-birthday-lists-with-repetition
  (implies (and (natp k) (<= k 365))
	   (equal (len (birthday-lists-with-repetition k))
		  (- (expt 365 k)
                     (/ (fact 365) (fact (- 365 k)))))))

;; The probability that a random assignment of birthdays to a group of k people
;; contains a repetition:

(defun probability-of-repetition (k)
  (/ (len (birthday-lists-with-repetition k))
     (len (birthday-lists k))))

(defthm probability-of-repetition-value
  (implies (and (natp k) (<= k 365))
	   (equal (probability-of-repetition k)
                  (- 1 (/ (fact 365) (* (fact (- 365 k)) (expt 365 k)))))))

(in-theory (disable (probability-of-repetition)))

;; The least value of k for which this probability exceeds 1/2 is 23:

(defthm probability-of-repetition-22
  (< (probability-of-repetition 22) 1/2))

(defthm probability-of-repetition-23
  (> (probability-of-repetition 23) 1/2))
