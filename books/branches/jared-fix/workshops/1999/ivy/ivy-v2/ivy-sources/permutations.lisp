(in-package "ACL2")

;; This book is about permutations and related stuff.
;;
;; It includes some congruence theorems for permutation.

(include-book "sets")

;;-------------------------
;; Function remove1 (x lst) removes the first occurrence of x.

; Matt K.:  Function remove1 was defined here, but has been removed for ACL2
; Version_2.9.4 in favor of new ACL2 function remove1-equal.

(defthm not-member-remove1-equal
  (implies (not (member-equal x a))
	   (not (member-equal x (remove1-equal y a)))))

(defthm member-remove1-equal
  (implies (and (member-equal x a)
                (not (equal x y)))
           (member-equal x (remove1-equal y a))))

(defthm remove1-equal-commute
  (equal (remove1-equal x (remove1-equal y a))
         (remove1-equal y (remove1-equal x a))))

(defthm subset-not-member-remove1-equal
  (implies (and (subsetp-equal a b)
		(not (member-equal x a)))
	   (subsetp-equal a (remove1-equal x b))))

(defthm member-not-equal-remove1-equal
  (implies (and (member-equal a1 b)
		(not (equal x a1)))
	   (member-equal a1 (remove1-equal x b))))

(defthm subset-not-member-subset-remove
  (implies (and (subsetp-equal a b)
		(not (member-equal x a)))
	   (subsetp-equal a (remove1-equal x b))))

;;----------------
;; perm (permutation)

(defun perm (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))))
  (cond ((atom a) (atom b))
        ((member-equal (car a) b) (perm (cdr a) (remove1-equal (car a) b)))
        (t nil)))

(defthm perm-reflexive
  (perm x x))

(defthm perm-cons
  (implies (member-equal a x)
           (equal (perm x (cons a y))
                  (perm (remove1-equal a x) y)))
  :hints (("Goal" :induct (perm x y))))

(defthm perm-symmetric
  (implies (perm x y) (perm y x)))

(defthm perm-member
  (implies (and (perm x y)
                (member-equal a x))
           (member-equal a y)))

(defthm perm-remove1-equal
  (implies (perm x y)
           (perm (remove1-equal a x) (remove1-equal a y))))

(defthm perm-transitive
  (implies (and (perm x y) (perm y z))
           (perm x z)))

(defequiv perm)

(defcong perm perm (append a b) 2)

(defthm append-cons
  (perm (append a (cons b c)) (cons b (append a c))))

(defthm append-commutes
  (perm (append a b) (append b a)))

(defcong perm perm (append x y) 1
  :hints (("Goal" :induct (append y x))))

(defcong perm iff (member-equal a b) 2)

;;--------------

(defthm member-perm-not
  (implies (and (perm a b)
                (not (member-equal x a)))
           (not (member-equal x b)))
  :rule-classes nil)

(defthm setp-remove
  (implies (and (setp (remove1-equal x b))
                (not (member-equal x (remove1-equal x b))))
           (setp b))
  :rule-classes nil)

(defthm perm-setp-setp
  (implies (and (perm a b)
                (setp a))
           (setp b))
  :hints (("Subgoal *1/5'4'"
           :use ((:instance setp-remove (x a1) (b b))
                 (:instance member-perm-not (a a2) (b (remove1-equal a1 b)) (x a1)))
           )))

(defthm perm-not-setp-not-setp
  (implies (and (perm a b) (not (setp a)))
           (not (setp b))))

(defcong perm iff (setp a) 1)

;;--------------- subbag
;; A bag is a multiset, that is, a collection with possible duplicates.
;; Everything can be considered a bag, and the subbag relation
;; considers the number of occurrences of the members.

(defun subbag (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))))
  (if (atom x)
      t
      (and (member-equal (car x) y)
           (subbag (cdr x) (remove1-equal (car x) y)))))

(defthm subbag-cons
  (subbag l (cons x l)))

(defthm subbag-append-left
  (implies (subbag a b)
           (subbag (append c a) (append c b))))

(defthm subbag-remove1-equal
  (implies (subbag a (remove1-equal x b))
           (subbag a b)))

(defthm remove1-equal-append-commute
  (implies (member-equal x a)
           (equal (remove1-equal x (append a b))
                  (append (remove1-equal x a) b))))

(defthm remove1-equal-append-commute-2
  (implies (and (not (member-equal x a))
                (member-equal x b))
           (equal (remove1-equal x (append a b))
                  (append a (remove1-equal x b)))))

(defthm member-equal-append
  (implies (and (not (member-equal x a))
                (member-equal x (append a b)))
           (member-equal x b)))

(defthm subbag-append-right
  (implies (subbag a b)
           (subbag (append a c) (append b c))))

(defthm first-of-subbag-is-member
  (implies (subbag (cons x l) a)
           (member-equal x a)))

(defthm subbag-remove1-equal-member-cons
  (implies (and (subbag a2 (remove1-equal a1 b))
                (member-equal a1 b))
           (subbag (cons a1 a2) b)))

(defthm subbag-flip-start
  (implies (subbag (list* x y a) b)
           (subbag (list* y x a) b))
  :hints (("Goal"
           :expand ((subbag (list* x y a) b)
                    (subbag (list* y x a) b)))
          ("Subgoal 2"
           :expand ((subbag (cons y a) (remove1-equal x b))))
          ("Subgoal 1"
           :expand ((subbag (cons y a) (remove1-equal x b))
                    (subbag (cons x a) (remove1-equal y b))))
          )
  :rule-classes nil)

(defthm subbag-member-cons
  (implies (and (subbag a b)
                (member-equal x b)
                (not (member-equal x a)))
           (subbag (cons x a) b))
  :hints (("Goal"
           :do-not generalize)
          ("Subgoal *1/1''"
           :expand ((subbag (cons x a) b)))
          ("Subgoal *1/6'4'"
           :use ((:instance subbag-flip-start (x a1) (y x) (a a2) (b b))))))

(defthm subbag-not-member
  (implies (and (subbag vs q)
                (not (member-equal c q)))
           (not (member-equal c vs))))

(defthm subbag-trans-helper
  (implies (and (member-equal x a)
                (member-equal x b)
                (subbag a b))
           (subbag (remove1-equal x a) (remove1-equal x b))))

(defthm subbag-trans
  (implies (and (subbag a b)
                (subbag b c))
           (subbag a c))
  :hints (("Goal"
           :do-not generalize))
  :rule-classes nil)

(defthm subbag-reflexive
  (subbag x x))

;;--------------

(defthm member-len-remove1-equal
  (implies (member-equal x b)
           (equal (len (remove1-equal x b)) (- (len b) 1))))

(defthm subbag-of-same-len-is-perm
  (implies (and (subbag a b)
                (equal (len a) (len b)))
           (perm a b))
  :rule-classes nil)

(defthm perm-implies-subbag
  (implies (perm a b)
           (subbag a b))
  :rule-classes nil)

(defthm subbag-equal-len
  (implies (and (subbag a b)
                (equal (len a) (len b)))
           (subbag b a))
  :hints (("Goal"
           :use ((:instance subbag-of-same-len-is-perm)
                 (:instance perm-implies-subbag (a b) (b a))))))

;;-------------------------
;; This section builds up to some congruences about permutation and disjoint.

(defthm not-member-not-disjiont-not-disjoint-remove1-equal
  (implies (and (not (member-equal x b))
		(not (disjoint a b)))
	   (not (disjoint (remove1-equal x a) b))))

(defthm perm-disjoint-disjoint
  (implies (and (perm a a1)
		(disjoint a b))
	   (disjoint a1 b))
  :hints (("goal"
	   :induct (perm a a1))))

(defthm disjoint-remove1-equal
  (implies (disjoint a b)
	   (disjoint (remove1-equal x a) b)))

(defthm perm-not-disjoint-not-disjoint
  (implies (and (perm a a1)
		(not (disjoint a b)))
	   (not (disjoint a1 b)))
  :hints (("goal"
	   :induct (perm a a1))))

(defcong perm equal (disjoint a b) 1)

(defcong perm equal (disjoint a b) 2)
