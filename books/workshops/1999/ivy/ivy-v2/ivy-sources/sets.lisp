(in-package "ACL2")

;; This book is about set operations on lists.  The definitions
;; of member-equal, subsetp-equal, and union-equal are built into
;; ACL2.  Here we define remove-equal, set-equal, setp, and disjoint.
;;
;; The lemmas are just what arose in practice, without much thought
;; on designing good sets of rewrite rules for these operations.
;;
;; This includes some congruence theorems for set-equal.

;;-----------------------
;; First, some properties of subsetp-equal, member-equal, union-equal.

;;-----------------------
;; subsetp-equal

(defthm subset-cons
  (implies (subsetp-equal a b)
	   (subsetp-equal a (cons x b))))

(defthm subset-reflexive
  (subsetp-equal x x))

(defthm subsetp-equal-transitive
  (implies (and (subsetp-equal x y)
                (subsetp-equal y z))
           (subsetp-equal x z)))

(defthm subset-member-subset-cons
  (implies (and (subsetp-equal a b)
		(member-equal x b))
	   (subsetp-equal (cons x a) b)))

(defthm not-member-subset
  (implies (and (not (member-equal a y))
                (subsetp-equal x y))
           (not (member-equal a x))))

(defun subset-skolem (a b)  ;; first member of a not in b
  (declare (xargs :guard (and (true-listp a) (true-listp b))))
  (cond ((atom a) nil)
        ((not (member-equal (car a) b)) (car a))
        (t (subset-skolem (cdr a) b))))

(defthm subset-skolem-lemma
  (implies (implies (member-equal (subset-skolem a b) a)
                    (member-equal (subset-skolem a b) b))
           (subsetp-equal a b))
  :rule-classes nil)

;;-----------------------
;; union-equal

(defthm union-equal-preserves-true-listp
  (implies (true-listp y)
	   (true-listp (union-equal x y))))

(defthm union-nil-left
  (equal (union-equal nil x) x))

(defthm union-nil-right
  (implies (true-listp x)
	   (equal (union-equal x nil) x)))

(defthm member-union-or
  (implies (or (member-equal x a)
	       (member-equal x b))
	   (member-equal x (union-equal a b))))

(defthm not-member-union-equal
  (implies (and (not (member-equal x a))
		(not (member-equal x b)))
	   (not (member-equal x (union-equal a b)))))

(defthm union-not-nil-if-either-argument-is-a-cons
  (implies (or (consp x) (consp y))
	   (union-equal x y)))

(defthm subset-union-2
  (implies (subsetp-equal a b)
	   (equal (union-equal a b) b)))

(defthm union-equal-idempotent
  (equal (union-equal x x) x))

(defthm subset-union-3
  (implies (and (subsetp-equal a c)
		(subsetp-equal b c))
	   (subsetp-equal (union-equal a b) c)))

(defthm subset-union
  (implies (and (subsetp-equal a b)
		(subsetp-equal c d))
	   (subsetp-equal (union-equal a c)
			  (union-equal b d))))

(defthm subset-union-4
  (implies (subsetp-equal a b)
	   (subsetp-equal a (union-equal c b))))

(defthm subset-union-left-2
  (implies (subsetp-equal a b)
           (subsetp-equal a (union-equal b c))))

(defthm subset-union-left-not
  (implies (not (subsetp-equal a c))
	   (not (subsetp-equal (union-equal a b) c))))

(defthm subset-union-right-not
  (implies (not (subsetp-equal b c))
	   (not (subsetp-equal (union-equal a b) c))))

;;-----------------------
;; Function remove-equal (x lst) removes all occurrences of x.

; Matt K.: Commented out after v2-9-3 because remove-equal is now defined in
; axioms.lisp, very slightly differently.
;(defun remove-equal (x l)
;  (declare (xargs :guard (true-listp l)))
;  (cond ((atom l) l)
;	((equal x (car l)) (remove-equal x (cdr l)))
;	(t (cons (car l) (remove-equal x (cdr l))))))

(defthm removed-element-is-not-member
  (not (member-equal x (remove-equal x a))))

(defthm subset-equal-remove
  (implies (subsetp-equal a b)
	   (subsetp-equal (remove-equal x a)
			  (remove-equal x b)))
  :hints (("Goal" :do-not generalize)))

(defthm not-member-not-member-remove
  (implies (not (member-equal y a))
	   (not (member-equal y (remove-equal x a)))))

(defthm remove-distributes-over-union
  (equal (remove-equal x (union-equal a b))
	 (union-equal (remove-equal x a) (remove-equal x b)))
  :hints (("Goal"
	   :do-not generalize)))

(defthm subset-cons-remove
  (subsetp-equal a (cons x (remove-equal x a))))

(defthm subset-remove-append-one
  (subsetp-equal a (append (remove-equal x a) (list x))))

(defthm not-equal-member-remove
  (implies (and (not (equal x v1))
                (member-equal x a))
           (member-equal x (remove-equal v1 a))))

(defthm remove-equal-commutative
  (equal (remove-equal x (remove-equal y a))
         (remove-equal y (remove-equal x a))))

(defthm remove-equal-idempotent
  (equal (remove-equal x (remove-equal x a))
         (remove-equal x a)))

(defthm true-listp-remove-equal
  (implies (true-listp l)
	   (true-listp (remove-equal x l))))

;;-----------------------
;; set-equal (nonrecursive)  (I now think recursive might be better.)

(defun set-equal (a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b))))
  (and (subsetp-equal a b)
       (subsetp-equal b a)))

(defthm set-equal-reflexive
  (set-equal x x))

(defequiv set-equal)

(defcong set-equal set-equal (union-equal a b) 1)

(defcong set-equal set-equal (union-equal a b) 2)

(defcong set-equal set-equal (remove-equal x a) 2)

(defcong set-equal set-equal (cons x a) 2)

(defthm member-append-left
  (implies (member-equal x a)
           (member-equal x (append a b))))

(defthm member-append-right
  (implies (member-equal x b)
           (member-equal x (append a b))))

(defthm subset-append-left
  (implies (subsetp-equal a b)
           (subsetp-equal (append a c) (append b c))))

(defcong set-equal set-equal (append a b) 1)

(defcong set-equal set-equal (append a b) 2)

(defthm set-equal-member-equal-cons
  (implies (member-equal x a)
	   (set-equal (cons x a) a)))

(defthm set-equal-nil
  (not (set-equal nil (cons x a))))

;;---------------------------------------------------------------
;; A collection of rewrite rules for canonicalizing union-equal expressions.

(defthm union-equal-commute-subset
  (subsetp-equal (union-equal a b) (union-equal b a)))

(defthm union-equal-commutative
  (set-equal (union-equal a b) (union-equal b a)))

(defthm union-equal-associative
  (equal (union-equal (union-equal a b) c)
	 (union-equal a (union-equal b c))))

(defthm union-equal-assoc-commute-subset
  (subsetp-equal (union-equal a (union-equal b c))
		 (union-equal b (union-equal a c))))

(defthm union-equal-assoc-commute
  (set-equal (union-equal a (union-equal b c))
	     (union-equal b (union-equal a c))))

(defthm union-equal-idempotent-general
  (equal (union-equal x (union-equal x y))
	 (union-equal x y))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance union-equal-associative
                            (a x) (b x) (c y))))))

;;-----------------  append and subsetp-equal

(defthm subset-append-1
  (implies (not (subsetp-equal a b))
           (not (subsetp-equal (append a c) b))))

(defthm subset-append-2
  (implies (not (subsetp-equal a b))
           (not (subsetp-equal (append c a) b))))

(defthm member-append-cons
  (member-equal x (append a (cons x b))))

(defthm subset-append-cons
  (subsetp-equal (append b c) (append b (cons x c))))

(defthm subset-append-cons-2
  (implies (subsetp-equal a (append b c))
           (subsetp-equal a (append b (cons x c))))
  :hints (("Goal"
           :use ((:instance subsetp-equal-transitive
                            (x a) (y (append b c))
                            (z (append b (cons x c))))))))

(defthm subset-append-cons-3
  (implies (subsetp-equal (append a b) c)
           (subsetp-equal (append a (cons x b)) (cons x c))))

;;--------------------------
;; The setp predicate checks that a list has no duplicates.

(defun setp (a)
  (declare (xargs :guard (true-listp a)))
  (cond ((atom a) t)
        ((member-equal (car a) (cdr a)) nil)
        (t (setp (cdr a)))))

(defthm union-equal-setp
  (implies (and (setp a)
                (setp b))
           (setp (union-equal a b))))

(defthm remove-equal-setp
  (implies (setp a)
           (setp (remove-equal x a))))

(defthm setp-append-1
  (implies (not (setp b))
           (not (setp (append a b)))))

(defthm setp-append-2
  (implies (not (setp a))
           (not (setp (append a b))))
  :hints (("Goal"
           :do-not generalize)))

;;--------------------------------
;; set-difference-equal

(defthm not-member-set-difference
  (implies (not (member-equal x c))
           (not (member-equal x (set-difference-equal c d)))))

(defthm set-difference-equal-nil
  (implies (true-listp a)
           (equal (set-difference-equal a nil) a)))


;;--------------------------------
;; misc

(defthm consp-has-member-equal
  (implies (consp x)
           (member-equal (car x) x))
  :rule-classes nil)

;;--------------------------------
;; This section is a bunch of special-purpose lemmas about subset and union.

(defthm subset-union-6
  (subsetp-equal a (union-equal c (union-equal a d))))

(defthm special-set-lemma-2
  (implies (subsetp-equal b (union-equal c (union-equal a d)))
           (subsetp-equal (union-equal a b)
                          (union-equal c (union-equal a d)))))

(defthm subset-union-7
  (subsetp-equal a (union-equal c (cons x (union-equal a d)))))

(defthm special-set-lemma-3
  (implies (subsetp-equal b (union-equal c (cons x (union-equal a d))))
           (subsetp-equal (union-equal a b)
                          (union-equal c (cons x (union-equal a d))))))

(defthm subset-union-8
  (implies (subsetp-equal a (union-equal b m))
	   (subsetp-equal a (union-equal b (union-equal d m)))))

(defthm subset-union-9
  (implies (subsetp-equal c (union-equal d m))
	   (subsetp-equal c (union-equal b (union-equal d m)))))

(defthm special-set-lemma-4
  (implies (and (subsetp-equal a (union-equal b m))
                (subsetp-equal c (union-equal d m)))
           (subsetp-equal (union-equal a c)
                          (union-equal b (union-equal d m)))))

(defthm special-set-lemma-6
  (implies (and (subsetp-equal fs (union-equal fl ft))
                (subsetp-equal fl s)
                (subsetp-equal ft s))
           (subsetp-equal fs s))
  :rule-classes nil)

;;-----------------
;; Disjoint lists.

(defun disjoint (a b)
  (declare (xargs :guard (and (true-listp a) (true-listp b))))
  (cond ((atom a) t)
	((member-equal (car a) b) nil)
	(t (disjoint (cdr a) b))))

(defthm disjoint-nil-right
  (disjoint a nil))

(defthm disjoint-append-union-1
  (implies (not (disjoint a b))
	   (not (disjoint (append d a) (union-equal c b)))))

(defthm disjoint-append-union-2
  (implies (not (disjoint a b))
	   (not (disjoint (append a d) (union-equal b c)))))

(defthm disjoint-member-remove
  (implies (and (not (disjoint a b))
		(not (member-equal x a)))
	   (not (disjoint a (remove-equal x b)))))

(defthm disjoint-append-union-3
  (implies (not (disjoint a b))
	   (not (disjoint (append a d) (union-equal c b)))))

(defthm disjoint-append-union-4
  (implies (not (disjoint a b))
	   (not (disjoint (append d a) (union-equal b c)))))

(defthm disjoint-append-1
  (implies (not (disjoint a b))
	   (not (disjoint (append a c) b))))

(defthm disjoint-append-2
  (implies (not (disjoint a b))
	   (not (disjoint (append c a) b))))

(defthm disjoint-append-3
  (implies (not (disjoint a b))
	   (not (disjoint a (append b c)))))

(defthm disjoint-append-4
  (implies (not (disjoint a b))
	   (not (disjoint a (append c b)))))

(defthm disjoint-union-1
  (implies (not (disjoint a b))
	   (not (disjoint a (union-equal b c)))))

(defthm disjoint-union-2
  (implies (not (disjoint a b))
	   (not (disjoint a (union-equal c b)))))

;;------------------

(defun disjoint-skolem (a b)  ;; first member of a in b
  (declare (xargs :guard (and (true-listp a) (true-listp b))))
  (cond ((atom a) nil)
	((member-equal (car a) b) (car a))
	(t (disjoint-skolem (cdr a) b))))

(defthm disjoint-skolem-lemma
  (implies (implies (member-equal (disjoint-skolem a b) a)
                    (not (member-equal (disjoint-skolem a b) b)))
           (disjoint a b))
  :rule-classes nil)

