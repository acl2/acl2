(in-package "PROOF")

(defun subset (x y)
  (declare (xargs :guard (true-listp y)))
  (if (consp x)
      (if (member-equal (car x) y)
          (subset (cdr x) y)
        nil)
    (equal x nil)))

(defun get-subsets (x list)
  (declare (xargs :guard (true-listp x)))
  (if (consp list)
      (if (subset (car list) x)
          (cons (car list) (get-subsets x (cdr list)))
        (get-subsets x (cdr list)))
    nil))

(defun get-non-subsets (x list)
  (declare (xargs :guard (true-listp x)))
  (if (consp list)
      (if (subset (car list) x)
          (get-non-subsets x (cdr list))
        (cons (car list) (get-non-subsets x (cdr list))))
    nil))

(defun difference (x y)
  (declare (xargs :guard (true-listp y)))
  (if (consp x)
      (if (member-equal (car x) y)
          (difference (cdr x) y)
        (cons (car x) (difference (cdr x) y)))
    nil))

(defun subset-list (list x)
  (declare (xargs :guard (true-listp x)))
  (if (consp list)
      (and (subset (car list) x)
           (subset-list (cdr list) x))
    t))

(defun intersect (x y)
  (declare (xargs :guard (true-listp y)))
  (if (consp x)
      (if (member-equal (car x) y)
          (cons (car x) (intersect (cdr x) y))
        (intersect (cdr x) y))
    nil))

(defun no-conflicts (x list)
  (declare (xargs :guard (and (true-listp x)
                              (true-list-listp list))))
  (if (consp list)
      (if (intersect x (car list))
          (and
           (subset (car list) x)
           (no-conflicts x (cdr list)))
        (no-conflicts x (cdr list)))
    t))

(defun no-conflicts-list (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (consp x)
      (and (no-conflicts (car x) (cdr x))
           (no-conflicts-list (cdr x)))
    t))

(defun disjoint-list (x list)
  (declare (xargs :guard (true-list-listp list)))
  (if (consp list)
      (and (not (intersect x (car list)))
           (disjoint-list x (cdr list)))
    t))

(defun disjoint-lists (l1 l2)
  (declare (xargs :guard (true-list-listp l2)))
  (if (consp l1)
      (and (disjoint-list (car l1) l2)
           (disjoint-lists (cdr l1) l2))
    t))


;; no-dups

;; this membership needed for one below
(defthm member-1-member-append
  (implies (member-equal x y)
           (member-equal x (append y z))))

(defthm no-dups-append-gives-1
  (implies (and (true-listp x)
                (no-duplicatesp-equal (append x y)))
           (no-duplicatesp-equal x)))

(defthm no-dups-append-gives-2
  (implies (no-duplicatesp-equal (append x y))
           (no-duplicatesp-equal y)))

;member append subset
(defthm member-difference-member
  (implies (member-equal x (difference p q))
           (member-equal x p)))

(defthm member-equal-difference
  (implies (and (member-equal y top)
                (not (member-equal y x)))
           (member-equal y (difference top x))))

(defthm subset-append-gives-1
  (implies (and (true-listp x)
                (subset (append x y) z))
           (subset x z)))

(defthm subset-append-gives-2
  (implies (subset (append x y) z)
           (subset y z)))

(defthm member-2-member-append
  (implies (member-equal x y)
           (member-equal x (append z y))))

(defthm subset-gives-append-1
  (implies (subset x y)
           (subset x (append y z))))

(defthm subset-gives-append-2
  (implies (subset x y)
           (subset x (append z y))))

(defthm subset-same-members
  (implies (and (member-equal x y)
                (subset y z))
           (member-equal x z)))

(defthm not-member-subset
  (implies (and (not (member-equal x y))
                (subset z y))
           (not (member-equal x z))))

(defthm not-members-not-member-append
  (implies (and (not (member-equal x y))
                (not (member-equal x z)))
           (not (member-equal x (append y z)))))

(defthm subset-transitive
  (implies (and (subset x y)
                (subset y z))
           (subset x z)))

(defthm subset-cons
  (implies (subset x y)
           (subset x (cons z y))))

(defthm subset-x-x
  (implies (true-listp x)
           (subset x x)))

(defthm subset-cons-identity
  (implies (true-listp x)
           (subset x (cons y x))))

(defthm subset-gives-true-listp
  (implies (subset x y)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm subset-subset-gives-subset-append
  (implies (and (subset x z)
                (subset y z))
           (subset (append x y) z)))


;; subset-list
(defthm subset-list-gives-append-1
  (implies (subset-list x y)
           (subset-list x (append y z))))

(defthm subset-list-gives-append-2
  (implies (subset-list x y)
           (subset-list x (append z y))))

(defthm subset-list-cons
  (implies (subset-list x y)
           (subset-list x (cons z y))))

(defthm subset-list-get-subsets-x
  (subset-list (get-subsets x y)
               x))

(defthm subset-list-get-subsets-equal
  (implies (and (subset-list list x)
                (true-listp list))
           (equal (get-subsets x list)
                  list)))

(defthm subset-list-nil-non-subsets
  (implies (subset-list x y)
           (not (get-non-subsets y x))))

(defthm non-subsets-nil
  (implies (subset-list x y)
           (subset-list (get-non-subsets nil x)
                        y)))

(defthm subset-list-subset
  (implies (and (subset-list list y)
                (subset y z))
           (subset-list list z)))


;; difference
(defthm subset-difference-nil
  (implies (subset x y)
           (not (difference x y))))

(defthm difference-x-x
  (implies (true-listp x)
           (not (difference x x))))

(defthm difference-nil
  (implies (true-listp x)
           (equal (difference x nil)
                  x)))

(defthm subset-subset-difference
  (implies (subset x z)
           (subset (difference x y) z)))

(defthm subset-append-difference
  (implies (and (subset x y)
                (true-listp y))
           (subset (append x (difference y x))
                   y)))

(defthm difference-not-member
  (implies (not (member-equal x y))
           (equal (difference y (cons x z))
                  (difference y z))))

;; intersect
(defthm no-duplicates-append-disjoint
  (implies (no-duplicatesp-equal (append x y))
           (not (intersect x y)))
  :rule-classes :forward-chaining)

(defthm member-equal-intersect
  (implies (and (member-equal x y)
                (member-equal x z))
           (intersect y z)))

(defthm intersect-subset
  (implies (and (subset x y)
                (subset u v)
                (intersect x u))
           (intersect y v)))

(defthm intersect-cons
  (implies (intersect y x)
           (intersect y (cons z x))))

(defthm intersect-commutative
  (implies (intersect x y)
           (intersect y x)))

(defthm intersect-subset-intersect
  (implies (and (intersect x z)
                (subset x y))
           (intersect y z)))

(defthm disjoint-nil
  (not (intersect x nil)))

(defthm not-intersect-commutative
  (implies (not (intersect a b))
           (not (intersect b a))))

(defthm not-intersect-subsets
  (implies (and (not (intersect u v))
                (subset x u)
                (subset y v))
           (not (intersect x y))))

;; no-conflicts(-list)
(defthm disjoint-no-conflicts
  (implies (disjoint-list x y)
           (no-conflicts x y)))

(defthm no-conflicts-disjoint-append
  (implies (and (no-conflicts x y)
                (disjoint-list x z))
           (no-conflicts x (append y z))))

(defthm subset-list-no-conflicts
  (implies (subset-list list x)
           (no-conflicts x list)))

(defthm subset-list-no-conflicts-append
  (implies (and (subset-list x z)
                (subset-list y z))
           (no-conflicts z (append x y))))

(defthm no-conflicts-list-disjoint-append
  (implies (and (no-conflicts-list x)
                (no-conflicts-list y)
                (disjoint-lists x y))
           (no-conflicts-list (append x y))))

(defthm no-conflicts-get-subsets
  (implies (no-conflicts x y)
           (no-conflicts x (get-subsets z y))))

(defthm no-conflicts-list-subsets
  (implies (no-conflicts-list x)
           (no-conflicts-list (get-subsets y x))))

(defthm no-conflicts-get-non-subsets
  (implies (no-conflicts x y)
           (no-conflicts x (get-non-subsets z y))))

(defthm no-conflicts-list-non-subsets
  (implies (no-conflicts-list x)
           (no-conflicts-list (get-non-subsets y x))))


;; disjoint-lists
(defthm subset-not-disjoint-intersect
  (implies (and (not (disjoint-list x u))
                (subset x y)
                (subset-list u v))
           (intersect y v)))

(defthm subset-disjoint-disjoint
  (implies (and (subset-list x y)
                (subset-list u v)
                (not (intersect y v)))
           (disjoint-lists x u)))

(in-theory (disable disjoint-lists))

;; playing together

(defthm subset-difference
  (implies (and (subset y top)
                (not (intersect y x))
                )
           (subset y (difference top x)))
  :hints (("Goal" :induct (subset y top))))

(defthm get-non-subsets-difference
  (implies (and (subset x top)
                (subset-list y top)
                (no-conflicts x y))
           (subset-list (get-non-subsets x y)
                        (difference top x))))

(defthm not-intersect-tops-not-subset
  (implies (and (not (intersect x v))
                (consp y)
                (subset y v)
                (subset z x))
           (not (subset y z))))

(defthm subset-list-through-get-subsets
  (implies (subset-list x y)
           (subset-list (get-subsets z x) y)))

(defthm subset-list-through-get-non-subsets
  (implies (subset-list x y)
           (subset-list (get-non-subsets z x) y)))

(defthm true-list-listp-through-get-subsets
  (implies (true-list-listp x)
           (true-list-listp (get-subsets y x))))

(defthm true-list-listp-through-get-non-subsets
  (implies (true-list-listp x)
           (true-list-listp (get-non-subsets y x))))