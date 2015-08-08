(in-package "ACL2")
(include-book "extra")

(defun member-gen (x y)
  (declare (xargs :guard t))
  (if (consp y)
      (if (equal x (car y))
          t
        (member-gen x (cdr y)))
    nil))

(defthm member-gen-when-not-cons
  (implies (not (consp y))
           (equal (member-gen x y)
                  nil)))

(defthm member-gen-of-consp
  (equal (member-gen x (cons first rest))
         (if (equal x first)
             t
           (member-gen x rest))))

(dis+ind member-gen)

(defun subset (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (member-gen (car x) y)
          (subset (cdr x) y)
        nil)
    t))

(defthm subset-when-not-cons
  (implies (not (consp x))
           (equal (subset x y)
                  t)))

(defthm subset-of-consp
  (equal (subset (cons first rest) y)
         (if (member-gen first y)
             (subset rest y)
           nil)))

(dis+ind subset)

(defun get-subsets (x list)
  (declare (xargs :guard t))
  (if (consp list)
      (if (subset (car list) x)
          (cons (car list) (get-subsets x (cdr list)))
        (get-subsets x (cdr list)))
    list))

(defthm get-subsets-when-not-cons
  (implies (not (consp list))
           (equal (get-subsets x list)
                  list)))

(defthm get-subsets-of-consp
  (equal (get-subsets x (cons first rest))
         (if (subset first x)
             (cons first (get-subsets x rest))
           (get-subsets x rest))))

(dis+ind get-subsets)

(defun get-non-subsets (x list)
  (declare (xargs :guard t))
  (if (consp list)
      (if (subset (car list) x)
          (get-non-subsets x (cdr list))
        (cons (car list) (get-non-subsets x (cdr list))))
    list))

(defthm get-non-subsets-when-not-cons
  (implies (not (consp list))
           (equal (get-non-subsets x list)
                  list)))

(defthm get-non-subsets-of-consp
  (equal (get-non-subsets x (cons first rest))
         (if (subset first x)
             (get-non-subsets x rest)
           (cons first (get-non-subsets x rest)))))

(dis+ind get-non-subsets)

(defun difference (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (member-gen (car x) y)
          (difference (cdr x) y)
        (cons (car x) (difference (cdr x) y)))
    x))

(defthm difference-when-not-cons
  (implies (not (consp x))
           (equal (difference x y)
                  x)))

(defthm difference-of-cons
  (equal (difference (cons first rest) y)
         (if (member-gen first y)
             (difference rest y)
           (cons first (difference rest y)))))

(dis+ind difference)

(defun subset-list (list x)
  (declare (xargs :guard t))
  (if (consp list)
      (and (subset (car list) x)
           (subset-list (cdr list) x))
    t))

(defthm subset-list-when-not-consp
  (implies (not (consp list))
           (equal (subset-list list x)
                  t)))

(defthm subset-list-of-cons
  (equal (subset-list (cons first rest) x)
         (and (subset first x)
              (subset-list rest x))))

(dis+ind subset-list)

;changed to return binary
(defun intersect (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (member-gen (car x) y)
          t;(cons (car x) (intersect (cdr x) y))
        (intersect (cdr x) y))
    nil))

(defthm intersect-when-not-consp
  (implies (not (consp x))
           (equal (intersect x y)
                  nil)))

(defthm intersect-of-consp
  (equal (intersect (cons first rest) y)
         (if (member-gen first y)
             t
           (intersect rest y))))

(dis+ind intersect)

(defun no-conflicts (x list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if bipartition x is consistent with each of those in list. ~/
;  ~/
;  Arguments:
;    (1) x - a bipartition
;    (2) list - a list of bipartitions

;  Details: Set operations are used to determine if the bipartition x does not
;           conflict with each of the bipartitions in list.  Bipartitions must
;           be list based (as opposed to bdd-based) and the underlying taxa list
;           must be preserved between x and each member of list.
;           The bipartitions are assumed to be ordered such that no bipartition
;           x following y in list exists such that y is a subset of x and x=/y.
;           See also q-no-conflicts (bdd based)."
  (declare (xargs :guard t))
  (if (consp list)
      (if (intersect x (car list))
          (and
           (subset (car list) x)
           (no-conflicts x (cdr list)))
        (no-conflicts x (cdr list)))
    t))

(defthm no-conflicts-when-not-consp
  (implies (not (consp list))
           (equal (no-conflicts x list)
                  t)))

(defthm no-conflicts-of-consp
  (equal (no-conflicts x (cons first rest))
         (if (intersect x first)
             (and (subset first x)
                  (no-conflicts x rest))
           (no-conflicts x rest))))

(dis+ind no-conflicts)

(defun no-conflicts-list (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if the list of bipartitions x is consistent. ~/
;  ~/
;  Arguments:
;    (1) list - a list of bipartitions

;  Details: Set operations are used to determine if the list of bipartitions x
;           do not conflict.  Bipartitions must be list based (as opposed to
;           bdd based), and an underlying taxa list must be preserved between
;           every pair of bipartitions in the list.
;           The bipartitions are assumed to be ordered such that no bipartition
;           x following y in list exists such that y is a subset of x and x=/y.
;           See also q-no-conflicts-list (bdd based)."
  (declare (xargs :guard t))
  (if (consp list)
      (and (no-conflicts (car list) (cdr list))
           (no-conflicts-list (cdr list)))
    t))

(defthm no-conflicts-list-when-not-consp
  (implies (not (consp x))
           (equal (no-conflicts-list x)
                  t)))

(defthm no-conflicts-list-of-consp
  (equal (no-conflicts-list (cons first rest))
         (and (no-conflicts first rest)
              (no-conflicts-list rest))))

(dis+ind no-conflicts-list)

(defun disjoint-list (x list)
  (declare (xargs :guard t))
  (if (consp list)
      (and (not (intersect x (car list)))
           (disjoint-list x (cdr list)))
    t))

(defthm disjoint-list-when-not-consp
  (implies (not (consp list))
           (equal (disjoint-list x list)
                  t)))

(defthm disjoint-list-of-consp
  (equal (disjoint-list x (cons first rest))
         (and (not (intersect x first))
              (disjoint-list x rest))))

(dis+ind disjoint-list)

(defun disjoint-lists (l1 l2)
  (declare (xargs :guard t))
  (if (consp l1)
      (and (disjoint-list (car l1) l2)
           (disjoint-lists (cdr l1) l2))
    t))

(defthm disjoint-lists-when-not-consp
  (implies (not (consp l1))
           (equal (disjoint-lists l1 l2)
                  t)))

(defthm disjoint-lists-of-consp
  (equal (disjoint-lists (cons first rest) l2)
         (and (disjoint-list first l2)
              (disjoint-lists rest l2))))

(dis+ind disjoint-lists)

(defun no-dups-gen (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (member-gen (car x) (cdr x))
          nil
        (no-dups-gen (cdr x)))
    t))

(defthm no-dups-when-not-consp
  (implies (not (consp x))
           (equal (no-dups-gen x)
                  t)))

(defthm no-dups-of-consp
  (equal (no-dups-gen (cons first rest))
         (if (member-gen first rest)
             nil
           (no-dups-gen rest))))

(dis+ind no-dups-gen)

;; this membership needed for one below
(local (defthm member-1-member-append
  (implies (member-gen x y)
           (member-gen x (append y z))))
)

(defthm no-dups-append-gives-1
  (implies (no-dups-gen (append x y))
           (no-dups-gen x)))

(defthm no-dups-append-gives-2
  (implies (no-dups-gen (append x y))
           (no-dups-gen y)))

;member append subset
(defthm member-difference-member
  (implies (member-gen x (difference p q))
           (member-gen x p)))

(defthm member-gen-difference
  (implies (and (member-gen y top)
                (not (member-gen y x)))
           (member-gen y (difference top x))))

(defthm subset-append-gives-1
  (implies (subset (append x y) z)
           (subset x z)))

(defthm subset-append-gives-2
  (implies (subset (append x y) z)
           (subset y z)))

(defthm member-2-member-append
  (implies (member-gen x y)
           (member-gen x (append z y))))

(defthm subset-gives-subset-of-append-1
  (implies (subset x y)
           (subset x (append y z))))

(defthm subset-gives-subset-of-append-2
  (implies (subset x y)
           (subset x (append z y))))

(defthm subset-same-members
  (implies (and (member-gen x y)
                (subset y z))
           (member-gen x z)))

(defthm not-member-subset
  (implies (and (not (member-gen x y))
                (subset z y))
           (not (member-gen x z))))

(defthm not-members-not-member-append
  (implies (and (not (member-gen x y))
                (not (member-gen x z)))
           (not (member-gen x (append y z)))))

(defthm subset-transitive
  (implies (and (subset x y)
                (subset y z))
           (subset x z)))

(defthm subset-cons
  (implies (subset x y)
           (subset x (cons z y))))

(defthm subset-x-x
  (subset x x))

(defthm subset-cons-identity
  (subset x (cons y x)))

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
  (implies (subset-list list x)
           (equal (get-subsets x list)
                  list)))

(defthm non-subsets-nil
  (implies (subset-list x y)
           (subset-list (get-non-subsets nil x)
                        y)))

(defthm subset-list-subset
  (implies (and (subset-list list y)
                (subset y z))
           (subset-list list z)))

(defthm subset-subset-difference
  (implies (subset x z)
           (subset (difference x y) z)))

(defthm subset-append-difference
  (implies (subset x y)
           (subset (append x (difference y x))
                   y)))

(defthm difference-not-member
  (implies (not (member-gen x y))
           (equal (difference y (cons x z))
                  (difference y z))))

;; intersect
(defthm no-duplicates-append-disjoint
  (implies (and (no-dups-gen (append x y))
                (consp x))
           (not (intersect x y)))
  :rule-classes :forward-chaining)

(defthm member-gen-intersect
  (implies (and (member-gen x y)
                (member-gen x z))
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

;; playing together

(defthm subset-difference
  (implies (and (subset y top)
                (not (intersect y x)))
           (subset y (difference top x))))

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

(defun del (a x)
  (declare (xargs :guard t))
  (cond ((atom x) x) ;was nil
        ((equal a (car x)) (cdr x))
        (t (cons (car x) (del a (cdr x))))))

(defthm del-when-not-consp
  (implies (not (consp x))
           (equal (del a x) x)))

(defthm del-of-consp
  (equal (del a (cons first rest))
         (if (equal a first)
             rest
           (cons first (del a rest)))))

(dis+ind del)

(defun del-all (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal a (car x))
          (del-all a (cdr x))
        (cons (car x) (del-all a (cdr x))))
    nil))

(defthm del-all-when-not-consp
  (implies (not (consp x))
           (equal (del-all a x)
                  nil)))

(defthm del-all-of-consp
  (equal (del-all a (cons first rest))
         (if (equal a first)
             (del-all a rest)
           (cons first (del-all a rest)))))

(dis+ind del-all)

(defun remove-dups (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x) (remove-dups (del-all (car x) (cdr x))))
    nil))

(defthm remove-dups-when-not-consp
  (implies (not (consp x))
           (equal (remove-dups x)
                  nil)))

(defthm remove-dups-of-consp
  (equal (remove-dups (cons first rest))
         (cons first (remove-dups (del-all first rest)))))

(dis+ind remove-dups)

(defun perm (x y)
  (declare (xargs :guard t))
  (cond ((atom x) (atom y)) ;was (equal x y)
        (t (and (member-gen (car x) y)
                (perm (cdr x) (del (car x) y))))))

(defthm perm-when-not-consp
  (implies (not (consp x))
           (equal (perm x y)
                  (not (consp y))))) ; was equal x y

(defthm perm-of-consp
  (equal (perm (cons first rest) y)
         (and (member-gen first y)
              (perm rest (del first y)))))

(dis+ind perm)

(local (defthm perm-reflexive
         (perm x x)))

(local
 (encapsulate
  ()

  (local
   (defthm perm-del
     (implies (member-gen a y)
              (equal (perm (del a y) x)
                     (perm y (cons a x))))
     ;; A hint is necessary.
     :hints (("Goal" :induct (perm y x)))))

  (defthm perm-symmetric
    (implies (perm x y) (perm y x)))))

; The following arises from an attempt to prove perm-implies-same-in, below.
(local (defthm member-gen-del-implies-member-gen
         (implies (member-gen x (del a y))
                  (member-gen x y))))

(local (defthm perm-implies-same-member-gen
         (implies (and (not (member-gen x1 z))
                       (member-gen x1 y))
                  (not (perm y z)))))

(local (defthm del-del
         (equal (del a (del b x))
                (del b (del a x)))))

(local (defthm member-gen-del
         (implies (not (equal a b))
                  (equal (member-gen a (del b y))
                         (member-gen a y)))))

(local (defthm perm-del-del
         (implies (and (member-gen a y)
                       (member-gen a z))
                  (equal (perm y z)
                         (perm (del a y) (del a z))))))

(local (defthm perm-transitive
         (implies (and (perm x y) (perm y z)) (perm x z))))

(defequiv perm)

(defthm member-gen-append
  (equal (member-gen a (append x y))
         (or (member-gen a x) (member-gen a y))))

(defthm del-append
  (equal (del a (append x y))
         (if (member-gen a x)
             (append (del a x) y)
           (append x (del a y)))))

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)

(defthm member-gen-len
  (implies (member-gen x y)
           (equal (+ 1 (len (del x y)))
                  (len y))))

(defcong perm equal (len x) 1)

(defthm diff-lens-not-perm
  (implies (not (equal (len x) (len y)))
           (equal (perm x y)
                  nil)))

(defcong perm perm (member-gen x y) 2)

(local
 (defthm subset-del-member-gives-subset
   (implies (member-gen x y)
            (equal (subset (del x z) y)
                   (subset z y))))
)

(defcong perm perm (subset x y) 1)

(defthm member-perm-gives-member
  (implies (and (member-gen x y)
                (perm (double-rewrite z)
                      (double-rewrite y)))
           (member-gen x z)))

(defcong perm perm (subset x y) 2)

(defthm append-nil
  (implies (true-listp x)
           (equal (append x nil)
                  x)))

(defthm subset-append-subset
  (implies (and (subset x y)
                (subset z (append y w)))
           (subset (append x z)
                   (append y w))))

(defthm not-member-gen-cdr
  (implies (and (not (member-gen x y))
                (consp y))
           (not (member-gen x (cdr y)))))

(defthm not-member-gen-p-not-equal-car-p
  (implies (and (not (member-gen p x))
                (consp x))
           (not (equal (car x) p)))
  :rule-classes :forward-chaining)


(defthm consp-gives-member-gen-car
  (implies (consp x)
           (member-gen (car x) x)))

(defthm subset-from-del
  (subset (del x y) y))

(defthm perm-implies-subset
  (implies (perm (double-rewrite x) (double-rewrite y))
           (subset x y))
  :hints (("Goal" :induct (perm x y))))

(defthm not-equal-args-equal-member-gen
  (implies (not (equal x y))
           (equal (member-gen x (del y z))
                  (member-gen x z))))

(defcong perm equal (member-gen a x) 2)

(defthm not-member-del-equal-no-dups
  (implies (not (member-gen x (del x y)))
           (equal (no-dups-gen (del x y))
                  (no-dups-gen y))))

(defthm member-gen-x-del-x-not-no-dups
  (implies (member-gen x (del x y))
           (not (no-dups-gen y))))

(defcong perm equal (no-dups-gen x) 1)

;; Really just your basic sort of union, but "union" is a lisp
;; name so I had to come up with something else
(defun my-union (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (member-gen (car x) y)
          (my-union (cdr x) y)
        (cons (car x) (my-union (cdr x) y)))
    y))

(defthm my-union-when-not-consp
  (implies (not (consp x))
           (equal (my-union x y)
                  y)))

(defthm my-union-of-consp
  (equal (my-union (cons first rest) y)
         (if (member-gen first y)
             (my-union rest y)
           (cons first (my-union rest y)))))

(dis+ind my-union)

(defthm not-member-through-union
  (implies (and (not (member-gen x (double-rewrite a)))
                (not (member-gen x (double-rewrite b))))
           (not (member-gen x (my-union a b)))))


(defthm subset-through-my-union
  (implies (and (subset x z)
                (subset y z))
           (subset (my-union x y) z)))

