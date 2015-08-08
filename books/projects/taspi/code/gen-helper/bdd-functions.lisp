;; bdd-functions needed to represent and manipulate fringes as bdds
;; intersects with functions in qi.lisp, but is not a subset nor superset of
;; those functions

(in-package "ACL2")
(include-book "sets")

(defmacro qcons (x y)
  ;; should this be called qhons?
  `(cond ((or (and (eq ,x t)   (eq ,y t))
              (and (eq ,x nil) (eq ,y nil)))
          ,x)
         (t (hons ,x ,y))))

;; implements union
(defun q-or (x y)
  (declare (xargs :guard t))
  (if (atom x)
      (if (atom y)
          (or x y)
        (if x t y))
    (if (atom y)
        (if y t x)
      (let ((l (q-or (car x) (car y)))
            (r (q-or (cdr x) (cdr y))))
        (qcons l r)))))

(defthm q-or-when-not-consp
  (implies (not (consp x))
           (equal (q-or x y)
                  (if (atom y)
                      (or x y)
                    (if x t y)))))

(defthm q-or-of-consp
  (equal (q-or (cons first rest) y)
         (if (atom y)
             (if y t (cons first rest))
           (let ((l (q-or first (car y)))
                 (r (q-or rest (cdr y))))
             (qcons l r)))))

(dis+ind q-or)

(defun qs-subset (x y)
  (declare (xargs :guard t))
  (cond ((atom x)
         (if x (eq y t) t))
        ((atom y) (if y t nil))
        (t (and (qs-subset (car x) (car y))
                (qs-subset (cdr x) (cdr y))))))

(defthm qs-subset-when-not-consp
  (implies (not (consp x))
           (equal (qs-subset x y)
                  (if x (equal y t) t))))

(defthm qs-subset-of-consp
  (equal (qs-subset (cons first rest) y)
         (if (not (consp y))
             (if y t nil)
           (and (qs-subset first (car y))
                (qs-subset rest (cdr y))))))

(dis+ind qs-subset)

(defun qs-subset-list (list x)
  (declare (xargs :guard t))
  (if (consp list)
      (and (qs-subset (car list) x)
           (qs-subset-list (cdr list) x))
    t))

(defthm qs-subset-list-when-not-consp
  (implies (not (consp list))
           (equal (qs-subset-list list x)
                  t)))

(defthm qs-subset-list-of-consp
  (equal (qs-subset-list (cons first rest) x)
         (and (qs-subset first x)
              (qs-subset-list rest x))))

(dis+ind qs-subset-list)

(defun q-not (x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (hons (q-not (car x)) (q-not (cdr x)))))

(defthm q-not-when-not-consp
  (implies (not (consp x))
           (equal (q-not x)
                  (not x))))

(defthm q-not-of-consp
  (equal (q-not (cons first rest))
         (hons (q-not first) (q-not rest))))

(dis+ind q-not)

;; Could also be called qs-difference
(defun q-and-c2 (x y)
  (declare (xargs :guard t))
  (if (atom x)
      (if (atom y)
          (and x (not y))
        (if x (q-not y) nil))
    (if (atom y)
        (if y nil x)
      (let ((l (q-and-c2 (car x) (car y)))
            (r (q-and-c2 (cdr x) (cdr y))))
        (qcons l r)))))

(defthm q-and-c2-when-not-consp
  (implies (not (consp x))
           (equal (q-and-c2 x y)
                  (if (atom y)
                      (and x (not y))
                    (if x (q-not y) nil)))))

(defthm q-and-c2-of-consp
  (equal (q-and-c2 (cons first rest) y)
         (if (atom y)
             (if y nil (cons first rest))
           (let ((l (q-and-c2 first (car y)))
                 (r (q-and-c2 rest (cdr y))))
             (qcons l r)))))

(dis+ind q-and-c2)

;; Could also be called qs-intersect
(defun q-and (x y)
  (declare (xargs :guard t))
  (if (atom x)
      (if (atom y)
          (and x y)
        (if x y nil))
    (if (atom y)
        (if y x nil)
      (let ((l (q-and (car x) (car y)))
            (r (q-and (cdr x) (cdr y))))
        (qcons l r)))))

(defthm q-and-when-not-consp
  (implies (not (consp x))
           (equal (q-and x y)
                  (if (atom y)
                      (and x y)
                    (if x y nil)))))


(defthm q-and-of-consp
  (equal (q-and (cons first rest) y)
         (if (atom y)
             (if y (cons first rest) nil)
           (let ((l (q-and first (car y)))
                 (r (q-and rest (cdr y))))
             (qcons l r)))))

(dis+ind q-and)

(defun q-no-conflicts (x list)

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
;           be bdd based (as opposed to list based) and the underlying taxa list
;           must be preserved between x and each member of list.
;           The bipartitions are assumed to be ordered such that no bipartition
;           x following y in list exists such that y is a subset of x and x=/y.
;           See also no-conflicts (list based)."
  (declare (xargs :guard t))
  (if (consp list)
      (if (q-and x (car list))
          (and (qs-subset (car list) x)
               (q-no-conflicts x (cdr list)))
        (q-no-conflicts x (cdr list)))
    t))

(defthm q-no-conflicts-when-not-consp
  (implies (not (consp list))
           (equal (q-no-conflicts x list)
                  t)))

(defthm q-no-conflicts-of-consp
  (equal (q-no-conflicts x (cons first rest))
         (if (q-and x first)
             (and (qs-subset first x)
                  (q-no-conflicts x rest))
           (q-no-conflicts x rest))))

(dis+ind q-no-conflicts)

(defun q-no-conflicts-gen (x list)

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
;           be bdd based (as opposed to list based) and the underlying taxa list
;           must be preserved between x and each member of list.
;           Assumes no ordering of bipartitions in list.
;           See also q-no-conflicts."
  (declare (xargs :guard t))
  (if (consp list)
      (if (q-and x (car list))
          (and (or (qs-subset (car list) x)
                   (qs-subset x (car list)))
               (q-no-conflicts-gen x (cdr list)))
        (q-no-conflicts-gen x (cdr list)))
    t))

(defun q-no-conflicts-list (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Determines if the list of bipartitions list is consistent. ~/
;  ~/
;  Arguments:
;    (1) list - a list of bipartitions

;  Details: Set operations are used to determine if the list of bipartitions
;           do not conflict.  Bipartitions must be list based (as opposed to
;           bdd based), and an underlying taxa list must be preserved between
;           every pair of bipartitions in the list. The bipartitions are
;           assumed to be ordered such that no bipartition x following y in
;           list exists such that y is a subset of x and x=/y.
;           See also no-conflicts-list (list based) and q-no-conflicts-list-gen."
  (declare (xargs :guard t))
  (if (consp list)
      (and (q-no-conflicts (car list) (cdr list))
           (q-no-conflicts-list (cdr list)))
    t))

(defthm q-no-conflicts-list-when-not-consp
  (implies (not (consp x))
           (equal (q-no-conflicts-list x)
                  t)))

(defthm q-no-conflicts-list-of-consp
  (equal (q-no-conflicts-list (cons first rest))
         (and (q-no-conflicts first rest)
              (q-no-conflicts-list rest))))

(dis+ind q-no-conflicts-list)

(defun q-no-conflicts-list-gen (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Determines if the list of bipartitions list is consistent. ~/
;  ~/
;  Arguments:
;    (1) list - a list of bipartitions

;  Details: Set operations are used to determine if the list of bipartitions
;           do not conflict.  Bipartitions must be list based (as opposed to
;           bdd based), and an underlying taxa list must be preserved between
;           every pair of bipartitions in the list. No ordering on the
;           bipartitions is assumed.
;           See also q-no-conflicts-list."
  (declare (xargs :guard t))
  (if (consp list)
      (and (q-no-conflicts-gen (car list) (cdr list))
           (q-no-conflicts-list-gen (cdr list)))
    t))

; Finds bipartitions in l that refine bipartition tree.
(defun subtrees-implying (branch l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns bipartitions that refine a tree *below* the branch given.~/
;  ~/
;  Arguments:
;     (1) branch - a bdd based bipartition
;     (2) l - a list of bdd based bipartitions

;  Details: All bipartitions must be based on the same taxa list.
;           *Below* is defined in terms of the rooting given by taxa list."
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((qs-subset (car l) branch)
         (cons (car l)
               (subtrees-implying branch (cdr l))))
        (t (subtrees-implying branch (cdr l)))))

(defthm subtrees-implying-when-not-consp
  (implies (not (consp list))
           (equal (subtrees-implying branch list)
                  nil)))

(defthm subtrees-implying-of-consp
  (equal (subtrees-implying branch (cons first rest))
         (if (qs-subset first branch)
             (cons first
                   (subtrees-implying branch rest))
           (subtrees-implying branch rest))))

(dis+ind subtrees-implying)

(defun subtrees-not-implying (branch l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Returns bipartitions that are not *below* the branch given.~/
;  ~/
;  Arguments:
;     (1) branch - a bdd based bipartition
;     (2) l - a list of bdd based bipartitions

;  Details: All bipartitions must be based on the same taxa list.
;           *Below* is defined in terms of the rooting given by taxa list."
  (declare (xargs :guard t))
  (cond ((atom l) nil)
        ((not (qs-subset (car l) branch))
         (cons (car l)
               (subtrees-not-implying branch (cdr l))))
        (t (subtrees-not-implying branch (cdr l)))))

(defthm subtrees-not-implying-when-not-consp
  (implies (not (consp l))
           (equal (subtrees-not-implying branch l)
                  nil)))

(defthm subtrees-not-implying-of-consp
  (equal (subtrees-not-implying branch (cons first rest))
         (if (not (qs-subset first branch))
             (cons first
                   (subtrees-not-implying branch rest))
           (subtrees-not-implying branch rest))))

(dis+ind subtrees-not-implying)

(defthm qs-subset-nil-equal-nil
  (implies (qs-subset x nil)
           (equal x nil))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable qs-subset))))

(defthm qs-subset-and-t-equal-t
  (implies (and (qs-subset y z)
                (equal y t))
           (equal z t))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable qs-subset))))

(defthm qs-subset-transitive
  (implies (and (qs-subset x y)
                (qs-subset y z))
           (qs-subset x z))
  :hints (("Subgoal *1/3" :in-theory (enable qs-subset))))

(defthm subtrees-implying-smaller
  (<= (acl2-count (subtrees-implying x y))
      (acl2-count y))
  :rule-classes :linear)

(defthm subtrees-not-implying-smaller
  (<= (acl2-count (subtrees-not-implying x y))
      (acl2-count y))
  :rule-classes :linear)

(defthm qs-subset-list-subtrees-implying
  (qs-subset-list (subtrees-implying x y) x))

(defthm q-no-conflicts-through-subtrees-implying
  (implies (q-no-conflicts x y)
           (q-no-conflicts x (subtrees-implying z y))))

(defthm not-member-through-subtrees-implying
  (implies (not (member-gen x (double-rewrite y)))
           (not (member-gen x (subtrees-implying z y)))))

(defthm q-no-conflicts-list-through-subtrees-implying
  (implies (q-no-conflicts-list x)
           (q-no-conflicts-list (subtrees-implying y x))))

(defun valid-bdd (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (car x))
          (if (consp (cdr x))
              (and (valid-bdd (car x))
                   (valid-bdd (cdr x)))
            (and (or (equal (cdr x) t)
                     (equal (cdr x) nil))
                 (valid-bdd (car x))))
        (if (consp (cdr x))
            (and (or (equal (car x) t)
                     (equal (car x) nil))
                 (valid-bdd (cdr x)))
          (and (or (equal (car x) t)
                   (equal (car x) nil))
               (or (equal (cdr x) t)
                   (equal (cdr x) nil))
               (not (equal (car x) (cdr x))))))
    (or (equal x t)
        (equal x nil))))

(defthm valid-bdd-when-not-consp
  (implies (not (consp x))
           (equal (valid-bdd x)
                  (or (equal x t)
                      (equal x nil)))))

(defthm valid-bdd-of-consp
  (equal (valid-bdd (cons first rest))
         (if (consp first)
             (if (consp rest)
                 (and (valid-bdd first)
                      (valid-bdd rest))
               (and (or (equal rest t)
                        (equal rest nil))
                    (valid-bdd first)))
           (if (consp rest)
               (and (or (equal first t)
                        (equal first nil))
                    (valid-bdd rest))
             (and (or (equal first t)
                      (equal first nil))
                  (or (equal rest t)
                      (equal rest nil))
                  (not (equal first rest)))))))

(dis+ind valid-bdd)

(defun valid-bdd-list (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (valid-bdd (car x))
           (valid-bdd-list (cdr x)))
    t))

(defthm valid-bdd-list-when-not-consp
  (implies (not (consp x))
           (equal (valid-bdd-list x)
                  t)))

(defthm valid-bdd-list-of-consp
  (equal (valid-bdd-list (cons first rest))
         (and (valid-bdd first)
              (valid-bdd-list rest))))

(dis+ind valid-bdd-list)

(defun qs-subset-pop (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp y)
          (and (qs-subset-pop (car x) (car y))
               (qs-subset-pop (cdr x) (cdr y)))
        (if y
            (and (qs-subset-pop (car x) t)
                 (qs-subset-pop (cdr x) t))
          (and (qs-subset-pop (car x) nil)
               (qs-subset-pop (cdr x) nil))))
    (if x (equal y t) t)))

(defthm qs-subset-pop-when-not-consp
  (implies (not (consp x))
           (equal (qs-subset-pop x y)
                  (if x (equal y t) t))))

(defthm qs-subset-pop-of-consp
  (equal (qs-subset-pop (cons first rest) y)
         (if (consp y)
             (and (qs-subset-pop first (car y))
                  (qs-subset-pop rest (cdr y)))
           (if y
               (and (qs-subset-pop first t)
                    (qs-subset-pop rest t))
             (and (qs-subset-pop first nil)
                  (qs-subset-pop rest nil))))))

(dis+ind qs-subset-pop)

(defthm qs-subset-pop-not-q-and-q-and-c2
  (implies (and (qs-subset-pop y top)
                (not (q-and x y)))
           (qs-subset-pop y (q-and-c2 top x)))
  :hints (("Goal" :in-theory (enable qs-subset-pop
                                     q-and))))

(defthmd qs-subset-pop=qs-subset
  (implies (and (valid-bdd x)
                (valid-bdd y))
           (equal (qs-subset x y)
                  (qs-subset-pop x y))))

(defthm consp-through-q-not
  (implies (consp x)
           (consp (q-not x))))

(defthm valid-bdd-through-q-not
  (implies (valid-bdd x)
           (valid-bdd (q-not x)))
  :hints (("Goal" :induct (valid-bdd x))))

(defthm valid-bdd-q-and-c2-when-nil
  (implies (valid-bdd x)
           (valid-bdd (q-and-c2 x nil)))
  :hints (("Goal" :in-theory (enable q-and-c2))))

(defthm valid-bdd-q-and-c2-when-t
  (implies (valid-bdd x)
           (valid-bdd (q-and-c2 x t)))
  :hints (("Goal" :in-theory (enable q-and-c2))))

(defthm valid-bdd-through-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd y))
           (valid-bdd (q-and-c2 x y)))
  :hints (("Goal" :induct (q-and-c2 x y))))

(defthm subtrees-not-implying-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd top)
                (valid-bdd-list y)
                (qs-subset x top)
                (qs-subset-list y top)
                (q-no-conflicts x y))
           (qs-subset-list (subtrees-not-implying x y)
                           (q-and-c2 top x)))
  :hints (("Subgoal *1/5'4'"
           :use (:instance qs-subset-pop=qs-subset
                           (x y1) (y top)))
          ("Subgoal *1/5'6'"
           :in-theory (disable qs-subset-pop-not-q-and-q-and-c2)
           :use (:instance  qs-subset-pop-not-q-and-q-and-c2
                            (y y1)))
          ("Subgoal *1/5'8'"
           :use (:instance qs-subset-pop=qs-subset
                           (x y1) (y (q-and-c2 top x))))))

(defthm valid-bdd-list-through-subtrees-implying
  (implies (valid-bdd-list x)
           (valid-bdd-list (subtrees-implying y x))))

(defthm valid-bdd-list-through-subtrees-not-implying
  (implies (valid-bdd-list x)
           (valid-bdd-list (subtrees-not-implying y x))))

(defthm subset-list-gives-no-conflicts-q
  (implies (qs-subset-list y x)
           (q-no-conflicts x y)))

(defthm valid-bdd-cdr
  (implies (and (consp x)
                (valid-bdd x))
           (valid-bdd (cdr x))))

;(defthm qs-subset-pop-self
;  (implies (valid-bdd x)
;           (qs-subset-pop x x)))

;(defthm qs-subset-pop-q-and-c2
;  (implies (valid-bdd x)
;           (qs-subset-pop (q-and-c2 x y)
;                          x)))

(defthm qs-subset-self
  (implies (valid-bdd x)
           (qs-subset x x)))

(defthm q-and-c2-nil-gives-t
  (implies (valid-bdd x)
           (equal (q-and-c2 x nil)
                  x))
  :hints (("Goal" :in-theory (enable q-and-c2))))

; More for taspip build-term-helper
(defthm qs-subset-all-of-t
  (qs-subset y t)
  :hints (("Goal" :in-theory (enable qs-subset))))

(defthm qs-subset-q-and-c2
  (implies (valid-bdd x)
           (qs-subset (q-and-c2 x y)
                      x))
  :hints (("Subgoal *1/5" :in-theory (enable q-and-c2))))

(defthm not-member-gen-through-subtrees-not-implying
  (implies (not (member-gen x (double-rewrite y)))
           (not (member-gen x (subtrees-not-implying z y)))))

(defthm q-no-conflicts-through-subtrees-not-implying
  (implies (q-no-conflicts x y)
           (q-no-conflicts x (subtrees-not-implying z y))))

(defthm q-no-conflicts-list-through-subtrees-not-implying
  (implies (q-no-conflicts-list x)
           (q-no-conflicts-list (subtrees-not-implying y x))))

(defthm consp-not-equal-t
  (implies (consp x)
           (not (equal x t))))

(defthm not-q-and-c2-t
  (not (equal (q-and-c2 x t) t))
  :hints (("Goal" :in-theory (enable q-and-c2))))

(defthm consp-through-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (consp x)
                (consp y)
                (q-and-c2 x y))
           (consp (q-and-c2 x y))))

(defthm to-subset-from-not-intersect-add-in-a-not
  (implies (not (q-and x y1))
           (qs-subset y1 (q-not x)))
  :hints (("Goal" :in-theory (enable q-not q-and))))

(defthm q-no-conflicts-q-not-not-implying
  (implies (q-no-conflicts x y)
           (q-no-conflicts (q-not x)
                           (subtrees-not-implying x y))))

(defthm qs-subset-list-not-implying-q-not
  (implies (q-no-conflicts x y)
           (qs-subset-list (subtrees-not-implying x y)
                           (q-not x))))

(defthm not-intersect-keeps-consp
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (not (q-and x y))
                (consp x))
           (consp (q-and-c2 x y)))
  :hints (("Subgoal *1/1'''" :in-theory (enable q-and))))

(defthm not-q-and-nil
  (not (q-and x nil))
  :hints (("Goal" :in-theory (enable q-and))))

(defthm q-and-t
  (implies x
           (q-and x t))
  :hints (("Goal" :in-theory (enable q-and))))

(defthm q-and-q-and-c2-gives-q-and
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (valid-bdd z)
                (q-and (q-and-c2 x y) z))
           (q-and x z)))

(defthm not-q-and-c2-gives-subset
  (implies (and (not (q-and-c2 x y))
                (valid-bdd x)
                (valid-bdd y))
           (qs-subset x y))
  :rule-classes :forward-chaining)

(defthm to-not-subset
  (implies (and (qs-subset x y)
                (valid-bdd x)
                (valid-bdd y)
                (valid-bdd z)
                (consp z)
                (not (q-and y z)))
           (not (qs-subset z x))))

(defthm not-subset-subset-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (valid-bdd z)
                (not (q-and y z))
                (qs-subset z x))
           (qs-subset z (q-and-c2 x y))))

(defthm q-no-conflicts-q-and-c2-not-implying
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (valid-bdd-list (double-rewrite z))
                (not (member-gen t (double-rewrite z)))
                (not (member-gen nil (double-rewrite z)))
                (q-no-conflicts x z)
                (q-no-conflicts y z))
           (q-no-conflicts (q-and-c2 x y)
                           (subtrees-not-implying y z))))

(defthm q-and-c2-self-nil
  (not (q-and-c2 x x)))

(defthm not-consp-q-and-c2-equal
  (implies (and (not (consp (q-and-c2 y x)))
                (consp x)
                (valid-bdd x)
                (valid-bdd y)
                (qs-subset x y))
           (equal x y))
  :rule-classes :forward-chaining)

(defthm subset-list-not-implying-nil
  (implies (qs-subset-list under top)
           (equal (subtrees-not-implying top under)
                  nil)))

(defthm to-consp
  (implies (and (valid-bdd x)
                (not (equal x t))
                x)
           (consp x))
  :rule-classes :forward-chaining)

(defthm q-not-conclusion
  (implies (consp x)
           (q-not x)))

(defthm to-not-t
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (consp x)
                (q-and-c2 x y)
                (qs-subset y x))
           (consp (q-and-c2 x y))))

(defthm valid-bdd-not-nil-or-t-consp
  (implies (and (valid-bdd x)
                (not (equal x t))
                (not (equal x nil)))
           (consp x))
  :rule-classes :forward-chaining)


(defthm valid-bdd-list-cdr
  (implies (valid-bdd-list x)
           (valid-bdd-list (cdr x))))


(defthm valid-bdd-list-gives-valid-bdd-car
  (implies (valid-bdd-list x)
           (valid-bdd (car x))))


(defthm q-no-conflicts-list-cdr
  (implies (q-no-conflicts-list x)
           (q-no-conflicts-list (cdr x))))

(defthm valid-bdd-not-consp-or-t-nil
  (implies (and (valid-bdd x)
                (not (consp x)))
           (or (equal x t)
               (equal x nil)))
  :rule-classes nil)

(defthm valid-bdd-list-through-my-union
  (implies (and (valid-bdd-list x)
                (valid-bdd-list y))
           (valid-bdd-list (my-union x y))))


(defthm valid-bdd-through-q-or
  (implies (and (valid-bdd x)
               (valid-bdd y))
          (valid-bdd (q-or x y)))
  :hints (("Goal" :in-theory (enable q-or))))


(defthm q-or-if-either
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (or (not (equal x nil))
                    (not (equal y nil))))
           (q-or x y))
  :hints (("Goal" :in-theory (enable q-or))))

