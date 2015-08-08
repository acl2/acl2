(in-package "ACL2")
(include-book "arithmetic-3/bind-free/top" :dir :system)
(include-book "../gen-helper/extra")

; Definition.  If a and b are trees, then a is a "subtree" of b if and
; only if either (1) a is b or (2) b is a list and a is a subtree of
; a member of b.

; Definition.  If a and b are trees, a is a "proper subtree" of b iff
; a is a subtree of b and a is not b.

(mutual-recursion
 (defun subtreep (a b)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Determines if the first argument is a subtree of the second.~/
;   ~/
;   Arguments:
;      (1) a - a tree
;      (2) b - a tree

;  Details: Requires both arguments to be ordered according to the same
;           taxa-list.  Not a traditional form of subtree in that it does
;           not take into account unrootedness. See u-subtreep."
   (declare (xargs :guard t
                   :measure (tree-measure b t)))
   (or (equal a b)
       (proper-subtreep a b)))

 (defun proper-subtreep (a b)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Determines if the first argument is a proper subtree of the second.~/
;   ~/
;   Arguments:
;      (1) a - a tree
;      (2) b - a tree

;  Details: Requires both arguments to be ordered according to the same
;           taxa-list.  Not a traditional form of subtree in that it does
;           not take into account unrootedness. See u-proper-subtreep."
   (declare (xargs :guard t
                   :measure (tree-measure b nil)))
   (if (atom b)
       nil
     (or (subtreep a (car b))
         (proper-subtreep a (cdr b))))))

(defthm subtree-p-when-not-equal
  (implies (not (equal a b))
           (equal (subtreep a b)
                  (proper-subtreep a b))))

(defthm proper-subtreep-when-not-consp
  (implies (not (consp b))
           (equal (proper-subtreep a b)
                  nil)))

(defthm proper-subtreep-of-cons
  (equal (proper-subtreep a (cons first rest))
         (or (subtreep a first)
             (proper-subtreep a rest))))

(in-theory (disable subtreep proper-subtreep))

;; True if some element of l is a proper subtree of a.
(defun has-proper-subtree-in-list (a l)
  (declare (xargs :guard t))
  (if (atom l)
      nil
    (or (proper-subtreep (car l) a)
        (has-proper-subtree-in-list a (cdr l)))))

(defthm has-proper-subtree-in-list-when-not-consp
  (implies (not (consp l))
           (equal (has-proper-subtree-in-list a l)
                  nil)))

(defthm has-proper-subtree-in-list-of-consp
  (equal (has-proper-subtree-in-list a (cons first rest))
         (or (proper-subtreep first a)
             (has-proper-subtree-in-list a rest))))

(dis+ind has-proper-subtree-in-list)

;; True if no member of rest has a proper subtree in full.
;; A list l for which no member is a proper subtree of any other satistfies
;; (non-subtree-listp l l).
(defun non-subtree-listp (rest full)
  (declare (xargs :guard t))
  (if (atom rest)
      t
    (and (not (has-proper-subtree-in-list (car rest) full))
         (non-subtree-listp (cdr rest) full))))

(defthm non-subtree-listp-when-not-consp
  (implies (not (consp rest))
           (equal (non-subtree-listp rest full)
                  t)))

(defthm non-subtree-listp-of-consp
  (equal (non-subtree-listp (cons first rest) full)
         (and (not (has-proper-subtree-in-list first full))
              (non-subtree-listp rest full))))

(dis+ind non-subtree-listp)

; Definition.  "tip" means a symbol or integer.
(defun tip-p (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes whether or not input is a valid taxa name.~/
;  ~/
;  Arguments:
;    (1) x - a possible taxa name

;  Details: Does not allow branch lengths (see tip-p-brlen)."
  (declare (xargs :guard t))
  (or (and (symbolp x)
           (not (equal x nil)))
      (integerp x)))

(defthm tip-p-when-not-consp
  (implies (not (consp x))
           (equal (tip-p x)
                  (or (and (symbolp x)
                           (not (equal x nil)))
                      (integerp x)))))

(defthm tip-p-of-cons
  (equal (tip-p (cons first rest))
         nil))

(in-theory (disable tip-p))

;; A list of tips (integers or symbols),
;;  so we know we can sort them with olessp.
(defun tip-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (tip-p (car l))
         (tip-listp (cdr l)))))

(defthm tip-listp-when-not-consp
  (implies (not (consp l))
           (equal (tip-listp l)
                  t)))

(defthm tip-listp-of-consp
  (equal (tip-listp (cons first rest))
         (and (tip-p first)
              (tip-listp rest))))

(dis+ind tip-listp)

;; tree-recognizers

; Definition.  "tree" means a tip or, recursively, a list of 1 or more
; trees.
;; treep checks that we don't have singleton subtrees unless its a tip
(mutual-recursion
 (defun treep (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes well formed trees with no branch lengths and no singletons.~/
;   ~/
;   Arguments:
;      (1) x - a potential tree

;   Details: Well formed tips are defined as in tip-p, branch lengths are not
;            permitted (see treep-brlens)."
   (declare (xargs :guard t
                   :measure (tree-measure x t)))
   (or (tip-p x)
       (and (consp x)
            (consp (cdr x))
            (tree-listp x))))

 (defun tree-listp (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes a list of well formed trees with no branch lengths
;   and no singletons.~/
;   ~/
;   Arguments:
;      (1) list - a list of potential trees

;   Details: Well formed tips are defined as in tip-p, branch lengths are not
;            permitted (see tree-listp-brlens)."
   (declare (xargs :guard t
                   :measure (tree-measure list nil)))
   (if (atom list)
       (null list) ;; required to be true-listp
     (and (treep (car list))
          (tree-listp (cdr list))))))

(defthm treep-when-not-consp
  (implies (not (consp x))
           (equal (treep x)
                  (tip-p x))))

(defthm treep-of-consp
  (equal (treep (cons first rest))
         (and (consp rest)
              (tree-listp (cons first rest)))))

(dis+ind treep)

(defthm tree-listp-when-not-consp
  (implies (not (consp x))
           (equal (tree-listp x)
                  (null x))))

(defthm tree-listp-of-consp
  (equal (tree-listp (cons first rest))
         (and (treep first)
              (tree-listp rest))))

(dis+ind tree-listp)

;; taspip is both stronger and weaker than treep:
;; requires no labelling at internal nodes, but does allow
;; singleton subtrees
;;; neither taspip->treep nor treep->taspip in all cases

;; Question: Should we make a mutually recursive version??
(defun taspip (flg x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Recognizes well formed trees with no branch lengths
;   while allowing singletons.~/
;   ~/
;   Arguments:
;      (1) flg - nil indicating a set of trees,
;                non-nil indicating a single tree
;      (2) x - a potential tree

;   Details: Well formed tips are defined as in tip-p, branch lengths are not
;            permitted but singletons are allowed (see taspip-brlens)."
  (declare (xargs :measure (make-ord (1+ (acl2-count x))
                                     1
                                     (if flg 1 0))
                  :guard t))
  (if flg
      (if (atom x)
          (or (and (symbolp x)
                   (not (equal x nil)))
              (integerp x))
        (taspip nil x))
    (if (atom x)
        (null x)
      (and (taspip t (car x))
           (taspip nil (cdr x))))))

(defthm taspip-when-not-consp
  (implies (not (consp x))
           (equal (taspip flg x)
                  (if (double-rewrite flg)
                      (or (and (symbolp x)
                               (not (equal x nil)))
                          (integerp x))
                    (equal x nil)))))

(defthm taspip-of-cons
  (equal (taspip flg (cons first rest))
         (and (taspip t first)
              (taspip nil rest))))

(dis+ind taspip)

(defthm taspip-nil-and-consp-gives-taspip-flg
  (implies (and (taspip nil x)
                (consp x))
           (taspip flg x))
  :hints (("Goal" :in-theory (enable taspip)
           :cases (flg))))

(defthm taspip-flg-and-flg-open
  (implies (and (taspip flg y)
                flg
                (consp y))
           (taspip nil y))
  :hints (("Goal" :in-theory (enable taspip)))
  :rule-classes :forward-chaining)


(defthm tip-p-gives-taspip-t
  (implies (tip-p x)
           (taspip t x))
  :hints (("Goal" :in-theory (enable taspip tip-p))))

;; counts the tips in a tree
;; (to be used to check no proper subtrees property)
(mutual-recursion
 (defun count-tips (tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Returns the number of leaves in a tree.~/
;   ~/
;   Arguments:
;      (1) x - a tree

;   Details: Does not matter if branch lengths are present or not. "
   (declare (xargs :guard t
                   :measure (tree-measure tree t)))
   (if (atom tree)
       1
     (count-tips-list tree)))

 (defun count-tips-list (list)
   (declare (xargs :guard t
                   :measure (tree-measure list nil)))
   (if (atom list)
       0
     (+ (count-tips (car list))
        (count-tips-list (cdr list))))))

(defthm count-tips-when-not-consp
  (implies (not (consp x))
           (equal (count-tips x)
                  1)))

(defthm count-tips-of-consp
  (equal (count-tips (cons first rest))
         (count-tips-list (cons first rest))))

(dis+ind count-tips)

(defthm count-tips-list-when-not-consp
  (implies (not (consp x))
           (equal (count-tips-list x) 0)))

(defthm count-tips-list-of-consp
  (equal (count-tips-list (cons first rest))
         (+ (count-tips first)
            (count-tips-list rest))))

(dis+ind count-tips-list)

;; A list of trees all the same size (as given by count-tips) has the property
;; that no member is a proper subtree of any other, which is a property we want
;; the input lists to have without us having to check for it.
(defun trees-with-n-tips (n list)
  (declare (xargs :guard (acl2-numberp n)))
  (if (atom list)
      t
    (and (equal n (count-tips (car list)))
         (trees-with-n-tips n (cdr list)))))

(defthm trees-with-n-tips-when-not-consp
  (implies (not (consp list))
           (equal (trees-with-n-tips n list) t)))

(defthm trees-with-n-tips-of-consp
  (equal (trees-with-n-tips n (cons first rest))
         (and (equal n (count-tips first))
              (trees-with-n-tips n rest))))

(dis+ind trees-with-n-tips)

(defun all-same-num-tips (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Determines if all of the trees in the input have the same number of leaves.~/
;   ~/
;   Arguments:
;      (1) list - a list of trees

;   Details: Does not matter if branch lengths are present or not. "
  (declare (xargs :guard t))
  (or (atom list)
      (trees-with-n-tips (count-tips (car list)) (cdr list))))

(defthm all-same-num-tips-when-not-consp
  (implies (not (consp list))
           (equal (all-same-num-tips list) t)))

(defthm all-same-num-tips-of-consp
  (equal (all-same-num-tips (cons first rest))
         (trees-with-n-tips (count-tips first)
                            rest)))

(in-theory (disable all-same-num-tips))

;; Recognizes a list of nontip trees.
;(defun tree-list-listp (l)
;  (declare (xargs :guard t))
;  (if (atom l)
;      t
;    (and (consp (car l))
;         (consp (cdar l))
;         (tree-listp (car l))
;         (tree-list-listp (cdr l)))))

;; Same as above, but I (Serita) like it better
(defun non-tip-tree-listp (x)
  "a list of nontip trees"
  (declare (xargs :guard t))
  (if (atom x)
      (null x) ; so that it implies tree-listp
    (and (consp (car x))
         (treep (car x))
         (non-tip-tree-listp (cdr x)))))

;; this proves that they are indeed the same
;(defthm treep-of-cons
;  (implies (and (consp x)
;                (treep x))
;           (tree-listp x))
;  :hints (("Goal" :in-theory (enable treep tree-listp tip-p))))

;(defthm equal-tree-list-listp-non-tip-tree-listp
;  (equal (tree-list-listp l)
;         (non-tip-tree-listp l)))

;; instead of changing all the code, we can use this macro
(defmacro tree-list-listp (l)
  `(non-tip-tree-listp ,l))

(defthm non-tip-tree-listp-when-not-consp
  (implies (not (consp x))
           (equal (non-tip-tree-listp x)
                  (null x))))

(defthm non-tip-tree-listp-of-cons
  (equal (non-tip-tree-listp (cons first rest))
         (and (consp first)
              (treep first)
              (non-tip-tree-listp rest))))

(dis+ind non-tip-tree-listp)


;(defthm true-listp-append
;  (equal (true-listp (append x y))
;         (true-listp y)))

;; Gives the taxa names present in a tree
;; assumes?? no nil named subtrees
(defun mytips (tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns the taxa names from a tree.~/
;   ~/
;   Arguments:
;      (1) tree - a tree

;   Details: Assumes branch lengths are not present and that no taxon has been
;            assigned the name *nil*. See mytips-brlens."
  (declare (xargs :guard t))
  (if (consp tree)
      (append (mytips (car tree))
              (mytips (cdr tree)))
    (if (equal tree nil)
        nil
      (list tree))))

(defthm mytips-when-not-consp
  (implies (not (consp x))
           (equal (mytips x)
                  (if (equal x nil)
                      nil
                    (list x)))))

(defthm mytips-of-consp
  (equal (mytips (cons first rest))
         (append (mytips first)
                 (mytips rest))))

(dis+ind mytips)

(defthm true-listp-mytips
  (true-listp (mytips x)))

;;Gives name of taxon first appearing in representation
(defun first-taxon (term)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns the taxon name first appearing in the tree representation.~/
;   ~/
;   Arguments:
;      (1) term - a tree

;   Details: Does not matter if branch lengths are present or not. "
  (declare (xargs :guard t))
  (if (atom term)
      term
    (first-taxon (car term))))

(defthm first-taxon-when-not-consp
  (implies (not (consp x))
           (equal (first-taxon x)
                  x)))

(defthm first-taxon-of-consp
  (equal (first-taxon (cons first rest))
         (first-taxon first)))

(dis+ind first-taxon)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; theorems about above functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm tip-p-not-integer-gives-symbolp
  (implies (and (tip-p x)
                (not (integerp x)))
           (symbolp x))
  :hints (("Goal" :in-theory (enable tip-p))))


;; appears above
;(defthm balanced-gives-equal-depth-level
;  (implies (and (balanced-tree-helper x level)
;                (integerp level)
;                (<= 0 level))
;           (equal (depth x) level)))

;(defthm balanced-gives-equal-depths-consp
;  (implies (and (balanced-tree-helper x y)
;                (consp x))
;           (equal (depth (car x))
;                  (depth (cdr x))))
;;  :hints (("Goal" :in-theory (enable balanced-tree-helper)))
;  :rule-classes :forward-chaining)

;(defthm consp-depth-not-zero
;  (implies (consp x)
;           (< 0 (depth x)))
;  :rule-classes :forward-chaining)



(defthm treep-and-consp-gives-tree-listp
  (implies (and (treep x)
                (consp x))
           (tree-listp x))
  :hints (("Goal" :in-theory (enable treep
                                     tree-listp
                                     tip-p)))
  :rule-classes :forward-chaining)

;(defthm treep-gives-tree-listp
;  (implies (treep x)
;           (tree-listp x))
;  :hints (("Goal" :in-theory (enable treep
;                                     tip-p
;                                     tree-listp))))

(defthm count-tips-of-consp-equal-count-tips-list
  (implies (consp x)
           (equal (count-tips x)
                  (count-tips-list x)))
  :hints (("Goal" :in-theory (enable count-tips))))

(defthm tip-p-gives-count-tips-list-equal-0
  (implies (tip-p x)
           (equal (count-tips-list x)
                  0))
  :hints (("Goal" :in-theory (enable tip-p))))

(defthm tip-p-not-proper-subtree
  (implies (tip-p x)
           (not (proper-subtreep y x)))
  :hints (("Goal" :in-theory (enable tip-p))))

(defthm tree-list-listp-tree-listp
  (implies (tree-list-listp x)
           (tree-listp x)))

;; Stuff about count-tips and subtrees
(defthm count-tips-min
  (and (implies (flag flg t)
                (<= 1 (count-tips x)))
       (implies (flag flg nil)
                (and (<= 0 (count-tips-list x))
                     (implies (consp x)
                              (<= 1 (count-tips-list x))))))
  :hints (("Goal" :induct (tree-p-induction x flg)))
  :rule-classes (:rewrite :linear))

;; Main thing here is
;; (implies (and (treep b) (proper-subtreep a b))
;;          (< (count-tips a) (count-tips b))
;; which we'll use to say that if the tip counts of all the trees in a list are
;; equal, then no tree is a proper subtree of any other.
;(defthm count-tips-subtrees
;  (and (implies (and (flag flg t)
;                     (subtreep a b)
;                     (treep b))
;                (<= (count-tips a) (count-tips b)))
;       (implies (and (flag flg nil)
;                     (proper-subtreep a b))
;                (and (implies (treep b)
;                              (< (count-tips a) (count-tips b)))
;                     (implies (tree-listp b)
;                              (<= (count-tips a) (count-tips b))))))
;  :hints (("Goal" :induct (tree-p-induction b flg)))
;  :rule-classes (:rewrite :linear))

(defthm count-tips-list-subtrees
  (and (implies (and (flag flg t)
                     (subtreep a b)
                     (treep b))
                (<= (count-tips-list a) (count-tips-list b)))
       (implies (and (flag flg nil)
                     (proper-subtreep a b))
                (and (implies (treep b)
                              (< (count-tips-list a)
                                 (count-tips-list b)))
                     (implies (tree-listp b)
                              (<= (count-tips-list a)
                                  (count-tips-list b))))))
  :hints (("Goal" :induct (tree-p-induction b flg)
           :in-theory (enable subtreep count-tips)))
  :rule-classes (:rewrite :linear))

(defthm proper-subtree-gives-<-count-tips
  (implies (and (treep b)
                (proper-subtreep a b))
           (< (count-tips a) (count-tips b)))
  :hints (("Goal" :in-theory (enable subtreep
                                     proper-subtreep
                                     count-tips
                                     count-tips-list
                                     treep)))
  :rule-classes (:rewrite :linear))

(defthm trees-with-n-tips-not-has-proper-subtree-in-list
  (implies (and (trees-with-n-tips n list)
                (treep tree)
                (>= n (count-tips tree)))
           (not (has-proper-subtree-in-list tree list))))

(defthm trees-with-n-tips-non-subtree-listp
  (implies (let ((n (if (consp l2)
                        (count-tips (car l2))
                      (if (consp l1)
                          (count-tips (car l1))
                        0))))
             (and (trees-with-n-tips n l1)
                  (trees-with-n-tips n l2)
                  (tree-listp l1)))
           (non-subtree-listp l1 l2)))

(defthm all-same-num-tips-non-subtree-listp
  (implies (and (all-same-num-tips list)
                (tree-listp list))
           (non-subtree-listp list list)))

(defthm all-same-num-tips-atom
  (implies (atom x)
           (all-same-num-tips x)))

;(defthm balanced-tree-helper-cdr
;  (implies (and (balanced-tree-helper first
;                                      (depth rest))
;                (balanced-tree-helper rest
;                                      (1- (depth (cons first rest)))))
;           (balanced-tree-helper rest
;                                 (depth rest)))
;  :hints (("Goal" :in-theory
;           (e/d (balanced-tree-helper depth)
;                (balanced-tree-helper-when-not-zp)))))

(defthm subtreep-self
  (subtreep x x)
  :hints (("Goal" :in-theory (enable subtreep))))

(defthm subtreep-smaller
  (implies (subtreep a b)
           (<= (acl2-count a)
               (acl2-count b)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable subtreep))))

(defthm non-subtree-listp-cdrs
  (implies (non-subtree-listp rest full)
           (non-subtree-listp (cdr rest) (cdr full))))

(defthm proper-gives-subtree
  (implies (proper-subtreep x tree)
           (subtreep x tree))
  :hints (("Goal" :in-theory (enable subtreep))))


(defthm tree-listp-and-consp-gives-treep
  (implies (and (tree-listp x)
                (consp x)
                (consp (cdr x)))
           (treep x))
  :hints (("Goal" :in-theory (enable treep tip-p))))


(defthm taspip-flg-and-flg-gives-t
  (implies (and (taspip flg x)
                flg)
           (taspip t x)))

(defthm taspip-flg-consp-gives-taspip-nil
  (implies (and (taspip flg x)
                (consp x))
           (taspip nil x)))
