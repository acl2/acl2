; fringes.lisp
; from replete-trees and taxon.lisp of Boyer & Hunt

; Computing the frequencies of fringes in a set of trees.
; Start with a replete database mapping trees to parents.
; Then, represent fringes as either lists or BDDs.

(in-package "ACL2")

(include-book "../gen-trees/sets-lists-trees")
(include-book "../replete/replete")
(include-book "../gen-trees/btrees-bdds")

;;; Ordered and duplicate-free fringes

(defun olessp (x y)
  (declare (xargs :guard (and (tip-p x)
                              (tip-p y))))
  ;; orders integers and symbols, with integers first, ordered by <,
  ;; and symbols next, ordered by symbol<.
  (cond ((integerp x)
         (cond ((integerp y) (< x y))
               (t t)))
        ((integerp y) nil)
        (t (symbol< x y))))

(in-theory (disable olessp))

(defun omerge-oless (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))
                  :guard (and (tip-listp x)
                              (tip-listp y))))
  (cond ((atom x) y)
        ((atom y) x)
        ((olessp (car x) (car y))
         (cons (car x) (omerge-oless (cdr x) y)))
        ((olessp (car y) (car x))
         (cons (car y) (omerge-oless x (cdr y))))
        (t (cons (car x) (omerge-oless (cdr x) (cdr y))))))

(defthm omerge-oless-when-not-consp-first
  (implies (not (consp x))
           (equal (omerge-oless x y)
                  y)))

(defthm omerge-oless-when-not-consp-second
  (implies (not (consp y))
           (equal (omerge-oless x y)
                  (if (consp x)
                      x
                    y))))

(defthm omerge-oless-when-both-consp
  (equal (omerge-oless (cons first rest) (cons first1 rest1))
         (cond ((olessp first first1)
                (cons first (omerge-oless rest (cons first1 rest1))))
               ((olessp first1 first)
                (cons first1 (omerge-oless (cons first rest)
                                           rest1)))
               (t (cons first (omerge-oless rest rest1))))))

(dis+ind omerge-oless)

; (ofringe-oless x) returns the ordered (by olessp) and duplicate-free list
; of tip subtrees of x.

(mutual-recursion
(defun ofringe-oless (x)
  (declare (xargs :measure (+ 1 (* 2 (acl2-count x)))
                  :guard (treep x)
                  :verify-guards nil))
  (hopy (cond ((atom x) (hist x))
              (t (ofringe-oless-list x)))))

(defun ofringe-oless-list (l)
  (declare (xargs :measure (* 2 (acl2-count l))
                  :guard (tree-listp l)))
  (cond ((atom l) nil)
        (t (omerge-oless (ofringe-oless (car l))
                         (ofringe-oless-list (cdr l))))))
)

(defthm ofringe-oless-when-not-consp
  (implies (not (consp x))
           (equal (ofringe-oless x)
                  (list x))))

(defthm ofringe-oless-of-consp
  (equal (ofringe-oless (cons first rest))
         (omerge-oless (ofringe-oless first)
                       (ofringe-oless-list rest))))

(defthm consp-gives-equal-ofringe-to-ofringe-list
  (implies (consp x)
           (equal (ofringe-oless x)
                  (ofringe-oless-list x))))

(dis+ind ofringe-oless)

(defthm ofringe-oless-list-when-not-consp
  (implies (not (consp x))
           (equal (ofringe-oless-list x)
                  nil)))

(defthm ofringe-oless-list-of-consp
  (equal (ofringe-oless-list (cons first rest))
         (omerge-oless (ofringe-oless first)
                       (ofringe-oless-list rest))))

(dis+ind ofringe-oless-list)

;;; Fringe Frequencies

; Fringe-frequencies takes a list l of nontip trees such that no
; member of l is a proper subtree of any member of l.
; Fringe-frequencies returns a minimal length alist that pairs to the
; fringe fr of each nontip subtree of each member of l the number of
; occurrences in l of non-tip subtrees of members of l that have
; fringe fr.

(defun fringe-frequencies1 (l dbterms dbfringe-frequencies)
  (declare (xargs :guard (and (integer-halistp dbfringe-frequencies)
                              (alistp-gen dbterms)
                              (nat-or-cons-range-halistp dbterms)
                              (if-cons-range-member-of-all-halistp
                               dbterms)
                              (if-cons-range-subset-of-domain-halistp
                               dbterms
                               dbterms)
                              (alistp-gen l)
                              (tree-list-domain-alistp l))
                  :verify-guards nil))
  (cond ((atom l) dbfringe-frequencies)
        (t (let* ((o (ofringe-oless (car (car l))))
                  (p (het o dbfringe-frequencies)))
             (fringe-frequencies1
              (cdr l)
              dbterms
              (hut o (+ (if p (cdr p) 0) (frequency (car (car l)) dbterms))
                   dbfringe-frequencies))))))

(defthm fringe-frequencies1-when-not-consp
  (implies (not (consp l))
           (equal (fringe-frequencies1 l dbterms dbff)
                  dbff)))

(defthm fringe-frequencies1-of-consp
  (equal (fringe-frequencies1 (cons first rest) dbterms dbff)
         (let* ((o (ofringe-oless (car first)))
                (p (het o dbff)))
           (fringe-frequencies1
            rest
            dbterms
            (hut o (+ (if p (cdr p) 0) (frequency (car first) dbterms))
                 dbff)))))

(dis+ind fringe-frequencies1)

(defun fringe-frequencies (l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of the list based bipartitions present in the input list
;  of trees to the number of times it appeared in the input.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees

; Details: Trees in input list should not have branch lengths.  Trees should
;          all be ordered according to the same underlying taxa list.
;          See also fringe-frequencies-brlens."
  (declare (xargs :guard (and (tree-list-listp l)
                              (all-same-num-tips l))
                  :verify-guards nil))
  (let ((dbterms (hhshrink-alist (replete-trees-list-top l) nil)))
    (hshrink-alist (fringe-frequencies1 dbterms dbterms nil) nil)))

(in-theory (disable fringe-frequencies))

;; ====== end of list version of fringes and frequencies =======

;; =========== bdd version of fringes and frequencies ==========
(defun mc-flatten-cdr-first (x a)
  (declare (xargs :guard t))
  (if (atom x)
      (cons x a)
    (mc-flatten-cdr-first (cdr x)
                          (mc-flatten-cdr-first (car x) a))))

(defun btree-to-fringe-help (btree full-taxa-list-tree)
  (declare (xargs
            :guard (and (consp btree)
                        (balanced-tree
                         full-taxa-list-tree)
                        (<= (depth btree)
                            (depth full-taxa-list-tree)))
            :verify-guards nil))
  (if (atom btree) ;changed to make inductions work nicer
      (if btree full-taxa-list-tree nil); 'we-have-a-problem
    (let ((a (car btree))
          (d (cdr btree)))
      (if (atom a)
          (if (atom d)
              (if a
                  (car full-taxa-list-tree)
                (cdr full-taxa-list-tree))
            (if a
                (hons (car full-taxa-list-tree)
                      (btree-to-fringe-help
                       (cdr btree)
                       (cdr full-taxa-list-tree)))
              (btree-to-fringe-help
               (cdr btree)
               (cdr full-taxa-list-tree))))
        (if (atom d)
            (if d
                (hons (btree-to-fringe-help
                       (car btree)
                       (car full-taxa-list-tree))
                      (cdr full-taxa-list-tree))
              (btree-to-fringe-help
               (car btree)
               (car full-taxa-list-tree)))
          (hons (btree-to-fringe-help
                 (car btree)
                 (car full-taxa-list-tree))
                (btree-to-fringe-help
                 (cdr btree)
                 (cdr full-taxa-list-tree))))))))

(defthm btree-to-fringe-help-when-not-consp
  (implies (not (consp btree))
           (equal (btree-to-fringe-help btree ftlt)
                  (if btree ftlt nil))))

(defthm btree-to-fringe-help-of-consp
  (equal (btree-to-fringe-help (cons first rest) ftlt)
         (let ((a first)
               (d rest))
           (if (atom a)
               (if (atom d)
                   (if a (car ftlt) (cdr ftlt))
                 (if a
                     (hons (car ftlt)
                           (btree-to-fringe-help rest (cdr ftlt)))
                   (btree-to-fringe-help rest (cdr ftlt))))
             (if (atom d)
                 (if d
                     (hons (btree-to-fringe-help first (car ftlt))
                           (cdr ftlt))
                   (btree-to-fringe-help first(car ftlt)))
               (hons (btree-to-fringe-help first (car ftlt))
                     (btree-to-fringe-help rest (cdr ftlt))))))))

(dis+ind btree-to-fringe-help)

; btree would result from BDD operations, and specifies what part of
; the "full" tree to keep.
(defun btree-to-fringe (btree full-taxa-list-tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the list based version of the bdd based bipartition given.~/
;  ~/
;  Arguments:
;     (1) btree - a bdd based bipartition
;     (2) full-taxa-list-tree - a binary tree based version of the taxa list

;  Details: The btree given must have a depth less than that of the
;           full-taxa-list-tree and the resulting bipartition will have
;           the taxa given in the full-taxa-list-tree. "
  (declare (xargs :guard (and (balanced-tree
                               full-taxa-list-tree)
                              (<= (depth btree)
                                  (depth full-taxa-list-tree)))
                  :verify-guards nil))

  (if (atom btree)
      (if btree (mc-flatten-cdr-first full-taxa-list-tree nil) nil)
    (mc-flatten-cdr-first
     (btree-to-fringe-help btree full-taxa-list-tree) nil)))

(defthm btree-to-fringe-when-not-consp
  (implies (not (consp btree))
           (equal (btree-to-fringe btree ftlt)
                  (if btree (mc-flatten-cdr-first ftlt nil) nil))))

(defthm btree-to-fringe-of-consp
  (equal (btree-to-fringe (cons first rest) ftlt)
         (mc-flatten-cdr-first
          (btree-to-fringe-help (cons first rest) ftlt) nil)))

;(defthm btree-to-fringe-of-consp-explicit
;  (implies (consp btree)
;           (equal (btree-to-fringe btree ftlt)
;                  (mc-flatten-cdr-first
;                   (btree-to-fringe-help btree ftlt) nil))))

(in-theory (disable btree-to-fringe))


; it may be easy, and desireable, to make the following two functions faster
; by avoiding the creation of the full fringe

(defun btree-to-fringe-length (btree full-taxa-list-tree)
  (declare (xargs :guard (and (balanced-tree
                               full-taxa-list-tree)
                              (<= (depth btree)
                                  (depth full-taxa-list-tree)))
                  :verify-guards nil))
  (len (btree-to-fringe btree full-taxa-list-tree)))

(defun btree-fringe-first (btree full-taxa-list-tree)
  (declare (xargs :guard (and (balanced-tree
                               full-taxa-list-tree)
                              (<= (depth btree)
                                  (depth full-taxa-list-tree)))
                  :verify-guards nil))
  (car (btree-to-fringe btree full-taxa-list-tree)))

(mutual-recursion
 (defun bfringe (x ta)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Returns the bdd based bipartition implied by the (sub)tree given.~/
;   ~/
;   Arguments:
;      (1) x - a tree (usually a subtree of some larger tree)
;      (2) ta - a mapping of taxa-names their bdd based representation

;  Details: Arguments can actually be more general.  Another way to think of
;           this is that it returns the taxa names in the tree x, represented
;           as a bdd.  Requires that the taxa names in the tree are keys in the
;           ta argument. "
   (declare (xargs :measure (+ 1 (* 2 (acl2-count x)))
                   :guard t))
   (hopy (cond ((atom x) (cdr (het x ta)))
               (t (bfringe-list x ta)))))

 (defun bfringe-list (l ta)
   (declare (xargs :measure (* 2 (acl2-count l))
                   :guard t))
   (cond ((atom l) nil)
         (t (q-or (bfringe (car l) ta)
                  (bfringe-list (cdr l) ta))))))

(defthm bfringe-when-not-consp
  (implies (not (consp x))
           (equal (bfringe x ta)
                  (cdr (het x ta)))))

(defthm bfringe-of-consp
  (equal (bfringe (cons first rest) ta)
         (q-or (bfringe first ta)
               (bfringe-list rest ta))))

(dis+ind bfringe)

(defthm bfringe-list-when-not-consp
  (implies (not (consp x))
           (equal (bfringe-list x ta)
                  nil)))

(defthm bfringe-list-of-consp
  (equal (bfringe-list (cons first rest) ta)
         (q-or (bfringe first ta)
               (bfringe-list rest ta))))

(dis+ind bfringe-list)

(defun bfringe-frequencies1 (l dbterms dbfringe-frequencies ta)
  (declare (xargs
            :guard
            (and (integer-halistp dbfringe-frequencies)
                 (alistp-gen dbterms)
                 (nat-or-cons-range-halistp dbterms)
                 (if-cons-range-member-of-all-halistp
                  dbterms)
                 (if-cons-range-subset-of-domain-halistp
                  dbterms
                  dbterms)
                 (alistp-gen l)
                 (tree-list-domain-alistp l))
            :verify-guards nil))
  (cond ((atom l) dbfringe-frequencies)
        (t (let* ((o (bfringe (car (car l)) ta))
                  (p (het o dbfringe-frequencies)))
             (bfringe-frequencies1
              (cdr l)
              dbterms
              (hut o (+ (if p (cdr p) 0)
			(frequency (car (car l)) dbterms))
                   dbfringe-frequencies)
              ta)))))

(defthm bfringe-frequencies1-when-not-consp
  (implies (not (consp l))
           (equal (bfringe-frequencies1 l dbterms dbff ta)
                  dbff)))

(defthm bfringe-frequencies1-of-consp
  (equal (bfringe-frequencies1 (cons first rest)
                               dbterms dbff ta)
         (let* ((o (bfringe (car first) ta))
                (p (het o dbff)))
             (bfringe-frequencies1
              rest
              dbterms
              (hut o (+ (if p (cdr p) 0)
			(frequency (car first) dbterms))
                   dbff)
              ta))))

(dis+ind bfringe-frequencies1)

(defun bfringe-frequencies (l taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of the bdd based bipartitions present in the input list
;  of trees to the number of times it appeared in the input.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees
;     (2) taxa-list - a list of taxa

; Details: Trees in input list should not have branch lengths.  Trees should
;          all be ordered according to the taxa list given."
  (declare (xargs :guard (and (tree-list-listp l)
                              (all-same-num-tips l))
                  :verify-guards nil))
  (let ((dbterms (hshrink-alist (replete-trees-list-top l)
                                'replete-trees-list-top))
        (ta (build-fast-alist-from-alist
             (taxa-list-to-tree-alist taxa-list)
             'taxa-tree-alist
             )))
    (hshrink-alist (bfringe-frequencies1 dbterms dbterms nil ta)
		   'dbterms)))

(in-theory (disable bfringe-frequencies))

(defun btrees-to-fringes (fringe-list full-taxa-list-tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the list based version of bdd based bipartitions given.~/
;  ~/
;  Arguments:
;     (1) fringe-list - a list of bdd based bipartitions
;     (2) full-taxa-list-tree - a binary tree based version of the taxa list

;  Details: The bdd based bipartitions must each have a depth less than that of
;           the full-taxa-list-tree.  The resulting list based bipartitions will
;           have the taxa given in the full-taxa-list-tree. "
  (declare (xargs :guard (and (balanced-tree
                               full-taxa-list-tree)
                              (good-depths fringe-list
                                           full-taxa-list-tree))
                  :verify-guards nil))
  (if (consp fringe-list)
      (cons (btree-to-fringe (car fringe-list)
                             full-taxa-list-tree)
            (btrees-to-fringes (cdr fringe-list) full-taxa-list-tree))
    nil))

(defthm btrees-to-fringes-when-not-consp
  (implies (not (consp fringe-list))
           (equal (btrees-to-fringes fringe-list ftlt)
                  nil)))

(defthm btrees-to-fringes-of-consp
  (equal (btrees-to-fringes (cons first rest) ftlt)
         (cons (btree-to-fringe first ftlt)
               (btrees-to-fringes rest ftlt))))

(dis+ind btrees-to-fringes)

(defun merge-bdd-fringes (l1 l2 full-taxa-list-tree taxon-index-alist)
  (declare (xargs :measure (+ (acl2-count l1)
                              (acl2-count l2))
                  :guard (and (good-taxon-index-halist taxon-index-alist)
                              (consp full-taxa-list-tree)
                              (good-depths l1 full-taxa-list-tree)
                              (good-depths l2 full-taxa-list-tree)
                              (balanced-tree full-taxa-list-tree)
                              (subset-list (btrees-to-fringes
                                            l1
                                            full-taxa-list-tree)
                                           (get-taxa-from-taxon-index
                                            taxon-index-alist))
                              (subset-list (btrees-to-fringes
                                            l2
                                            full-taxa-list-tree)
                                           (get-taxa-from-taxon-index
                                            taxon-index-alist))
                              (not (member-gen nil l1))
                              (not (member-gen nil l2))
                              )
                  :verify-guards nil))
  (cond
   ((atom l1) l2)
   ((atom l2) l1)
   (t (let ((len-car-l1 (btree-to-fringe-length (car l1) full-taxa-list-tree))
            (len-car-l2 (btree-to-fringe-length (car l2) full-taxa-list-tree)))
        (cond ((or (> len-car-l1 len-car-l2)
                   (and (= len-car-l1 len-car-l2)
                        (< (cdr (het (btree-fringe-first (car l1)
                                                         full-taxa-list-tree)
                                     taxon-index-alist))
                           (cdr (het (btree-fringe-first (car l2)
                                                         full-taxa-list-tree)
                                     taxon-index-alist)))))
               (cons (car l1)
                     (merge-bdd-fringes
                      (cdr l1)
                      l2
                      full-taxa-list-tree taxon-index-alist)))
              (t
               (cons (car l2)
                     (merge-bdd-fringes
                      l1
                      (cdr l2)
                      full-taxa-list-tree taxon-index-alist))))))))

(defthm merge-bdd-fringes-when-not-consp-l1
  (implies (not (consp l1))
           (equal (merge-bdd-fringes l1 l2 ftlt tia)
                  l2)))

(defthm merge-bdd-fringes-when-not-consp-l2
  (implies (not (consp l2))
           (equal (merge-bdd-fringes l1 l2 ftlt tia)
                  (if (consp l1) l1 l2))))

(defthm merge-bdd-fringes-of-consp
  (equal (merge-bdd-fringes (cons first rest)
                            (cons first1 rest1) ftlt tia)
         (let ((len-car-l1 (btree-to-fringe-length
                            first ftlt))
               (len-car-l2 (btree-to-fringe-length first1 ftlt)))
           (cond ((or (> len-car-l1 len-car-l2)
                      (and (= len-car-l1 len-car-l2)
                           (< (cdr (het (btree-fringe-first first
                                                            ftlt)
                                        tia))
                              (cdr (het (btree-fringe-first first1
                                                            ftlt)
                                        tia)))))
                  (cons first (merge-bdd-fringes rest
                                                 (cons first1 rest1)
                                                 ftlt tia)))
                 (t
                  (cons first1
                        (merge-bdd-fringes (cons first rest)
                                           rest1
                                           ftlt tia)))))))

(dis+ind merge-bdd-fringes)

(defun sort-bdd-fringes (bdd-fringes full-taxa-list-tree taxon-index-alist)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the given list of bdd based bipartitions sorted by length of implied
;  list based bipartitions.~/
;  ~/
;  Arguments:
;     (1) bdd-fringes - a list of bdd based bipartitions
;     (2) full-taxa-list-tree - a binary tree based version of the taxa list
;     (3) taxon-index-alist - a mapping of taxa names to integers

; Details: Depth of each of the bdd based bipartitions must be less than that of
;          the full-taxa-list-tree.  The taxa names in the full-taxa-list-tree
;          must match those present as keys in the taxon-index-alist. "
  (declare (xargs
            :guard
            (and (good-depths bdd-fringes full-taxa-list-tree)
                 (good-taxon-index-halist taxon-index-alist)
                 (balanced-tree full-taxa-list-tree)
                 (subset-list (btrees-to-fringes
                               bdd-fringes
                               full-taxa-list-tree)
                              (get-taxa-from-taxon-index
                               taxon-index-alist))
                 (consp full-taxa-list-tree)
                 (not (member-gen nil bdd-fringes)))
            :verify-guards nil
            ))

  (cond ((or (atom bdd-fringes)
             (atom (cdr bdd-fringes)))
         bdd-fringes)
        (t (merge-bdd-fringes
            (sort-bdd-fringes (odds-gen bdd-fringes)
                              full-taxa-list-tree taxon-index-alist)
            (sort-bdd-fringes (evens-gen bdd-fringes)
                              full-taxa-list-tree taxon-index-alist)
            full-taxa-list-tree
            taxon-index-alist))))

(defthm sort-bdd-fringes-when-not-consp
  (implies (or (not (consp bdd-fringes))
               (not (consp (cdr bdd-fringes))))
           (equal (sort-bdd-fringes bdd-fringes ftlt tia)
                  bdd-fringes)))

(defthm sort-bdd-fringes-of-consp
  (equal (sort-bdd-fringes (cons first (cons first1 rest)) ftlt tia)
         (merge-bdd-fringes
          (sort-bdd-fringes (evens-gen (cons first1 rest)) ftlt tia)
          (sort-bdd-fringes (cons first (evens-gen rest)) ftlt tia)
          ftlt tia)))

(dis+ind sort-bdd-fringes)

;; Second attempt is much more efficient, but does same thing
(defun make-good-fringes (x full-taxa-list-tree taxa-list)
  (declare (xargs :guard (balanced-tree full-taxa-list-tree)
                  :verify-guards nil))
  (if (consp x)
      (if (and (<= (depth (car x)) (depth full-taxa-list-tree))
               (not (equal (car x) nil))
               (subset (btree-to-fringe (car x)
                                        full-taxa-list-tree)
                       taxa-list))
          (cons (car x) (make-good-fringes (cdr x)
                                           full-taxa-list-tree
                                           taxa-list))
        (make-good-fringes (cdr x)
                           full-taxa-list-tree
                           taxa-list))
    nil))

(defthm make-good-fringes-when-not-consp
  (implies (not (consp x))
           (equal (make-good-fringes x ftlt taxa-list)
                  nil)))

(defthm make-good-fringes-of-consp
  (equal (make-good-fringes (cons first rest) ftlt taxa-list)
         (if (and (<= (depth first) (depth ftlt))
                  (not (equal first nil))
                  (subset (btree-to-fringe first ftlt)
                          taxa-list))
             (cons first (make-good-fringes rest ftlt taxa-list))
           (make-good-fringes rest
                              ftlt
                              taxa-list))))

(dis+ind make-good-fringes)

(defun term-to-bfringes (term taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the bdd based list of bipartitions for the input tree.~/
;  ~/
;  Arguments:
;     (1) term - a tree
;     (2) taxa-list - a list of taxa

;  Details: Taxa names in the given tree must be a subset of those present in
;           the taxa-list given.  Tree input should not have branch lengths."
  (declare (xargs :guard (and (treep term)
                              (consp term)
                              (<= 2 (len taxa-list))
                              (int-symlist taxa-list))
                  :verify-guards nil))
  (let* ((bdd-fringes (strip-cars-gen (bfringe-frequencies
                                       (list term)
                                       taxa-list)))
         (full-taxa-list-tree (build-taxa-list-tree taxa-list))
         (taxon-index-alist (taxa-list-to-taxon-index taxa-list)))
    ;; just to make guards easier, cause I can't deal with this
    ;; anymore, I've added the wrappers around bdd-fringes...
    ;; *should* be able to prove from just adding to guards
    ;; (taspip t term) and (subset (mytips term) taxa-list)

    ;; This version does each strip one at a time
    ;(sort-bdd-fringes (remove-nils
    ;                   (make-subset-list
    ;                    (get-good-depths bdd-fringes
    ;                                     full-taxa-list-tree)
    ;                    full-taxa-list-tree
    ;                    taxa-list))
    ;                  full-taxa-list-tree
    ;                  taxon-index-alist)))

    ;; This version does all the strips at once (more efficient)
    (sort-bdd-fringes (make-good-fringes bdd-fringes
                                         full-taxa-list-tree
                                         taxa-list)
                      full-taxa-list-tree
                      taxon-index-alist)))
