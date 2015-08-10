(in-package "ACL2")

(include-book "../code/fringes/fringes-guards")
(include-book "../code/tree-manip/merge-based-sort")
(include-book "../code/tree-manip/mv-root")

;; returns top level piece of tree containing particular taxon
(defun get-top-containing-subtree-of-taxon (taxon tree)
  (declare (xargs :guard (member-gen taxon (mytips tree))))
  (if (consp tree)
      (if (member-gen taxon (mytips (car tree)))
          (car tree)
        (get-top-containing-subtree-of-taxon taxon (cdr tree)))
    ;; given member-gen taxon of tips, should be appropriate tip
    (if (equal tree taxon)
        tree
      nil)))

;; helper for brlen version
(defun get-top-containing-subtree-of-taxon-brlens-helper (taxon tree)
  (declare (xargs :guard t))
  (if (consp tree)
      (if (member-gen taxon (mytips-brlens (car tree)))
          (car tree)
        (get-top-containing-subtree-of-taxon-brlens-helper taxon (cdr tree)))
    nil))

;; returns top level piece of tree with brlens containing particular taxon
;; Would really like treep-num-brlens input
(defun get-top-containing-subtree-of-taxon-brlens (taxon tree)
  (declare (xargs :guard t))
  (if (consp tree)
      (if (consp (cdr tree))
          (get-top-containing-subtree-of-taxon-brlens-helper taxon tree)
        (get-top-containing-subtree-of-taxon-brlens-helper taxon (car tree)))
    nil))


(defthm container-no-larger
  (<= (acl2-count (get-top-containing-subtree-of-taxon
                   taxon tree))
      (acl2-count tree))
  :rule-classes :linear)

(defthm container-no-larger-brlens
  (<= (acl2-count (get-top-containing-subtree-of-taxon-brlens
                   taxon tree))
      (acl2-count tree))
  :rule-classes :linear)


;; Gives path length assuming unit lengths from root to taxon
(defun len-path-to-taxon (taxon tree acc)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns path length from root to taxon indicated assuming unit lengths on
;  each branch.~/
;  ~/
;  Arguments:
;    (1) taxon - a taxon name
;    (2) tree - a tree
;    (3) acc - accumulator (initially 0)
;
;  "
  (declare (xargs :guard (acl2-numberp acc)))
  (if (taspip t tree)
      (if (member-gen taxon (mytips tree))
          (if (or (member-gen taxon tree)
                  (equal taxon tree))
              acc
            (let ((container
                   (get-top-containing-subtree-of-taxon
                    taxon tree)))
              (len-path-to-taxon taxon
                                 container
                                 (1+ acc))))
        nil)
    'need-valid-tree))

;; Gives path length from root to taxon using brlens
(defun len-path-to-taxon-brlens (taxon tree acc)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns path length from root to taxon indicated using branch lengths given
;  in tree on each branch.~/
;  ~/
;  Arguments:
;    (1) taxon - a taxon name
;    (2) tree - a tree with branch lengths
;    (3) acc - accumulator (initially 0)
;
;  "
  (declare (xargs :guard (acl2-numberp acc)
                  :hints (("Subgoal 2.1" :in-theory (disable
                                                     container-no-larger-brlens)
                           :use (:instance container-no-larger-brlens
                                           (tree (cdr tree))))
                          ("Subgoal 1" :in-theory (disable
                                                   container-no-larger-brlens)
                           :use (:instance container-no-larger-brlens
                                           (tree (car tree)))))))
  (if (member-gen taxon (mytips-brlens tree))
      (if (member-gen taxon tree) ;;tip
          (if (acl2-numberp (cdr tree))
              (+ acc (cdr tree))
            'need-treep-num-brlens)
        (let ((container
               (get-top-containing-subtree-of-taxon-brlens
                taxon tree)))
          (if (consp tree)
              (if (acl2-numberp (cdr tree))
                  (len-path-to-taxon-brlens taxon
                                            container
                                            (+ acc (cdr tree)))
                (len-path-to-taxon-brlens taxon container acc))
            'need-treep-num-brlens)))
    'need-taxon-in-tree))

;; helper function for least common ancestor
(defun least-common-ancestor (flg a b tree curLeast)
  (declare (xargs :guard t
                  :measure (tree-measure tree flg)))
  (if (consp tree)
      (if flg
          (if (and (member-gen a (mytips tree))
                   (member-gen b (mytips tree)))
              (least-common-ancestor nil a b tree tree)
            curLeast)
        (if (and (member-gen a (mytips (car tree)))
                 (member-gen b (mytips (car tree))))
            (least-common-ancestor t a b (car tree) (car tree))
          (least-common-ancestor nil a b (cdr tree) curLeast)))
    curLeast))

;; only makes sense on a rooted tree
(defun lca (a b tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Returns least common ancestor of taxa a and b in tree.~/
;  ~/
;  Arguments:
;    (1) a - a taxon name
;    (2) b - a taxon name
;    (3) tree - a tree
;
;  Details: Returns empty tree if no common ancestor exists."
  (declare (xargs :guard t))
  (least-common-ancestor t a b tree nil))

(defthm taspip-get-containing
  (implies (and (member-gen taxon (mytips tree))
                (taspip flg tree))
           (taspip t (get-top-containing-subtree-of-taxon
                      taxon tree))))

(defthm get-containing-works
  (implies (member-gen taxon (mytips tree))
           (member-gen taxon
                       (mytips
                        (get-top-containing-subtree-of-taxon
                         taxon
                         tree)))))

(defthm len-path-number
  (implies (and (taspip t tree)
                (member-gen taxon (mytips tree))
                (acl2-numberp acc))
           (acl2-numberp (len-path-to-taxon taxon tree acc))))

(defthm not-either-gives-acc
  (implies (and (not (member-gen a (mytips tree)))
                (not (member-gen b (mytips tree))))
           (equal (least-common-ancestor flg a b tree acc)
                  acc)))

(defthm not-both-gives-acc
  (implies (and (member-gen a (mytips tree))
                (not (member-gen b (mytips tree))))
           (equal (least-common-ancestor flg a b tree acc)
                  acc)))

(defthm not-both-gives-acc-2
  (implies (and (member-gen b (mytips tree))
                (not (member-gen a (mytips tree))))
           (equal (least-common-ancestor flg a b tree acc)
                  acc)))

(defthm consp-lca
  (implies (and (not (equal a b))
                (consp acc)
                (member-gen a (mytips tree))
                (member-gen b (mytips tree)))
           (consp (least-common-ancestor flg a b tree acc))))

(defthm not-equal-member-gives-consp
  (implies (and (not (equal a b))
                (member-gen a (mytips tree))
                (member-gen b (mytips tree)))
           (consp tree))
  :rule-classes :forward-chaining)

(defthm consp-lca-2
  (implies (and (not (equal a b))
                (member-gen a (mytips tree))
                (member-gen b (mytips tree)))
           (consp (lca a b tree))))

(defthm taspip-lca
  (implies (and (taspip flg tree)
                (taspip flg acc)
                (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (not (equal a b)))
           (taspip flg (least-common-ancestor flg a b tree acc))))

(defthm taspip-t-lca
  (implies (and (taspip t tree)
                (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (not (equal a b)))
           (taspip t (least-common-ancestor t a b tree acc)))
  :hints (("Goal" :expand (least-common-ancestor t a b tree acc))))

(defthm taspip-t-lca-2
  (implies (and (taspip t tree)
                (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (not (equal a b)))
           (taspip t (lca a b tree))))

(defthm member-gen-tips-of-lca
  (implies (and (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (taspip flg tree)
                (if (not flg)
                    (member-gen a (mytips acc))
                  t)
                (not (equal a b)))
           (member-gen a (mytips
                          (least-common-ancestor flg a b tree acc)))))

(defthm member-gen-tips-of-lca-2
  (implies (and (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (taspip flg tree)
                (if (not flg)
                    (member-gen b (mytips acc))
                  t)
                (not (equal a b)))
           (member-gen b (mytips
                          (least-common-ancestor flg a b tree acc)))))

(defthm member-gen-tips-of-lca-3
  (implies (and (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (taspip t tree)
                (not (equal a b)))
           (member-gen a (mytips
                          (lca a b tree)))))

(defthm member-gen-tips-of-lca-4
  (implies (and (member-gen a (mytips tree))
                (member-gen b (mytips tree))
                (taspip t tree)
                (not (equal a b)))
           (member-gen b (mytips
                          (lca a b tree)))))

(in-theory (disable lca))

;; this assumes that the tree is rooted at a true node
(defun path-distance-no-brlens (a b tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Returns path distance between a and b in tree assuming unit branch lengths.~/
;  ~/
;  Arguments:
;    (1) a - a taxon name
;    (2) b - a taxon name
;    (3) tree - a tree
;
;  Details: Requires tree representation to be rooted at a node."
  (declare (xargs :guard (and (taspip t tree)
                              (member-gen a (mytips tree))
                              (member-gen b (mytips tree)))))
  (if (equal a b)
      0
    (let ((lca (lca a b tree)))
      (+ (len-path-to-taxon a lca 1)
         (len-path-to-taxon b lca 1)))))

(defun path-distance-brlens (a b tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Returns path distance between a and b in tree.~/
;  ~/
;  Arguments:
;    (1) a - a taxon name
;    (2) b - a taxon name
;    (3) tree - a tree with branch lengths
;
;  Details: Requires tree representation to be rooted at a node."
  (declare (xargs :guard t))
  (if (equal a b)
      0
    (let* ((lca (lca a b tree))
           (part1 (len-path-to-taxon-brlens a lca 0))
           (part2 (len-path-to-taxon-brlens b lca 0)))
      (if (and (acl2-numberp part1)
               (acl2-numberp part2))
          (+ part1 part2)
        'need-taxa-in-tree))))

(defthm len-path-rational
  (implies (and (taspip t tree)
                (member-gen taxon (mytips tree))
                (rationalp acc))
           (rationalp (len-path-to-taxon taxon tree acc))))


(defun find-max-pair-dist-help (taxon rest tree curMax)
  (declare (xargs :guard (rationalp curMax)
                  :guard-hints (("Subgoal 2'''"
                                 :in-theory (disable len-path-rational)
                                 :use ((:instance len-path-rational
                                                  (tree (lca taxon rest1 tree))
                                                  (taxon rest1)
                                                  (acc 1))
                                       (:instance len-path-rational
                                                  (tree (lca taxon rest1 tree))
                                                  (acc 1))))
                                ("Subgoal 1'''"
                                 :in-theory (disable len-path-rational)
                                 :use ((:instance len-path-rational
                                                  (tree (lca taxon rest1 tree))
                                                  (taxon rest1)
                                                  (acc 1))
                                       (:instance len-path-rational
                                                  (tree (lca taxon rest1 tree))
                                                  (acc 1)))))))
  (if (and (taspip t tree)
           (member-gen taxon (mytips tree)))
      (if (consp rest)
          (if (member-gen (car rest) (mytips tree))
              (find-max-pair-dist-help
               taxon (cdr rest) tree
               (max curMax
                    (path-distance-no-brlens taxon
                                             (car rest) tree)))
            0)
        curMax)
    0))

(defun find-max-pair-dist-help-brlens (taxon rest tree curMax)
  (declare (xargs :guard (rationalp curMax)))
  (if (consp rest)
      (let ((newMax? (path-distance-brlens taxon
                                           (car rest)
                                           tree)))
        (if (rationalp newMax?)
            (find-max-pair-dist-help-brlens taxon (cdr rest) tree
                                            (max curMax
                                                 newMax?))
          0))
    curMax))

(defthm rationalp-find-max-pair-dist-help
  (implies (rationalp curMax)
           (rationalp (find-max-pair-dist-help taxon rest tree curMax)))
  :hints (("Subgoal *1/1'5'"
           :in-theory (disable len-path-rational)
           :use ((:instance len-path-rational
                            (tree (lca taxon rest1 tree))
                            (taxon rest1)
                            (acc 1))
                 (:instance len-path-rational
                            (tree (lca taxon rest1 tree))
                            (acc 1))))))

(defun find-max-pair-dist (taxa tree curMax)
  (declare (xargs :guard (rationalp curMax)))
  (if (consp taxa)
      (find-max-pair-dist
       (cdr taxa)
       tree
       (find-max-pair-dist-help (car taxa) (cdr taxa) tree curMax))
    curMax))

(defun find-max-pair-dist-brlens (taxa tree curMax)
  (declare (xargs :guard (rationalp curMax)))
  (if (consp taxa)
      (find-max-pair-dist-brlens (cdr taxa)
                                 tree
                                 (find-max-pair-dist-help-brlens (car taxa)
                                                                 (cdr taxa)
                                                                 tree
                                                                 curMax))
    curMax))

;; makes most sense on a rooted tree
(defun get-containing-subtree-of-taxa-help (taxa tree curTree)
  (declare (xargs :guard t))
  (if (subset taxa (mytips curTree))
      (if (consp tree)
          (if (subset taxa (mytips (car tree)))
              (get-containing-subtree-of-taxa-help
               taxa (car tree)
               (car tree))
            (get-containing-subtree-of-taxa-help
             taxa (cdr tree)
             curTree))
        curTree)
    nil))

;; makes most sense on a rooted tree
(defun get-containing-subtree-of-taxa (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns subtree of tree containing each taxon in taxa.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - a tree
;
;  Details: Assumes a rooted tree with no branch lengths (see also
;           get-containing-subtree-of-taxa-brlens)."
  (declare (xargs :guard t))
  (get-containing-subtree-of-taxa-help taxa tree tree))

(defun get-containing-subtree-of-taxa-brlens (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns subtree of tree containing each taxon in taxa.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - a tree
;
;  Details: Assumes a rooted tree.  Does not preserve branch lengths if
;           present (see also get-containing-subtree-of-taxa)."
  (declare (xargs :guard t))
  (get-containing-subtree-of-taxa taxa (remove-brlens tree)))

;; again makes most sense in rooted sense
(defun monophyletic? (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if set of taxa is monophyletic in tree.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - a tree
;
;  Details: Assumes a rooted tree with no branch lengths (see also
;           monophyletic?-brlens)."
  (declare (xargs :guard t))
  (let ((subtree (get-containing-subtree-of-taxa taxa tree)))
    (if (perm (mytips subtree) taxa)
        subtree
      nil)))

;; requires rooted input
(defun monophyletic?-brlens (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if set of taxa is monophyletic in tree.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - a tree
;
;  Details: Assumes a rooted tree.  Does not preserve branch lengths if
;           present (see also monophyletic?-brlens)."
  (declare (xargs :guard t))
  (monophyletic? taxa (remove-brlens tree)))

;; so for unrooted trees, is there a way to root that would make
;; set monophyletic?
(defun check-for-fringe-membership (taxa not-taxa bfringes)
  (declare (xargs :guard t))
  (if (consp bfringes)
      (if (or (equal taxa (car bfringes))
              (equal not-taxa (car bfringes)))
          t
        (check-for-fringe-membership taxa not-taxa (cdr bfringes)))
    nil))

(defun fringe-based-monophyletic-check (taxa tree taxa-list)
  (declare (xargs :guard t))
  (if (and (treep tree)
           (consp tree)
           (<= 2 (len taxa-list))
           (int-symlist taxa-list)
           (consp taxa)
           (treep taxa)
           (consp (difference taxa-list taxa))
           (treep (difference taxa-list taxa)))
      (let ((bfringes (term-to-bfringes tree taxa-list))
            (taxa-fringe (term-to-bfringes taxa taxa-list))
            (not-taxa-fringe (term-to-bfringes
                              (difference taxa-list taxa)
                              taxa-list)))
        (check-for-fringe-membership (car taxa-fringe)
                                     (car not-taxa-fringe)
                                     bfringes))
    (perm taxa tree)))

(defun root-to-monophyletic? (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if it is possible to root tree such that taxa is monophyletic
;  in tree.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - an unrooted tree
;
;  Details: Assumes an unrooted tree with no branch lengths (see also
;           root-to-monophyletic?-brlens). Does not return monophyletic
;           structure if present."
  (declare (xargs :guard t))
  (if (consp tree)
      (if (or (consp (car tree))
              (member-gen (car tree) taxa))
          ;; need to do more technical search
          (fringe-based-monophyletic-check taxa tree (mytips tree))
        ;; otherwise, pretend we're in the rooted case
        (monophyletic? taxa (cdr tree)))
    'not-unrooted-tree))

(defun root-to-monophyletic?-brlens (taxa tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if it is possible to root tree such that taxa is monophyletic
;  in tree.~/
;  ~/
;  Arguments:
;    (1) taxa - a list of taxa names
;    (2) tree - an unrooted tree
;
;  Details: Assumes an unrooted tree.  Does not preserve structure (see also
;           root-to-monophyletic?)."
  (declare (xargs :guard t))
  (root-to-monophyletic? taxa (remove-brlens tree)))

(defun project (flg keep x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tree on taxa in keep implied by x.~/
;  ~/
;  Arguments:
;    (1) flg - non-nil for a single tree,
;              nil for a set of trees
;    (2) keep - a list of taxa names
;    (2) x - a tree
;
;  Details: Does not matter if branch lengths are present or not, but
;           resulting trees will not have branch lengths."
  (declare (xargs :guard t
                  :measure (tree-measure x flg)))
  (if flg
      (if (atom x)
          (if (member-gen x keep)
              x
            nil)
        (let ((lst (project nil keep x)))
          (if (atom lst)
              nil
            (if (atom (cdr lst))
                (car lst) lst))))
    (if (atom x)
        nil
      (let ((term (project t keep (car x)))
            (rest (project nil keep (cdr x))))
        (if (null term) rest (cons term rest))))))


(defthm tip-p-through-project
  (implies (and (tip-p x)
                (not (equal (project flg keep x)
                            nil)))
           (tip-p (project flg keep x))))

;Not sure whether this rule or one above is more useful
(defthm tip-p-through-project-2
  (implies (and (tip-p x)
                (not (tip-p (project flg keep x))))
           (equal (project flg keep x)
                  nil)))

(defthm project-produces-treep
  (and (implies (treep x)
                (or (treep (project t keep x))
                    (equal (project t keep x)
                           nil)))
       (implies (tree-listp x)
                (tree-listp (project nil keep x))))
  :rule-classes nil
  :hints (("Goal" :induct (tree-p-induction x flg))))

(defthm treep-through-project
  (implies (and (treep x)
                (not (equal (project t keep x)
                            nil)))
           (treep (project t keep x)))
  :hints (("Goal" :use
           (:instance project-produces-treep))))

(defthm tree-listp-through-project
  (implies (tree-listp x)
           (tree-listp (project nil keep x)))
  :hints (("Goal" :use
           (:instance project-produces-treep))))

;(defthm tree-listp-through-project2
;  (implies (treep x)
;           (tree-listp (project flg keep x))))

(defun project-with-normalize (rooted? keep tree taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the normalized tree on taxa in keep implied by x.~/
;  ~/
;  Arguments:
;    (1) rooted? - non-nil for a rooted tree,
;                  nil for an unrooted tree
;    (2) keep - a list of taxa names
;    (3) tree - a tree
;    (4) taxa-list - a list of taxa names
;
;  Details: Assumes tree does not have branch lengths.  Resulting tree will be
;           ordered according to the taxa list given, and if the tree is
;           unrooted, its representation will be rooted at the node at which
;           the least taxon is connected to the rest of the tree."
  (declare (xargs :guard t))
  (if (and (good-taxon-index-halist (taxa-list-to-taxon-index taxa-list))
           (taspip t (project t keep tree))
           (subset (mytips (project t keep tree))
                   (get-taxa-from-taxon-index
                    (taxa-list-to-taxon-index taxa-list))))
      (let ((ordered-projection
             (order-by-merge (project t keep tree)
                             (taxa-list-to-taxon-index taxa-list))))
        (if rooted?
            ordered-projection
          (mv-root ordered-projection (taxa-list-to-taxon-index taxa-list))))
    "Error: bad arguments in project-with-normalize"))

#|| EXAMPLES:

(len-path-to-taxon 'a '((a v) (d g)) 0)
(len-path-to-taxon 'f
                   '((((a b) c) (d e)) (f ((g h) (i j))))
                   1)
(len-path-to-taxon 'c
                   '((((a b) c) (d e)) (f ((g h) (i j))))
                   1)

(lca 'a 'b '(((a v) (b c)) (d f)))
(lca 'a 'y '((a v) (d g)))
(lca 'a 'x '((a . 3) (((b . 2) (x . 4)) . 5)))
(lca 'b 'x '((a . 3) (((b . 2) (x . 4)) . 5)))

(path-distance-no-brlens
 'a 'b '((((a b) c) (d e)) (f ((g h) (i j)))))
(path-distance-no-brlens ;rooted
 'a 'g '((((a b) c) (d e)) (f ((g h) (i j)))))
(path-distance-no-brlens ; unrooted
 'a 'g '(((a b) c) (d e) (f ((g h) (i j)))))

(get-containing-subtree-of-taxa
 '(a b g)
 '((((a b) c) (d e)) (f ((g h) (i j)))))
(get-containing-subtree-of-taxa
 '(a d)
 '((((a b) c) (d e)) (f ((g h) (i j)))))
(get-containing-subtree-of-taxa-brlens
 '(a b)
 '((a . 3) (((b . 2) (x . 4)) . 5)))
(get-containing-subtree-of-taxa-brlens
 '(b c)
 '((a . 4) ((b . 4) (c . 2)) (e . g)))

(monophyletic? '(a d e) '(((a b) c) (d e) (f ((g h) (i j)))))
(monophyletic? '(j h i g) '(((a b) c) (d e) (f ((g h) (i j)))))
(monophyletic?-brlens '(b e) '((a . 4) ((b . 4) (c . 2)) (e . g)))
(monophyletic?-brlens '(b c) '((a . 4) (((b . 4) (c . 2)) . 1) (e . g)))
(monophyletic? '(a b c d e f)
               '(((a b) c) (d e) (f ((g h) (i j)))))

(root-to-monophyletic? '(a b c d e f)
                       '(((a b) c) (d e) (f ((g h) (i j)))))
(root-to-monophyletic?-brlens '(a b c d e f)
                       '(((a b) c) (((d . 2) (e . 5)) . 5)
                         (f ((g h) (i j)))))

(project t '(a e g j) '(((a b) c) (d e) (f ((g h) (i j)))))
(project t '(a b f g j) '(((a b) c) (d e) (f ((g h) (i j)))))
(project t '(a b) '((a . 4) (((b . 4) (c . 2)) . 1) (e . g)))
(project t '(a e g j)
         '(((((a . 4) b) . 3) c) ((d . 3) e)
           ((f . 3) ((((g . 3) (h . 4)) . 5) (i (j . 7))))))

(project-with-normalize
 t '(a e g j)
 '(((((a . 4) b) . 3) c) ((d . 3) e)
   ((f . 3) ((((g . 3) (h . 4)) . 5) (i (j . 7)))))
 '(g e a j))


(treep-num-brlens '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                    (((d . 3) (e . 5)) . 6)
                    (((f . 3)
                      (((((g . 3) (h . 4)) . 5)
                        (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                    ))

(len-path-to-taxon-brlens 'f '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                    (((d . 3) (e . 5)) . 6)
                    (((f . 3)
                      (((((g . 3) (h . 4)) . 5)
                        (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                    ) 0)

(path-distance-brlens 'a 'c '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                    (((d . 3) (e . 5)) . 6)
                    (((f . 3)
                      (((((g . 3) (h . 4)) . 5)
                        (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                    ))

(path-distance-brlens 'a 'g '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                    (((d . 3) (e . 5)) . 6)
                    (((f . 3)
                      (((((g . 3) (h . 4)) . 5)
                        (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                    ))

(path-distance-brlens 'b 'g '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                    (((d . 3) (e . 5)) . 6)
                    (((f . 3)
                      (((((g . 3) (h . 4)) . 5)
                        (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                    ))


||#
