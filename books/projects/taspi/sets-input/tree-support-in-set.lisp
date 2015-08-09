(in-package "ACL2")

(include-book "../code/build/build-term-guards")

;; only correct if ordered according to same taxa-list
;; and mytips perm same taxa-list
(defun not-conflicting (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if the given tree does not conflict with any of the trees in the
;  set given.~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Does not allow branch lengths (see also not-conflicting-brlens).
;           Computation is only accurate if all trees are ordered according to
;           the same taxa list, and the taxa names in each tree are exactly
;           those given in the taxa list."
  (declare (xargs :guard t))
  (if (consp set)
      (if (and (treep tree)
               (treep (car set))
               (consp (car set))
               (consp tree)
               (<= 2 (len taxa-list))
               (int-symlist taxa-list))
          (let ((tree-fringes (term-to-bfringes tree taxa-list))
                (curFringes (term-to-bfringes (car set)
                                              taxa-list)))
            (if (and (good-depths (app tree-fringes curFringes)
                                  (build-taxa-list-tree taxa-list))
                     (not (member-gen nil (app tree-fringes curFringes)))
                     (subset-list (btrees-to-fringes (app tree-fringes
                                                          curFringes)
                                                     (build-taxa-list-tree
                                                      taxa-list))
                                  (taspi-rev taxa-list)))
                (if (q-no-conflicts-list
                     (sort-bdd-fringes (app tree-fringes curFringes)
                                       (build-taxa-list-tree taxa-list)
                                       (taxa-list-to-taxon-index taxa-list)))
                    (cons (car set)
                          (not-conflicting tree (cdr set) taxa-list))
                  (not-conflicting tree (cdr set) taxa-list))
              'bad-tree-fringes-in-not-conflicting))
        'bad-tree-comparison-in-not-conflicting)
    nil))

(defun not-conflicting-brlens (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if the given tree does not conflict with any of the trees in the
;  set given.~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Allows branch lengths (see also not-conflicting).  Branch lengths
;           are not preserved in the trees returned.
;           Computation is only accurate if all trees are ordered according to
;           the same taxa list, and the taxa names in each tree are exactly
;           those given in the taxa list."
  (declare (xargs :guard t))
    (let ((trees-no-brlens (remove-brlens-list set))
          (tree-no-brlens (remove-brlens tree)))
      (not-conflicting tree-no-brlens
                       trees-no-brlens
                       taxa-list)))

(defun trees-supporting-all-branches (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from input set that support all branches in input tree~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (2) taxa-list - a list of taxa names
;
;  Details: Does not allow branch lengths
;           (see trees-supporting-all-branches-brlens).  Trees returned may be
;           more resolved than the input tree, but not less."
  (declare (xargs :guard t))
  (if (consp set)
      (if (and (treep tree)
               (treep (car set))
               (consp (car set))
               (consp tree)
               (<= 2 (len taxa-list))
               (int-symlist taxa-list))
          (let ((tree-fringes (term-to-bfringes tree taxa-list))
                (curFringes (term-to-bfringes (car set)
                                              taxa-list)))
            (if (subset tree-fringes curFringes)
                (cons (car set)
                      (trees-supporting-all-branches
                       tree (cdr set) taxa-list))
              (trees-supporting-all-branches tree (cdr set) taxa-list)))
        'bad-tree-comparison-in-trees-supporting-all-branches)
    nil))

(defun trees-supporting-all-branches-brlens (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;   ":Doc-Section TASPI
;  Returns trees from input set that support all branches in input tree
;  while allowing branch lengths~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (2) taxa-list - a list of taxa names
;
;  Details: Allows branch lengths (see trees-supporting-all-branches).  Trees
;           returned may be more resolved than the input tree, but not less.
;           Branch lengths are not preserved in trees returned."
  (declare (Xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list set))
        (tree-no-brlens (remove-brlens tree)))
    (trees-supporting-all-branches tree-no-brlens
                                   trees-no-brlens
                                   taxa-list)))

(defun count-support (tree-fringes comp-fringes acc)
  (declare (xargs :guard (integerp acc)))
  (if (consp tree-fringes)
      (if (member-gen (car tree-fringes) comp-fringes)
          (count-support (cdr tree-fringes) comp-fringes (1+ acc))
        (count-support (cdr tree-fringes) comp-fringes acc))
    acc))

(defun how-much-support-for-branches-in-tree (tree compTree taxa-list)
  (declare (xargs :guard t))
  (if (and (treep tree)
           (treep compTree)
           (consp compTree)
           (consp tree)
           (<= 2 (len taxa-list))
           (int-symlist taxa-list))
      (let ((tree-fringes (term-to-bfringes tree taxa-list))
            (comp-fringes (term-to-bfringes compTree taxa-list)))
        (count-support tree-fringes comp-fringes 0))
    0))

(defthm integerp-count-support
  (implies (integerp acc)
           (integerp (count-support fringe1 fringe2 acc))))

(defthm integerp-how-much-support
  (integerp (how-much-support-for-branches-in-tree tree compTree taxa-list)))

(defthm integerp->rationalp
  (implies (integerp x)
           (rationalp x)))

(defthm rationalp-how-much-support
  (rationalp (how-much-support-for-branches-in-tree tree compTree taxa-list)))

(defun get-trees-with-count-greater (x tree set taxa-list)
  (declare (xargs :guard (rationalp x)))
  (if (consp set)
      (if (and (treep (car set))
               (treep tree)
               (consp (car set))
               (consp tree)
               (<= 2 (len taxa-list))
               (int-symlist taxa-list))
          (if (<= x (how-much-support-for-branches-in-tree tree
                                                           (car set)
                                                           taxa-list))
              (cons (car set)
                    (get-trees-with-count-greater x tree
                                                  (cdr set)
                                                  taxa-list))
            (get-trees-with-count-greater x tree
                                          (cdr set) taxa-list))
        'bad-comparison-in-get-trees-with-count-greater)
    nil))

(defun trees-supporting-x-proportion-of-branches-in-tree
  (x tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns trees from input set that support x proportion of branches in input tree~/
;  ~/
;  Arguments:
;    (1) x - a rational number indicating support level
;    (2) tree - a tree
;    (3) set - a list of trees
;    (4) taxa-list - a list of taxa names

;  Details: Does not allow branch lengths (see
;           trees-supporting-x-proportion-of-branches-in-tree-brlens).  All
;           trees involved should have the taxa list given."
  (declare (xargs :guard (rationalp x)))
  (if (and (treep tree)
           (consp tree)
           (<= 2 (len taxa-list))
           (int-symlist taxa-list))
      (let ((fringes (term-to-bfringes tree taxa-list)))
        (let ((needed-count (* (len fringes) (/ x 100))))
          (get-trees-with-count-greater needed-count
                                     tree set taxa-list)))
    'bad-comparison-in-trees-supporting-x-proportion-of-branches-in-tree))

(defun trees-supporting-x-proportion-of-branches-in-tree-brlens
  (x tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;   ":Doc-Section TASPI
;  Returns trees from input set that support x proportion of branches in input
;  tree while allowing branch lengths~/
;  ~/
;  Arguments:
;    (1) x - a rational number indicating support level
;    (2) tree - a tree
;    (3) set - a list of trees
;    (4) taxa-list - a list of taxa names

;  Details: Does not allow branch lengths (see
;           trees-supporting-x-proportion-of-branches-in-tree-brlens).  All
;           trees involved should have the taxa list given. Trees returned do
;           not preserve branch lengths. "
  (declare (xargs :guard (rationalp x)))
  (let ((trees-no-brlens (remove-brlens-list set))
        (tree-no-brlens (remove-brlens tree)))
    (trees-supporting-x-proportion-of-branches-in-tree
     x tree-no-brlens
     trees-no-brlens
     taxa-list)))

;; need branch to be a bfringe from a tree with same taxa-list as
;;  set
(defun branch-support-trees (branch set taxa-list)
  (declare (xargs :guard t))
  (if (consp set)
      (if (and (treep (car set))
               (consp (car set))
               (<= 2 (len taxa-list))
               (int-symlist taxa-list))
          (let ((curFringes (term-to-bfringes (car set) taxa-list)))
            (if (member-gen branch curFringes)
                (cons (car set)
                      (branch-support-trees branch (cdr set) taxa-list))
              (branch-support-trees branch (cdr set) taxa-list)))
        'bad-tree-comparison)
    nil))

(defun proportion-of-trees-supporting-branch (branch set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns proportion of trees from input set that support the input branch~/
;  ~/
;  Arguments:
;    (1) branch - a bdd based bipartition
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: The branch must have been created using the same taxa list as
;           given, and the trees must also have this same taxa list.
;           Does not allow branch lengths (see
;           proportion-of-trees-supporting-branch-brlens)."
  (declare (xargs :guard t))
  (if (< 0 (len set))
      (/ (len (branch-support-trees branch set taxa-list))
         (len set))
    0))

(defun proportion-of-trees-supporting-branch-brlens (branch set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;   ":Doc-Section TASPI
;  Returns proportion of trees from input set with branch lengths
;  that support the input branch~/
;  ~/
;  Arguments:
;    (1) branch - a bdd based bipartition
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: The branch must have been created using the same taxa list as
;           given, and the trees must also have this same taxa list.
;           Allow branch lengths (see also
;           proportion-of-trees-supporting-branch)."
  (declare (xargs :guard t))
  (if (< 0 (len set))
      (/ (len (branch-support-trees branch (remove-brlens-list set) taxa-list))
         (len set))
    0))

(defun make-tree-support-for-branches (fringes set taxa-list)
  (declare (xargs :guard t))
  (if (consp fringes)
      (cons (cons (car fringes)
                  (branch-support-trees (car fringes)
                                        set
                                        taxa-list))
            (make-tree-support-for-branches (cdr fringes)
                                            set taxa-list))
    nil))

(defun branch-by-branch-tree-support (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Returns a listing of branches in the input tree and the trees supporting
;  that branch from the input set~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: All trees must have the taxa list given.  Bipartitions returned
;           are bdd based.
;           Does not allow branch lengths (see
;           branch-by-branch-tree-support-brlens)."
  (declare (xargs :guard t))
  (if (and (treep tree)
           (consp tree)
           (<= 2 (len taxa-list))
           (int-symlist taxa-list))
      (let ((fringes (term-to-bfringes tree taxa-list)))
        (make-tree-support-for-branches fringes set taxa-list))
    'bad-input-tree))

(defun branch-by-branch-tree-support-brlens (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a listing of branches in the input tree and the trees supporting
;  that branch from the input set~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: All trees must have the taxa list given.  Bipartitions returned
;           are bdd based.
;           Allows branch lengths (see branch-by-branch-tree-support) but the
;           trees returned do not have branch lengths."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list set))
        (tree-no-brlens (remove-brlens tree)))
    (branch-by-branch-tree-support tree-no-brlens
                                   trees-no-brlens
                                   taxa-list)))

(defun make-proportion-support-for-branches (fringes set taxa-list)
  (declare (xargs :guard t))
  (if (consp fringes)
      (cons (cons (car fringes)
                  (proportion-of-trees-supporting-branch
                   (car fringes) set taxa-list))
            (make-proportion-support-for-branches (cdr fringes)
                                                  set taxa-list))
    nil))

(defun branch-by-branch-proportion-support (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a listing of branches in the input tree and the proportion of trees
;  in the input set that support that branch~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: All trees must have the taxa list given.  Bipartitions returned
;           are bdd based.  Does not allow branch lengths
;           (see branch-by-branch-proportion-support).  "
  (declare (xargs :guard t))
  (if (and (treep tree)
           (consp tree)
           (<= 2 (len taxa-list))
           (int-symlist taxa-list))
      (let ((fringes (term-to-bfringes tree taxa-list)))
        (make-proportion-support-for-branches
         fringes set taxa-list))
    'bad-input-tree))

(defun branch-by-branch-proportion-support-brlens (tree set taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a listing of branches in the input tree and the proportion of trees
;  in the input set with branch lengths that support that branch~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) set - a list of trees
;    (3) taxa-list - a list of taxa names

;  Details: All trees must have the taxa list given.  Bipartitions returned
;           are bdd based.  Allows branch lengths
;           (see branch-by-branch-proportion).  "
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list set))
        (tree-no-brlens (remove-brlens tree)))
    (branch-by-branch-proportion-support tree-no-brlens
                                         trees-no-brlens
                                         taxa-list)))
