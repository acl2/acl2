;; tree-compatibility tests whether a collection of trees
;; is compatible.  If the set is compatible, their common
;; refinement is returned as evidence.  If not, nil is returned.

(in-package "ACL2")
(include-book "../code/build/build-term-guards")
(include-book "../code/gen-trees/btrees-bdds")
(include-book "../code/fringes/fringes-props")

;; determines if a tree is compatible with the set of edges
;; accumulated thus far
(defun bi-compat (cur-set tree taxa-list)
  (declare
   (xargs :guard (and (treep tree)
                      (consp tree)
                      (<= 2 (len taxa-list))
                      (int-symlist taxa-list)
                      (not (member-gen nil cur-set))
                      (good-depths
                       cur-set
                       (build-taxa-list-tree taxa-list))
                      (subset-list
                       (btrees-to-fringes
                        cur-set
                        (build-taxa-list-tree taxa-list))
                       taxa-list)
                      )
          :verify-guards nil))
  (let* ((new-set (my-union
                  cur-set
                  (cdr (term-to-bfringes tree taxa-list))))
         (o-set (sort-bdd-fringes
                 new-set
                 (build-taxa-list-tree taxa-list)
                 (taxa-list-to-taxon-index taxa-list))))
    (if (q-no-conflicts-list o-set)
        (mv t o-set)
      (mv nil nil))))

(local
(defthm not-member-gen-cdr-2
  (implies (not (member-gen x y))
           (not (member-gen x (cdr y)))))
)

(verify-guards
 bi-compat
 :hints (("Goal'" ; changed by J Moore after v5-0, from "Subgoal 1", for tau system
          :in-theory
          (disable subset-list-union-cdr)
          :use (:instance
                subset-list-union-cdr
                (x cur-set)
                (y (term-to-bfringes tree taxa-list))
                (ftlt
                 (build-taxa-list-tree taxa-list))
                (z (taspi-rev taxa-list))))
         ("Goal''" ; changed by J Moore after v5-0, from "Subgoal 1'''", for tau system
          :in-theory
          (disable
           subset-list-btrees-to-fringes-of-term-to-bfringes)
          :use (:instance
                subset-list-btrees-to-fringes-of-term-to-bfringes
                (term tree)))))

;; helper function for tree compatibility
(defun tree-compat (cur-set tips-seen tree-list taxa-list)
  (declare (xargs :measure (acl2-count tree-list)
                  :guard (and (tree-listp tree-list)
                              (<= 2 (len taxa-list))
                              (int-symlist taxa-list)
                              (subset (mytips tree-list)
                                      taxa-list)
                              (subset tips-seen taxa-list)
                              (not (member-gen nil cur-set))
                              (valid-bdd-list cur-set)
                              (good-depths
                               cur-set
                               (build-taxa-list-tree taxa-list))
                              (subset-list
                               (btrees-to-fringes
                                cur-set
                                (build-taxa-list-tree taxa-list))
                               taxa-list))
		  :verify-guards nil
                  ))
  (if (consp tree-list)
      (if (consp (car tree-list))
          (mv-let (flg new-set)
                  (bi-compat cur-set (car tree-list) taxa-list)
                  (if flg
                      (tree-compat new-set (my-union
                                            (mytips (car tree-list))
                                            tips-seen)
                                   (cdr tree-list)
                                   taxa-list)
                    nil))
        (tree-compat cur-set (my-union
                              (mytips (car tree-list))
                              tips-seen) (cdr tree-list) taxa-list))
    (if (consp tips-seen)
        (build-term-top (cons (bfringe tips-seen
                                       (build-fast-alist-from-alist
                                        (taxa-list-to-tree-alist
                                         taxa-list)
                                        'taxon-tree-alist))
                              cur-set)
                        taxa-list)
      nil)))

(defun tree-compatibility (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if a set of trees is compatible~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Does not allow branch lengths (see tree-compatibility-brlens).
;           Does a pairwise check of compatibility between all bipartitions
;           in the given list of trees. NOTE: Guards are not yet verified."
  (declare (xargs :guard (and (tree-listp list-of-trees)
                              (subset (mytips list-of-trees)
                                      taxa-list)
                              (<= 2 (len taxa-list))
                              (int-symlist taxa-list))
		  :verify-guards nil))
  (tree-compat nil nil
               list-of-trees taxa-list))

(defun tree-compatibility-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if a set of trees with branch lengths is compatible~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Allows branch lengths (see also tree-compatibility).
;           Does a pairwise check of compatibility between all bipartitions
;           in the given list of trees. NOTE: Guards are not yet verified. "
  (declare (xargs :guard t
		  :verify-guards nil))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (if (and (tree-listp trees-no-brlens)
             (subset (mytips trees-no-brlens)
                     taxa-list)
             (<= 2 (len taxa-list))
             (int-symlist taxa-list))
        (tree-compatibility trees-no-brlens taxa-list)
      'bad-input-to-tree-compatibility)))

#|| some examples
(tree-compatibility '(((a b c) (d e))
                      ((b c) (f g h))
                      (a (g h)))
                    '(a b c d e f g h))

(tree-compatibility '((a b c (d e))
                      (b c (f g h))
                      (a g h))
                    '(a b c d e f g h))

(tree-compatibility '((a (b (c (d e f g))))
                      (a (b c d (e (f g)))))
                    '(a b c d e f g))

(tree-compatibility '((a b (c (d e f g)))
                      (a b c d (e (f g))))
                    '(a b c d e f g))

(tree-compatibility '((a ((b c) (d e (f g))))
                      (a (b (c d (e f) g))))
                    '(a b c d e f g))

(tree-compatibility '((a (b c) (d e (f g)))
                      (a b c d (e f) g))
                    '(a b c d e f g))

(tree-compatibility-brlens '(((a . 4) (b . 6) (c (d e (f . 2) g)))
                      (a b (c . 1/2) d (e (f (g . 1)))))
                    '(a b c d e f g))
||#
