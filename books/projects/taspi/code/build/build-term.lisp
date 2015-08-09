;  build-term.lisp                                      Boyer & Hunt

; Added functions for building trees from lists, guards for all

; Here we provide a function for constructing printed answers.  These
; functions might be considered non-HONS functions as we just use CONS
; everywhere as we assume once an answer is printed, the answer will
; be discarded.

(in-package "ACL2")
(include-book "../fringes/fringes")

(defun orderly-cons (x l taxon-index-alist)
  (declare (xargs :guard
                  (and (good-taxon-index-halist taxon-index-alist)
                       (taspip nil l)
                       (subset (mytips l)
                               (get-taxa-from-taxon-index
                                taxon-index-alist))
                       (member-gen
                        (first-taxon x)
                        (get-taxa-from-taxon-index taxon-index-alist)))
                  :verify-guards nil))
  (cond ((atom l) (hons x nil))
        ((< (cdr (het (first-taxon x) taxon-index-alist))
            (cdr (het (first-taxon (car l)) taxon-index-alist)))
         (hons x l))
        (t (hons (car l) (orderly-cons x (cdr l) taxon-index-alist)))))

(defthm orderly-cons-when-not-consp
  (implies (not (consp l))
           (equal (orderly-cons x l tia)
                  (cons x nil))))

(defthm orderly-cons-of-consp
  (equal (orderly-cons x (cons first rest) tia)
         (if (< (cdr (het (first-taxon x) tia))
                (cdr (het (first-taxon first) tia)))
             (cons x (cons first rest))
           (cons first (orderly-cons x rest tia)))))

(dis+ind orderly-cons)

(defun orderly-append (l1 l2 taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (taspip nil l1)
                              (subset (mytips l1)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist))
                              (taspip nil l2)
                              (subset (mytips l2)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))
                  :verify-guards nil))
  (cond ((atom l1) l2)
        (t (orderly-cons (car l1)
                         (orderly-append (cdr l1) l2
                                         taxon-index-alist)
                         taxon-index-alist))))

(defthm orderly-append-when-not-consp
  (implies (not (consp l1))
           (equal (orderly-append l1 l2 tia)
                  l2)))

(defthm orderly-append-of-consp
  (equal (orderly-append (cons first rest) l2 tia)
         (orderly-cons first
                       (orderly-append rest l2 tia)
                       tia)))

(dis+ind orderly-append)

(defun build-term-helper
  (outstanding-taxa     ;;  A BDD fringe
   required-subtrees    ;;  A list of BDD fringes
   full-taxa-list-tree  ;;  BDD-like structure; actual taxa symbols at tips
   taxon-index-alist    ;;  A taxon to index fast alist
   ans)
  (declare (xargs :guard
                  (and (good-taxon-index-halist taxon-index-alist)
                       (balanced-tree full-taxa-list-tree)
                       (<= (depth outstanding-taxa)
                           (depth full-taxa-list-tree))
                       (or outstanding-taxa (consp ans))
                       (valid-bdd-list required-subtrees)
                       (valid-bdd outstanding-taxa)
                       (good-depths required-subtrees
                                    full-taxa-list-tree)
                       (subset (btree-to-fringe
                                outstanding-taxa
                                full-taxa-list-tree)
                                (get-taxa-from-taxon-index
                                 taxon-index-alist))
                       (subset (mytips ans)
                               (get-taxa-from-taxon-index
                                taxon-index-alist))
                       (qs-subset-list required-subtrees
                                       outstanding-taxa)
                       (taspip nil ans)
                       (q-no-conflicts-list required-subtrees)
                       (not (member-gen nil required-subtrees))
                       (not (member-gen t required-subtrees)))
                  :verify-guards nil))
  (cond
   ((atom required-subtrees)
    (orderly-append
     (btree-to-fringe outstanding-taxa full-taxa-list-tree)
     ans
     taxon-index-alist))
   (t (let ((x (build-term-helper
                (car required-subtrees)
                (subtrees-implying (car required-subtrees)
                                   (cdr required-subtrees))
                full-taxa-list-tree
                taxon-index-alist
                nil)))
        (build-term-helper
         (q-and-c2 outstanding-taxa (car required-subtrees))
         (subtrees-not-implying (car required-subtrees)
                                (cdr required-subtrees))
         full-taxa-list-tree
         taxon-index-alist
         (orderly-cons x ans
                       taxon-index-alist))))))

(defthm build-term-helper-when-not-consp
  (implies (not (consp required-subtrees))
           (equal (build-term-helper outstanding-taxa
                                     required-subtrees
                                     ftlt tia ans)
                  (orderly-append
                   (btree-to-fringe outstanding-taxa ftlt)
                   ans tia))))

(defthm build-term-helper-of-consp
  (equal (build-term-helper outstanding-taxa (cons first rest)
                            ftlt tia ans)
         (let ((x (build-term-helper
                   first
                   (subtrees-implying first rest)
                   ftlt tia nil)))
           (build-term-helper
            (q-and-c2 outstanding-taxa first)
            (subtrees-not-implying first rest)
            ftlt tia (orderly-cons x ans tia)))))

(dis+ind build-term-helper)

(defun build-term-top (bdd-fringes taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tree implied by the bipartitions given.~/
;  ~/
;  Arguments:
;     (1) bdd-fringes - a list of bdd based bipartitions
;     (2) taxa-list - a list of taxa names

;  Details: BDD based bipartitions should have been created using the taxa-list
;           given.  Tree returned will be ordered according the order implied
;           by the taxa list given. NOTE: Representation returned is rooted
;           at the *longest* bipartition but could/should probably use mv-root when
;           building an unrooted tree."
  (declare (xargs :guard
                  (and (<= 2 (len taxa-list))
                       (int-symlist taxa-list)
                       (valid-bdd-list bdd-fringes)
                       (good-depths bdd-fringes
                                    (build-taxa-list-tree taxa-list))
                       (subset-list (btrees-to-fringes bdd-fringes
                                                       (build-taxa-list-tree
                                                        taxa-list))
                                    taxa-list)
                       (not (member-gen nil bdd-fringes)))
                  :verify-guards nil))
  (let* ((full-taxa-list-tree (build-taxa-list-tree taxa-list))
         (taxon-index-alist (taxa-list-to-taxon-index taxa-list))
         (bdd-fringes-sorted (sort-bdd-fringes bdd-fringes
                                               full-taxa-list-tree
                                               taxon-index-alist)))
    (if (consp bdd-fringes-sorted)
        (if (member-gen t (cdr bdd-fringes-sorted))
            'not-possible-to-create-tree-from-fringes
          (if (and (q-no-conflicts-list bdd-fringes-sorted)
                   (qs-subset-list (cdr bdd-fringes-sorted)
                                   (car bdd-fringes-sorted)))
              (build-term-helper (car bdd-fringes-sorted)
                                 (cdr bdd-fringes-sorted)
                                 full-taxa-list-tree
                                 taxon-index-alist
                                 nil)
            'not-possible-to-create-tree-from-fringes))
      nil)))


