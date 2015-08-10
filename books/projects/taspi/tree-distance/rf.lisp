(in-package "ACL2")

(include-book "../code/fringes/fringes-guards")
(include-book "../database/props")

;; we'll use difference from code.  Correctness will require that
;; that fringes don't have duplicates

;; FN rate = false-negatives/number of true branches
;; FP rate = false-positives/number of branches found
;; RF = (FN rate + FP rate) / 2 to get avg
;; RF(T,T')= (|C(T)-C(T')| / C(T) + |C(T')-C(T)| / C(T')) / 2
;;   if we have a binary tree, this simplifies to:
;; RF(T,T') = (|C(T)-C(T')| + |C(T')-C(T)|) / 2 (n-3)
;;   where (n is number of leaves, so n-3 is number of internal branches)

(defun rf (tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the RF rate, false negative rate and false positive rate between the
;  two trees input.~/
;  ~/
;  Arguments:
;    (1) tree1 - a tree
;    (2) taxa-list1 - a list of taxa names
;    (3) rooted1 - a flag indicating rootedness
;    (4) tree2 - a tree
;    (5) taxa-list2 - a list of taxa names
;    (6) rooted2 - a flag indicating rootedness

;  Details: Trees input should not have branch lengths (see rf-brlens)."
  (declare (xargs :guard (and (good-taxa-list taxa-list1)
                              (good-taxa-list taxa-list2)
                              (good-tree tree1)
                              (good-tree tree2)
                              (good-tree-tl tree1 taxa-list1)
                              (good-tree-tl tree2 taxa-list2))))
  ;; need to check if they're rooted or unrooted, get appropriate
  ;; fringes to compare, make sure same taxa-list, etc
  (if (and (equal taxa-list1 taxa-list2)
           (consp tree1)
           (consp tree2))
      (let ((fringes1 (term-to-bfringes tree1 taxa-list1))
            (fringes2 (term-to-bfringes tree2 taxa-list1)))
        (let ((fringes1-to-compare
               (if (or (and rooted1 ;rooted and
                            (< 2 (len tree1))) ; not binary at root
                       (not rooted1)) ; or not rooted
                   (cdr fringes1)
                 (cddr fringes1))) ; rooted, binary at root
              (fringes2-to-compare
               (if (or (and rooted2 ;rooted and
                            (< 2 (len tree2))) ; not binary at root
                       (not rooted2)) ; or not rooted
                   (cdr fringes2)
                 (cddr fringes2)))) ; rooted, binary at root
          (let ((numBr1 (len fringes1-to-compare))
                (numBr2 (len fringes2-to-compare)))
            (if (or (= numBr1 0)
                    (= numBr2 0))
                (mv 'undefined numBr1 numBr2)
              (let ((fnRate (/ (len (difference fringes1-to-compare
                                                fringes2-to-compare))
                               numBr1))
                    (fpRate (/ (len (difference fringes2-to-compare
                                                fringes1-to-compare))
                               numBr2)))
                (mv (/ (+ fnRate fpRate) 2) fnRate fpRate))))))
    (mv 'need-same-taxa-list-and-consp-trees 'error 'error)))

(defun rf-brlens (tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the RF rate, false negative rate and false positive rate between the
;  two trees input.~/
;  ~/
;  Arguments:
;    (1) tree1 - a tree
;    (2) taxa-list1 - a list of taxa names
;    (3) rooted1 - a flag indicating rootedness
;    (4) tree2 - a tree
;    (5) taxa-list2 - a list of taxa names
;    (6) rooted2 - a flag indicating rootedness

;  Details: Trees input may have branch lengths (see rf)."
  (declare (xargs :guard t))
  (let ((tree1-no-brlens (remove-brlens tree1))
        (tree2-no-brlens (remove-brlens tree2)))
    (if (and (good-taxa-list taxa-list1)
             (good-taxa-list taxa-list2)
             (good-tree tree1-no-brlens)
             (good-tree tree2-no-brlens)
             (good-tree-tl tree1-no-brlens taxa-list1)
             (good-tree-tl tree2-no-brlens taxa-list2))
        (rf tree1-no-brlens taxa-list1 rooted1
                   tree2-no-brlens taxa-list2 rooted2)
      (mv 'error-in-rf-brlens 'error 'error))))


(defun find-closest-by-rf-help (tree list rooted1? rooted2? curScore curTree)
  (declare (xargs :guard (rationalp curScore)))
  (if (consp list)
      (mv-let (rf fn fp)
              (rf-brlens tree (mytips-brlens tree) rooted1?
                         (car list) (mytips-brlens (car list)) rooted2?)
              (declare (ignore fn fp))
              (if (and (rationalp rf)
                       (< rf curScore))
                  (find-closest-by-rf-help tree (cdr list)
                                           rooted1? rooted2? rf (car list))
                (find-closest-by-rf-help tree (cdr list)
                                         rooted1? rooted2?
                                         curScore curTree)))
    (mv curScore curTree)))

(defun find-closest-by-rf (tree list rooted1? rooted2?)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a tree from list closest according to rf rate to the given tree.~/
;  ~/
;  Arguments:
;    (1) tree - a tree
;    (2) list - a list of trees
;    (3) rooted1 - a flag indicating rootedness of tree
;    (4) rooted2 - a flag indicating rootedness of each tree in list

;  Details: Trees input may have branch lengths but they will not be preserved
;           in the tree returned.  A single tree is returned even if equally
;           close trees exist in the input list."
  (declare (xargs :guard t))
  (if (consp list)
      (mv-let (rf fn fp)
              (rf-brlens tree (mytips-brlens tree) rooted1?
                         (car list) (mytips-brlens (Car list))
                         rooted2?)
              (declare (ignore fn fp))
              (if (rationalp rf)
                  (find-closest-by-rf-help tree (cdr list) rooted1? rooted2? rf
                                           (car list))
                (mv 'error-in-find-closest-by-rf 'error)))
    (mv 'need-at-least-one-tree-in-list 'error)))

;(defun rf-entry (entry1 entry2)
;  (declare (xargs :guard (and (good-entry entry1)
;                              (good-entry entry2))))
;  (let ((taxa-list1 (get-taxa-list entry1))
;        (taxa-list2 (get-taxa-list entry2))
;        (tree1 (get-tree entry1))
;        (tree2 (get-tree entry2))
;        (rooted1 (get-rooted-flg entry1))
;        (rooted2 (get-rooted-flg entry2)))
;    (rf tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)))

#||
(rf '(a b ((c (d e)) ((f i) (g h)))) '(a b c d e f g h i) nil
    '(a ((b (c e)) (d (g h))) (f i) ) '(a b c d e f g h i) nil)
||#

