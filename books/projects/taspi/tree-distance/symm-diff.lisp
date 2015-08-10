(in-package "ACL2")

(include-book "../code/fringes/fringes-guards")
(include-book "../database/props")

(defun symm-diff (tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the symmetric difference, number of false negatives and number of
;  false positives between the two trees input.~/
;  ~/
;  Arguments:
;    (1) tree1 - a tree
;    (2) taxa-list1 - a list of taxa names
;    (3) rooted1 - a flag indicating rootedness
;    (4) tree2 - a tree
;    (5) taxa-list2 - a list of taxa names
;    (6) rooted2 - a flag indicating rootedness

;  Details: Trees input should not have branch lengths (see symm-diff-brlens)."
  (declare (xargs :guard (and (good-taxa-list taxa-list1)
                              (good-taxa-list taxa-list2)
                              (good-tree tree1)
                              (good-tree tree2)
                              (good-tree-tl tree1 taxa-list1)
                              (good-tree-tl tree2 taxa-list2))))
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
          (let ((FN (len (difference fringes1-to-compare
                                     fringes2-to-compare)))
                (FP (len (difference fringes2-to-compare
                                     fringes1-to-compare))))
            (mv (+ FN FP) FN FP))))
    (mv 'need-same-taxa-list-and-consp-trees 'error 'error)))

(defun symm-diff-brlens (tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the symmetric difference, number of false negatives and number of
;  false positives between the two trees input.~/
;  ~/
;  Arguments:
;    (1) tree1 - a tree
;    (2) taxa-list1 - a list of taxa names
;    (3) rooted1 - a flag indicating rootedness
;    (4) tree2 - a tree
;    (5) taxa-list2 - a list of taxa names
;    (6) rooted2 - a flag indicating rootedness

;  Details: Trees input may have branch lengths (see also symm-diff)."
  (declare (xargs :guard t))
  (let ((tree1-no-brlens (remove-brlens tree1))
        (tree2-no-brlens (remove-brlens tree2)))
    (if (and (good-taxa-list taxa-list1)
             (good-taxa-list taxa-list2)
             (good-tree tree1-no-brlens)
             (good-tree tree2-no-brlens)
             (good-tree-tl tree1-no-brlens taxa-list1)
             (good-tree-tl tree2-no-brlens taxa-list2))
        (symm-diff tree1-no-brlens taxa-list1 rooted1
                   tree2-no-brlens taxa-list2 rooted2)
      (mv 'error-in-symm-diff-brlens 'error 'error))))

;(defun symm-diff-entry (entry1 entry2)
;  (declare (xargs :guard (and (good-entry entry1)
;                              (good-entry entry2))))
;  (let ((taxa-list1 (get-taxa-list entry1))
;        (taxa-list2 (get-taxa-list entry2))
;        (tree1 (get-tree entry1))
;        (tree2 (get-tree entry2))
;        (rooted1 (get-rooted-flg entry1))
;        (rooted2 (get-rooted-flg entry2)))
;    (symm-diff tree1 taxa-list1 rooted1 tree2 taxa-list2 rooted2)))

#||
(symm-diff '(a b ((c (d e)) ((f i) (g h)))) '(a b c d e f g h i) nil
    '(a ((b (c e)) (d (g h))) (f i) ) '(a b c d e f g h i) nil)
||#
