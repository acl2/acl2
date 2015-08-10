(in-package "ACL2")

(include-book "consensus")

(defun rational-val-alistp-gen (list)
  (declare (xargs :guard t))
  (if (consp list)
      (and (consp (car list))
           (rationalp (cdar list))
           (rational-val-alistp-gen (cdr list)))
    t))

(defun sort-by-frequency-merge (l1 l2)
  (declare (xargs :guard t
                  :measure (+ (acl2-count l1)
                              (acl2-count l2))))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((and (rational-val-alistp-gen l1)
              (rational-val-alistp-gen l2))
         (if (>= (cdar l1) (cdar l2))
             (cons (car l1)
                   (sort-by-frequency-merge (cdr l1) l2))
           (cons (car l2)
                 (sort-by-frequency-merge l1 (cdr l2)))))
        (t 'bad-input-to-sort-by-frequency-merge)))

(defun sort-by-frequency (alist)
  (declare (xargs :guard t
                  :hints (("Subgoal 2'4'" :in-theory
                           (disable even-gen-smaller-3)
                           :use (:instance even-gen-smaller-3
                                           (alst2 alist2)
                                           (alst1 (cons alist3 alist4)))))))
  (if (rational-val-alistp-gen alist)
      (if (and (consp alist)
               (consp (cdr alist)))
          (sort-by-frequency-merge
           (sort-by-frequency (evens-gen alist))
           (sort-by-frequency (odds-gen alist)))
        alist)
    'bad-input-to-sort-by-frequency))

(defun get-compatible-set (list ans)
  (declare (xargs :guard t))
  (if (consp list)
      (if (q-no-conflicts-list-gen
           (cons (car list) ans))
          (get-compatible-set (cdr list)
                              (cons (car list) ans))
        (get-compatible-set (cdr list) ans))
    ans))


(defun greedy (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the greedy consensus of a set of trees~/
;  ~/
;  Arguments:
;     (1) list-of-trees - a list of trees
;     (2) taxa-list - list of taxa

;  Details: List-of-trees must have the given taxa list.  The greedy consensus
;           orders the bipartitions found by their frequencies and adds
;           bipartitions to the consensus starting with the most frequent,
;           skipping conflicting bipartitions, until no non-conflicting
;           bipartition remains. Greedy consensus will be a refinement of the
;           majority consensus.
;           Does not allow branch lengths (see greedy-brlens)."
  (declare (xargs :guard t))
  (if (and (non-tip-tree-listp list-of-trees)
           (int-symlist taxa-list)
           (<= 2 (len taxa-list))
           (all-same-num-tips list-of-trees))
       (let* ((bfringe-freqs (bfringe-frequencies list-of-trees
                                                 taxa-list))
             (fringe-freq-sorted-by-popularity
               (sort-by-frequency bfringe-freqs)))
        (if (alistp-gen fringe-freq-sorted-by-popularity)
            (let* ((fringes-sorted-by-popularity
                    (strip-cars-gen fringe-freq-sorted-by-popularity))
                   (greedy-fringes
                    (get-compatible-set
                     fringes-sorted-by-popularity nil)))
              (build-term-top-guard-t greedy-fringes taxa-list))
          'bad-fringe-freq-sorted-in-greedy))
    'bad-input-to-greedy))

(defun greedy-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the greedy consensus of a set of trees with branch lengths~/
;  ~/
;  Arguments:
;     (1) list-of-trees - a list of trees
;     (2) taxa-list - list of taxa

;  Details: List-of-trees must have the given taxa list.  The greedy consensus
;           orders the bipartitions found by their frequencies and adds
;           bipartitions to the consensus starting with the most frequent,
;           skipping conflicting bipartitions, until no non-conflicting
;           bipartition remains. Greedy consensus will be a refinement of the
;           majority consensus.
;           Allow branch lengths (see greedy)."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (greedy trees-no-brlens taxa-list)))

#|| EXAMPLES

(let* ((bfringe-freqs (bfringe-frequencies '((1 2 (3 (((4 5) 6) (7 8))))
   (1 2 (3 (4 (5 ((6 7) 8)))))
   (1 2 (5 ((3 4) ((6 7) 8))))
   (1 2 (((3 5) 6) (4 (7 8))))
   (1 2 (3 ((5 6) ((4 7) 8))))
   (1 2 (3 ((4 5) (6 (7 8)))))
   (1 2 ((4 5) (((3 6) 7) 8))))
 '(1 2 3 4 5 6 7 8)
                                           ))
       (fringe-freq-sorted-by-popularity
        (sort-by-frequency bfringe-freqs))
       (fringes-sorted-by-popularity
        (strip-cars-gen fringe-freq-sorted-by-popularity))
       (greedy-fringes
        (get-compatible-set
         fringes-sorted-by-popularity nil)))
  (acons 'fringe-freq-sorted-by-popularity
         fringe-freq-sorted-by-popularity
         (acons 'fringes-sorted-by-popularity
                 fringes-sorted-by-popularity
                 (acons 'greedy-fringes
                        greedy-fringes
                        nil))))


(greedy
 '((1 2 (3 (((4 5) 6) (7 8))))
   (1 2 (3 (4 (5 ((6 7) 8)))))
   (1 2 (5 ((3 4) ((6 7) 8))))
   (1 2 (((3 5) 6) (4 (7 8))))
   (1 2 (3 ((5 6) ((4 7) 8))))
   (1 2 (3 ((4 5) (6 (7 8)))))
   (1 2 ((4 5) (((3 6) 7) 8))))
 '(1 2 3 4 5 6 7 8))

||#
