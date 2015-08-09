;; Implements multipolar consensus as introduced in the
;; Sys. Bio paper - 55(5):837-843, 2006. BBL06.pdf
;; Also implements loose (semi-strict)

(in-package "ACL2")

(include-book "consensus")

(defun get-kernal-splits (bfringes-left all-bfringes)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns those bipartitions in bfringes-left compatible with the entire set~/
;  ~/
;  Arguments:
;    (1) bfringes-left - a set of bdd based bipartitions
;    (2) all-bfringes - a set of bdd based bipartitions

;  Details: Arguments should have been created using the same taxa-list.
;           First argument should always be a subset of second."
  (declare (xargs :guard t))
  (if (consp bfringes-left)
      (if (q-no-conflicts-gen (car bfringes-left)
                              all-bfringes)
          (cons (car bfringes-left)
                (get-kernal-splits (cdr bfringes-left) all-bfringes))
        (get-kernal-splits (cdr bfringes-left) all-bfringes))
    nil))

(defun determine-incompat (bfringe list)
  (declare (xargs :guard t))
  (if (consp list)
      (if (and (q-and bfringe (car list))
               (not (qs-subset bfringe (car list)))
               (not (qs-subset (car list) bfringe)))
          (cons (car list)
                (determine-incompat bfringe (cdr list)))
        (determine-incompat bfringe (cdr list)))
    nil))

(defun build-incompat-graph (bfringes-left all-bfringes)
  (declare (xargs :guard t))
  (if (consp bfringes-left)
      (cons
       (cons (car bfringes-left)
             (determine-incompat (car bfringes-left)
                                 all-bfringes))
       (build-incompat-graph (cdr bfringes-left) all-bfringes))
    nil))

(defun get-used-colors (vertices ans)
  (declare (xargs :guard t))
  (if (alistp-gen ans)
      (if (consp vertices)
          (let ((color-cons (assoc-hqual (car vertices) ans)))
            ;; color exists for neighboring vertex
            (if (consp color-cons)
                (cons (cdr color-cons)
                      (get-used-colors (cdr vertices) ans))
              ;; no color for neighbor
              (get-used-colors (cdr vertices) ans)))
        nil)
    'need-alistp-ans-in-get-used))

(defun integer-listp-gen (list)
  (declare (xargs :guard t))
  (if (consp list)
      (and (integerp (car list))
           (integer-listp-gen (cdr list)))
    t))

(defun find-color-less-than-num? (used-colors cur-list num)
  (declare (xargs :guard t))
  (if (and (integer-listp-gen used-colors)
           (integerp num))
      (if (consp cur-list)
          (if (member-gen (car cur-list)  used-colors)
              (find-color-less-than-num? used-colors (cdr cur-list) (nfix num))
            (mv t (car cur-list)))
        (mv nil nil))
    (mv nil nil)))

(defun list-down-to-zero (cur)
  (declare (xargs :guard (natp cur)))
  (if (zp cur)
      nil
    (cons (1- cur) (list-down-to-zero (1- cur)))))


(defun build-coloring (vertices incompat-graph-all num ans)
  (declare (xargs :guard t))
  (if (and (natp num)
           (alistp-gen ans)
           (alistp-gen incompat-graph-all))
      (if (consp vertices)
          (let ((used-colors
                 (get-used-colors (cdr (assoc-hqual (car vertices)
                                                    incompat-graph-all))
                                  ans)))
            (mv-let (found-color? color)
                    (find-color-less-than-num? used-colors
                                               (list-down-to-zero num)
                                               num)
                    (if found-color?
                        (build-coloring (cdr vertices)
                                        incompat-graph-all
                                        num
                                        (cons (cons (car vertices)
                                                    color)
                                              ans))
                      (build-coloring (cdr vertices)
                                      incompat-graph-all
                                      (1+ num)
                                      (cons (cons (car vertices)
                                                  num)
                                            ans)))))
        (mv ans num))
    (mv 'bad-input-to-build-coloring 0)))

(defun get-fringes-matching-color (coloring color)
  (declare (xargs :guard t))
  (if (alistp-gen coloring)
      (if (consp coloring)
          (if (equal (cdar coloring) color)
              (cons (caar coloring)
                    (get-fringes-matching-color (cdr coloring)
                                                color))
            (get-fringes-matching-color (cdr coloring)
                                        color))
        nil)
    'need-alistp-gen-coloring-in-get-fringes-matching-color))

(defun remove-from-alist (keys-to-be-removed alist)
  (declare (xargs :guard t))
  (if (alistp-gen alist)
      (if (consp alist)
          (if (member-gen (caar alist) keys-to-be-removed)
              (remove-from-alist keys-to-be-removed (cdr alist))
            (cons (car alist)
                  (remove-from-alist keys-to-be-removed (cdr alist))))
        nil)
    'need-alistp-gen-in-remove-from-alist))

(defun build-trees-from-coloring (kernal coloring taxa-list numPoles)
  (declare (xargs :guard (natp numPoles)
                  :measure (acl2-count numPoles)))
  (if (or (zp numPoles)
          (not (int-symlist taxa-list))
          (> 2 (len taxa-list)))
      nil
    (if (alistp-gen coloring)
        (if (consp coloring)
            (let* ((curColor (cdar coloring))
                   (curColor-bfringes (get-fringes-matching-color coloring
                                                                  curColor))
                   (remFringes (remove-from-alist curColor-bfringes
                                                  coloring))
                   (curTotal-fringes (app kernal curColor-bfringes)))
              (cons (build-term-top-guard-t curTotal-fringes
                                            taxa-list)
                    (build-trees-from-coloring kernal
                                               remFringes
                                               taxa-list (1- numPoles))))
          nil)
      'need-an-alist-coloring-for-build-trees-from-coloring)))

(defun multipolar (list-of-trees alpha taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the multipolar consensus of list-of-trees, using proportion alpha.~/
;  ~/
;  Arguments:
;     (1) list-of-trees - a list of trees
;     (2) alpha - rational between 0 and 1 indicating ratio at which
;                 bipartitions are displayed
;     (3) taxa-list - a list of taxa

;  Details: List-of-trees must have the taxa list given. Uses a greedy coloring
;           algorithm where vertex order is determined by the frequency of
;           representative bipartition.
;           Does not handle branch lengths (see multipolar-brlens)."
  (declare (xargs :guard t))
  (if (and (non-tip-tree-listp list-of-trees)
           (int-symlist taxa-list)
           (<= 2 (len taxa-list))
           (all-same-num-tips list-of-trees)
           (rationalp alpha)
           (< 0 alpha))
      (let* ((bfringe-freqs (bfringe-frequencies list-of-trees
                                                 taxa-list))
             (numtrees (len list-of-trees))
             (cutoff (ceiling numtrees (/ 1 alpha))) ;; num required to keep
             (often-enough-bfringes
              (collect-when-size-is-at-least-cutoff
               bfringe-freqs cutoff))
             ;; order doesn't yet matter
             (kernal (get-kernal-splits often-enough-bfringes
                                        often-enough-bfringes))
             ;; kernal will be disjoint in incompatibility graph
             ;; so use difference
             (no-kernal (difference often-enough-bfringes
                                          kernal))
             (incompat-graph (build-incompat-graph
                              no-kernal no-kernal)))
        (if (alistp-gen incompat-graph)
            (mv-let (coloring numPoles)
                    (build-coloring (strip-cars-gen incompat-graph)
                                    incompat-graph
                                    0 nil)
                    (if (natp numPoles)
                        (build-trees-from-coloring kernal
                                                   coloring
                                                   taxa-list
                                                   numPoles)
                      'need-natp-numPoles-in-multipolar))
          'need-alistp-gen-incompat-graph-in-multipolar))
    'bad-input-to-multipolar))

(defun multipolar-brlens (list-of-trees alpha taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the multipolar consensus of list-of-trees, using proportion alpha.~/
;  ~/
;  Arguments:
;     (1) list-of-trees - a list of trees
;     (2) alpha - rational between 0 and 1 indicating ratio at which
;                 bipartitions are displayed
;     (3) taxa-list - a list of taxa

;  Details: List-of-trees must have the taxa list given. Uses a greedy coloring
;           algorithm where vertex order is determined by the frequency of
;           representative bipartition.
;           Allows branch lengths (see also multipolar)."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (multipolar trees-no-brlens alpha taxa-list)))

(defun loose (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the loose consensus of a set of trees~/
;  ~/
;  Arguments:
;     (1) list-of-trees - a list of trees
;     (2) taxa-list - list of taxa

;  Details: List-of-trees must have the given taxa list.  The loose consensus
;           contains those biparititions in the list of trees given that are
;           compatible with every other bipartition present.
;           Does not allow branch lengths (see loose-brlens)."
  (declare (xargs :guard t))
  (if (and (non-tip-tree-listp list-of-trees)
           (int-symlist taxa-list)
           (<= 2 (len taxa-list))
           (all-same-num-tips list-of-trees))
      (let* ((bfringe-freqs (bfringe-frequencies list-of-trees
                                                 taxa-list))
             (kernal (get-kernal-splits (strip-cars-gen
                                         bfringe-freqs)
                                        (strip-cars-gen
                                         bfringe-freqs))))
        (build-term-top-guard-t kernal
                                taxa-list))
    'bad-input-to-loose))

(defun loose-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the loose consensus of a set of trees with branch lengths~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - list of taxa

;  Details: List-of-trees must have the given taxa list.  The loose consensus
;           contains those biparititions in the list of trees given that are
;           compatible with every other bipartition present. Allows branch
;           lenghts (see loose)."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (loose trees-no-brlens taxa-list)))

#|| EXAMPLES:

(multipolar '((1 2 (3 (((4 5) 6) (7 8))))
              (1 2 (3 (4 (5 ((6 7) 8)))))
              (1 2 (5 ((3 4) ((6 7) 8))))
              (1 2 (((3 5) 6) (4 (7 8))))
              (1 2 (3 ((5 6) ((4 7) 8))))
              (1 2 (3 ((4 5) (6 (7 8)))))
              (1 2 ((4 5) (((3 6) 7) 8))))
            2/7
            '(1 2 3 4 5 6 7 8))

(loose '((1 2 (3 (((4 5) 6) (7 8))))
              (1 2 (3 (4 (5 ((6 7) 8)))))
              (1 2 (5 ((3 4) ((6 7) 8))))
              (1 2 (((3 5) 6) (4 (7 8))))
              (1 2 (3 ((5 6) ((4 7) 8))))
              (1 2 (3 ((4 5) (6 (7 8)))))
              (1 2 ((4 5) (((3 6) 7) 8))))
            '(1 2 3 4 5 6 7 8))


(let* ((bfringe-freqs (bfringe-frequencies '((1 2 (3 (((4 5) 6) (7 8))))
                                             (1 2 (3 (4 (5 ((6 7) 8)))))
                                             (1 2 (5 ((3 4) ((6 7) 8))))
                                             (1 2 (((3 5) 6) (4 (7 8))))
                                             (1 2 (3 ((5 6) ((4 7) 8))))
                                             (1 2 (3 ((4 5) (6 (7 8)))))
                                             (1 2 ((4 5) (((3 6) 7) 8))))
                                           '(1 2 3 4 5 6 7 8)))
             (cutoff (ceiling 7 (/ 1 2/7))) ;; num required to keep
             (often-enough-bfringes
              (collect-when-size-is-at-least-cutoff
               bfringe-freqs cutoff))
             ;; order doesn't yet matter
             (kernal (get-kernal-splits often-enough-bfringes
                                        often-enough-bfringes))
             (incompat-graph (build-incompat-graph
                                           (difference often-enough-bfringes
                                                       kernal)
                                           (difference often-enough-bfringes
                                                       kernal)))
             (coloring (build-coloring (strip-cars-gen incompat-graph)
                                       incompat-graph
                                       0 nil)))
  (cons (cons 'kernal kernal)
        (cons (cons 'often-enough often-enough-bfringes)
              (cons (cons 'incompat-graph incompat-graph)
                    (cons (cons 'coloring coloring)
                          nil)))))

(get-kernal-splits
 (strip-cars-gen
  (bfringe-frequencies
   '((1 2 (3 (((4 5) 6) (7 8))))
     (1 2 (3 (4 (5 ((6 7) 8)))))
     (1 2 (5 ((3 4) ((6 7) 8))))
     (1 2 (((3 5) 6) (4 (7 8))))
     (1 2 (3 ((5 6) ((4 7) 8))))
     (1 2 (3 ((4 5) (6 (7 8)))))
     (1 2 ((4 5) (((3 6) 7) 8))))
   '(1 2 3 4 5 6 7 8)))
 (strip-cars-gen
  (bfringe-frequencies
   '((1 2 (3 (((4 5) 6) (7 8))))
     (1 2 (3 (4 (5 ((6 7) 8)))))
     (1 2 (5 ((3 4) ((6 7) 8))))
     (1 2 (((3 5) 6) (4 (7 8))))
     (1 2 (3 ((5 6) ((4 7) 8))))
     (1 2 (3 ((4 5) (6 (7 8)))))
     (1 2 ((4 5) (((3 6) 7) 8))))
   '(1 2 3 4 5 6 7 8))) )

(btrees-to-fringes (strip-cars-gen
  (bfringe-frequencies
   '((1 2 (3 (((4 5) 6) (7 8))))
     (1 2 (3 (4 (5 ((6 7) 8)))))
     (1 2 (5 ((3 4) ((6 7) 8))))
     (1 2 (((3 5) 6) (4 (7 8))))
     (1 2 (3 ((5 6) ((4 7) 8))))
     (1 2 (3 ((4 5) (6 (7 8)))))
     (1 2 ((4 5) (((3 6) 7) 8))))
   '(1 2 3 4 5 6 7 8)))
(build-taxa-list-tree '(1 2 3 4 5 6 7 8)))

(btrees-to-fringes '(T)
                   (build-taxa-list-tree '(1 2 3 4 5 6 7 8)))

(incompat-graph (strip-cars-gen
  (bfringe-frequencies
   '((1 2 (3 (((4 5) 6) (7 8))))
     (1 2 (3 (4 (5 ((6 7) 8)))))
     (1 2 (5 ((3 4) ((6 7) 8))))
     (1 2 (((3 5) 6) (4 (7 8))))
     (1 2 (3 ((5 6) ((4 7) 8))))
     (1 2 (3 ((4 5) (6 (7 8)))))
     (1 2 ((4 5) (((3 6) 7) 8))))
   '(1 2 3 4 5 6 7 8)))
 (strip-cars-gen
  (bfringe-frequencies
   '((1 2 (3 (((4 5) 6) (7 8))))
     (1 2 (3 (4 (5 ((6 7) 8)))))
     (1 2 (5 ((3 4) ((6 7) 8))))
     (1 2 (((3 5) 6) (4 (7 8))))
     (1 2 (3 ((5 6) ((4 7) 8))))
     (1 2 (3 ((4 5) (6 (7 8)))))
     (1 2 ((4 5) (((3 6) 7) 8))))
   '(1 2 3 4 5 6 7 8))) )



(btrees-to-fringes (strip-cars-gen '((((NIL NIL . T) (T)) . 0)
                                     (((T T)) . 0)
                                     (((T)) . 1)
                                     (((T) (T)) . 1)
                                     ((((NIL . T) T)) . 0)))
                   (build-taxa-list-tree '(1 2 3 4 5 6 7 8)))

||#
