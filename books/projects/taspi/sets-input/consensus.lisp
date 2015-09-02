;; consensus.lisp: gives functions for strict and majority
(in-package "ACL2")

(include-book "../code/build/build-term-guards")
(include-book "../code/gen-trees/btrees-bdds")

;; To prove guards on compute-consensus, will also need:
;(include-book "../code/fringes/fringes-props")

(defun collect-when-size-is-at-least-cutoff (term-count-alist cutoff)
  (declare (xargs :guard (and (alistp-gen term-count-alist)
                              (rationalp cutoff))))
  (if (atom term-count-alist)
      nil
    (let ((element (car term-count-alist)))
      (if (>= (rfix (cdr element)) cutoff)
          (cons (car element)
                (collect-when-size-is-at-least-cutoff
                 (cdr term-count-alist) cutoff))
        (collect-when-size-is-at-least-cutoff
         (cdr term-count-alist) cutoff)))))

(defthm valid-bdd-list-through-collect
  (implies (valid-bdd-list (strip-cars-gen x))
           (valid-bdd-list (collect-when-size-is-at-least-cutoff
                            x cut-off))))

(defthm good-depths-through-collect
  (implies (good-depths (strip-cars-gen x) y)
           (good-depths (collect-when-size-is-at-least-cutoff
                         x cutoff)
                        y)))

(defun compute-consensus-helper
  (bfringe-frequencies taxa-list number-of-trees percentage)
  (declare (xargs :guard (and (alistp-gen bfringe-frequencies)
                              (valid-bdd-list
                               (strip-cars-gen bfringe-frequencies))
                              (good-depths
                               (strip-cars-gen bfringe-frequencies)
                               (build-taxa-list-tree taxa-list))
                              (int-symlist taxa-list)
                              (<= 2 (len taxa-list))
                              (integerp percentage)
                              (< 0 percentage)
                              (natp number-of-trees))
                  ))
  ;; (ceiling (numtrees * (percentage/100)))
  (let* ((cutoff (ceiling (* number-of-trees percentage) 100))
         ;; These next two forms build non-HONSP answers.
         (bio-majority (collect-when-size-is-at-least-cutoff
                        bfringe-frequencies cutoff)))
    (if (and (not (member-gen nil bio-majority))
             (subset-list
              (btrees-to-fringes bio-majority
                                 (build-taxa-list-tree taxa-list))
              taxa-list))
        (build-term-top bio-majority taxa-list)
      'invalid-bfringes)))


(defun compute-consensus (list-of-trees taxa-list percentage)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the majority consensus of a set of trees~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names
;    (3) percentage - an integer between 0 and 100

;  Details: Trees given must match taxa list given and all have the same
;           number of leaves.  Does not handle branch lengths (see
;           compute-consensus-brlens). NOTE: Guards not yet verified."
  (declare (xargs :guard (and (non-tip-tree-listp list-of-trees)
                              (int-symlist taxa-list)
                              (<= 2 (len taxa-list))
                              (all-same-num-tips list-of-trees)
                              (integerp percentage)
                              (< 0 percentage)
                              )
		  :verify-guards nil))
  (let ((bfringe-frequencies (bfringe-frequencies list-of-trees taxa-list))
        (num-trees (len list-of-trees)))
    (compute-consensus-helper bfringe-frequencies taxa-list
                              num-trees percentage)))

(defun compute-consensus-brlens (list-of-trees taxa-list percentage)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the majority consensus of a set of trees with branch lengths~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names
;    (3) percentage - an integer between 0 and 100

;  Details: Trees given must match taxa list given and all have the same
;           number of leaves.  Allows branch lengths (see also
;           compute-consensus). Guards are not yet verified."
  (declare (xargs :guard t
		  :verify-guards nil))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (if (and (non-tip-tree-listp trees-no-brlens)
             (int-symlist taxa-list)
             (<= 2 (len taxa-list))
             (all-same-num-tips trees-no-brlens)
             (integerp percentage)
             (< 0 percentage))
        (compute-consensus trees-no-brlens taxa-list percentage)
      'bad-input-trees-to-consensus)))

(defun compute-frequencies (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of bdd based bipartitions to their frequencies in
;  list-of-trees.~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Does not allow branch lengths on input trees.
;           Manages memory more explicitly than bfringe-frequencies."
  (declare (xargs :guard (and (non-tip-tree-listp list-of-trees)
                              (int-symlist taxa-list)
                              (<= 2 (len taxa-list))
                              (all-same-num-tips list-of-trees))))
  (let* ((replete-trees-list-top (replete-trees-list-top list-of-trees))
         (dbterms (hshrink-alist replete-trees-list-top 'replete-database))
         (void (flush-hons-get-hash-table-link replete-trees-list-top))
         (ta (build-fast-alist-from-alist
              (taxa-list-to-tree-alist taxa-list)
              'taxa-tree-alist))
         (bfringe-frequencies1
          (bfringe-frequencies1 dbterms dbterms
                                'the-bfringe-frequencies1 ta))
         (void1 (flush-hons-get-hash-table-link dbterms))
         (void2 (flush-hons-get-hash-table-link ta))
         (bio-ans (hshrink-alist bfringe-frequencies1 'bio-ans))
         (void3 (flush-hons-get-hash-table-link bfringe-frequencies1)))
    (declare (ignore void void1 void2 void3))
    bio-ans))

(defun compute-frequencies-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of bdd based bipartitions to their frequencies in
;  list-of-trees.~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Allows branch lengths.
;           Manages memory more explicitly than bfringe-frequencies-brlens."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (if (and (non-tip-tree-listp trees-no-brlens)
             (int-symlist taxa-list)
             (<= 2 (len taxa-list))
             (all-same-num-tips trees-no-brlens))
        (compute-frequencies trees-no-brlens taxa-list)
       'bad-input-trees-to-compute-frequencies)))

#||
(compute-consensus '((1 2 (3 (((4 5) 6) (7 8))))
                     (1 2 (3 (4 (5 ((6 7) 8)))))
                     (1 2 (5 ((3 4) ((6 7) 8))))
                     (1 2 (((3 5) 6) (4 (7 8))))
                     (1 2 (3 ((5 6) ((4 7) 8))))
                     (1 2 (3 ((4 5) (6 (7 8)))))
                     (1 2 ((4 5) (((3 6) 7) 8))))
                   '(1 2 3 4 5 6 7 8)
                   100)

(compute-frequencies '((1 2 (3 (((4 5) 6) (7 8))))
                     (1 2 (3 (4 (5 ((6 7) 8)))))
                     (1 2 (5 ((3 4) ((6 7) 8))))
                     (1 2 (((3 5) 6) (4 (7 8))))
                     (1 2 (3 ((5 6) ((4 7) 8))))
                     (1 2 (3 ((4 5) (6 (7 8)))))
                     (1 2 ((4 5) (((3 6) 7) 8))))
                   '(1 2 3 4 5 6 7 8))


(btrees-to-fringes (strip-cars-gen
                    (compute-frequencies '((1 2 (3 (((4 5) 6) (7 8))))
                                           (1 2 (3 (4 (5 ((6 7) 8)))))
                                           (1 2 (5 ((3 4) ((6 7) 8))))
                                           (1 2 (((3 5) 6) (4 (7 8))))
                                           (1 2 (3 ((5 6) ((4 7) 8))))
                                           (1 2 (3 ((4 5) (6 (7 8)))))
                                           (1 2 ((4 5) (((3 6) 7) 8))))
                                         '(1 2 3 4 5 6 7 8)))
                   (build-taxa-list-tree '(1 2 3 4 5 6 7 8)))

(compute-consensus-brlens '(((1 . 1) (2 . 2) (3 (((4 5) 6) (7 8))))
                            (1 2 (3 (4 (5 ((6 7) 8)))))
                            (1 2 (5 ((3 4) ((6 7) 8))))
                            (1 2 (((3 5) 6) (4 (7 8))))
                            (1 2 (3 ((5 6) ((4 7) 8))))
                            (1 2 (3 ((4 5) (6 (7 8)))))
                            (1 2 ((4 5) (((3 6) 7) 8))))
                          '(1 2 3 4 5 6 7 8)
                          100)

(compute-frequencies-brlens '(((1 . 1) (2 . 2) (3 (((4 5) 6) (7 8))))
                              (1 2 (3 (4 (5 ((6 7) 8)))))
                              (1 2 (5 ((3 4) ((6 7) 8))))
                              (1 2 (((3 5) 6) (4 (7 8))))
                              (1 2 (3 ((5 6) ((4 7) 8))))
                              (1 2 (3 ((4 5) (6 (7 8)))))
                              (1 2 ((4 5) (((3 6) 7) 8))))
                            '(1 2 3 4 5 6 7 8))


||#
