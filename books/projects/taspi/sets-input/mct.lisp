(in-package "ACL2")

;; This basic implementation assumes trees are on the same set of taxa
(include-book "mast")
(include-book "../code/build/build-term-guards")

;; This could/should move to somewhere else!!
(defun get-all-fringes (trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns all bdd based bipartitions present in the trees input.~/
;  ~/
;  Arguments:
;    (1) trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Trees should have taxa list given and no branch lengths."
  (declare (xargs :guard t))
  (if (consp trees)
      (if (and (treep (car trees))
               (consp (car trees))
               (<= 2 (len taxa-list))
               (int-symlist taxa-list))
          (app (term-to-bfringes (car trees) taxa-list)
                (get-all-fringes (cdr trees) taxa-list))
        'bad-input-to-get-all-fringes)
    nil))

(defun project-each (trees taxa-list)
  (declare (xargs :guard t))
  (if (consp trees)
      (cons (project t taxa-list (car trees))
            (project-each (cdr trees) taxa-list))
    nil))

(defun project-each-check-compat (taxa-list list-of-trees)
  (declare (xargs :guard t))
  (let ((new-trees (project-each list-of-trees taxa-list)))
    (if (q-no-conflicts-list-gen (get-all-fringes new-trees taxa-list))
        t
      nil)))

(defun build-tree-taxa-list-trees-to-project (trees taxa-list)
  (declare (xargs :guard t))
  (let* ((new-trees (project-each trees taxa-list))
         (fringes (get-all-fringes new-trees taxa-list))
         (no-dup-fringes (remove-dups fringes)))
    (build-term-top-guard-t no-dup-fringes taxa-list)))

(defun find-mct (list-of-taxa-lists list-of-trees)
  (declare (xargs :guard t))
  (if (and (consp list-of-taxa-lists)
           (consp list-of-trees))
      (if (project-each-check-compat (car list-of-taxa-lists)
                                     list-of-trees)
          (build-tree-taxa-list-trees-to-project
           list-of-trees
           (car list-of-taxa-lists))
        (find-mct (cdr list-of-taxa-lists) list-of-trees))
    nil))

(defun mct (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the maximum compatibility tree of a set of trees~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: The trees given should have taxa list given and no branch lengths
;           (see also mct-brlens).  Returns a single maximum compatibility tree
;           even if there exists more than one."
  (declare (xargs :guard t))
  (find-mct (possible-taxa-lists taxa-list)
            list-of-trees))

(defun mct-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the maximum compatibility tree of a set of trees with branch lengths~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: The trees given should have taxa list given and may or may not
;           have branch lengths (see also mct).  Returns a single maximum
;           compatibility tree even if there exists more than one."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (find-mct (possible-taxa-lists taxa-list)
              trees-no-brlens)))

#||
Should probably put in more examples, but here is at least one

(mct '((1 2 (3 (((4 5) 6) (7 8))))
        (1 2 (3 (4 (5 ((6 7) 8)))))
        (1 2 (5 ((3 4) ((6 7) 8))))
        (1 2 (((3 5) 6) (4 (7 8))))
        (1 2 (3 ((5 6) ((4 7) 8))))
        (1 2 (3 ((4 5) (6 (7 8)))))
        (1 2 ((4 5) (((3 6) 7) 8))))
      '(1 2 3 4 5 6 7 8))
||#
