(in-package "ACL2")

(include-book "../single-input/taxa-based")

;; Stupid plan for MAST: make list of each possibility for
;; taxa in MAST, sort by length (or create as such), then
;; project each tree on set and determine if results
;; are equal.  Largest one satifying is MAST.

(defun distribute (x list)
  (declare (xargs :guard t))
  (if (consp list)
      (cons (append (list x) (car list))
            (distribute x (cdr list)))
    nil))

(defun make-possible-taxa (taxa-list)
  (declare (xargs :guard t))
  (if (consp taxa-list)
      (let ((ps-tail (make-possible-taxa (cdr taxa-list))))
        (app ps-tail (distribute (car taxa-list) ps-tail)))
    '(nil)))

(defun order-by-len-merge (l1 l2)
  (declare (xargs :measure (+ (acl2-count l1)
                              (acl2-count l2))
                  :guard t))
  (cond
   ((atom l1) l2)
   ((atom l2) l1)
   (t (let ((len-car-l1 (len (car l1)))
            (len-car-l2 (len (car l2))))
        (cond ((>= len-car-l1 len-car-l2)
               (cons (car l1)
                     (order-by-len-merge
                      (cdr l1)
                      l2)))
               (t
                (cons (car l2)
                      (order-by-len-merge
                       l1
                       (cdr l2)))))))))

(defun order-by-len (list)
  (declare (xargs :guard t))
  (if (and (consp list)
           (consp (cdr list)))
      (order-by-len-merge (order-by-len (evens-gen list))
                          (order-by-len (odds-gen list)))
    list))

(defun possible-taxa-lists (taxa-list)
  (declare (xargs :guard t))
  (order-by-len (make-possible-taxa taxa-list)))

;; this will only be right if input trees are all ordered
;; according to the same taxa-list.
(defun project-each-checking (taxa-list list-of-trees ans)
  (declare (xargs :guard t))
  (if (consp list-of-trees)
      (if (equal (project t taxa-list (car list-of-trees))
                 ans)
          (project-each-checking taxa-list
                                 (cdr list-of-trees)
                                 ans)
        nil)
    t))

(defun find-mast (list-of-taxa-lists list-of-trees)
  (declare (xargs :guard t))
  (if (and (consp list-of-taxa-lists)
           (consp list-of-trees))
      (let ((mast? (project t
                            (car list-of-taxa-lists)
                            (car list-of-trees))))
        (if (project-each-checking (car list-of-taxa-lists)
                                   (cdr list-of-trees)
                                   mast?)
            mast?
          (find-mast (cdr list-of-taxa-lists) list-of-trees)))
    nil))

(defun mast (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the maximum agreement subtree of a set of trees~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Returns a single maximum agreement tree even if there exists more
;           than one.  Does not handle branch lengths (see mast-brlens)."
  (declare (xargs :guard t))
  (find-mast (possible-taxa-lists taxa-list)
             list-of-trees))

(defun mast-brlens (list-of-trees taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Computes the maximum agreement subtree of a set of trees with branch lengths~/
;  ~/
;  Arguments:
;    (1) list-of-trees - a list of trees
;    (2) taxa-list - a list of taxa names

;  Details: Returns a single maximum agreement tree even if there exists more
;           than one.  Allows branch lengths (see mast)."
  (declare (xargs :guard t))
  (let ((trees-no-brlens (remove-brlens-list list-of-trees)))
    (find-mast (possible-taxa-lists taxa-list)
               trees-no-brlens)))

#||

(mast '((1 2 (3 (((4 5) 6) (7 8))))
        (1 2 (3 (4 (5 ((6 7) 8)))))
        (1 2 (5 ((3 4) ((6 7) 8))))
        (1 2 (((3 5) 6) (4 (7 8))))
        (1 2 (3 ((5 6) ((4 7) 8))))
        (1 2 (3 ((4 5) (6 (7 8)))))
        (1 2 ((4 5) (((3 6) 7) 8))))
      '(1 2 3 4 5 6 7 8))

(mast-brlens '((a ((b c) (d e (f g))))
               (a (b (c d (e f) g))))
             '(a b c d e f g))

(mast-brlens '(((a . 4) (((b c) . 5) (d e (f g))))
               (a (b (c d (((e . 2) f) . 3) g))))
             '(a b c d e f g))
||#
