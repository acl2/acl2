(in-package "ACL2")

(include-book "../code/gen-trees/sets-lists-trees")
(include-book "taxa-based")

(defun max-len-lists (flg x curMax)
  (declare (xargs :guard (integerp curMax)
                  :verify-guards nil
                  :measure (tree-measure x flg)))
  (if (consp x)
      (if flg ;top-level
          (max-len-lists nil x (max curMax (len x)))
        (max-len-lists nil (cdr x)
                       (max-len-lists t
                                      (car x)
                                      (max curMax (len (car x))))))
    curMax))

(defthm integerp-max-len-lists
  (implies (integerp curMax)
           (integerp (max-len-lists flg x curMax))))

(verify-guards max-len-lists)

(defun degree-of-tree (rooted-flg x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the degree of the input tree.~/
;  ~/
;  Arguments:
;    (1) rooted-flg - non-nil for a rooted tree,
;                     nil for an unrooted tree
;    (2) x - a tree
;
;  "
  (declare (xargs :guard t))
  (if rooted-flg
      (max-len-lists t x 0) ;rooted, all levels count
    (max-len-lists nil x (1- (len x)))))

(defun num-internal-help (flg x acc)
  (declare (xargs :guard (integerp acc)
                  :verify-guards nil
                  :measure (tree-measure x flg)))
  (if (consp x)
      (if flg
          (num-internal-help nil x (1+ acc))
        (num-internal-help nil
                           (cdr x)
                           (num-internal-help t (car x) acc)))
    acc))

(defthm integerp-num-internal-help
  (implies (integerp acc)
           (integerp (num-internal-help flg x acc))))

(verify-guards num-internal-help)

;(num-internal-help t '(a b (c d)) 0)
;(num-internal-help t '(a b (c d)) 0)

;; assumes a tree rep rooted at a node
(defun number-of-internal-nodes (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the number of internal nodes in the input tree.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Assumes the tree representation is rooted at a node.  Does not
;           handle branch lengths (see number-of-internal-nodes-brlens)."
  (declare (xargs :guard t))
  (num-internal-help t x 0))

(defun number-of-internal-nodes-brlens (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the number of internal nodes in the input tree.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Assumes the tree representation is rooted at a node.  Allows branch
;           lengths (see also number-of-internal-nodes)."
  (declare (xargs :guard t))
  (number-of-internal-nodes (remove-brlens x)))

;; Diameter
(defun diameter-no-brlens (tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the diameter of the input tree assuming unit branch lengths.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Maximum path distance between any two taxa in tree.
;           See diameter-brlens."
  (declare (xargs :guard t))
  (let* ((tree-no-brlens (remove-brlens tree))
         (taxa (mytips tree-no-brlens)))
    (find-max-pair-dist taxa tree-no-brlens 0)))

(defun diameter-brlens (tree)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the diameter of the input tree using branch lengths given.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Maximum path distance between any two taxa in tree.
;           See also diameter-no-brlens."
  (declare (xargs :guard t))
  (find-max-pair-dist-brlens (mytips-brlens tree) tree 0))

;; Depth of tree
(mutual-recursion
 (defun tree-depth (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the depth of the input tree representation.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Does not handle branch lengths.
;           See tree-depth-brlens."
   (declare (xargs :guard t
                   :measure (tree-measure x t)))
   (if (consp x)
       (1+ (tree-depth-list x))
     0))

 (defun tree-depth-list (x)
   (declare (xargs :guard t
                   :measure (tree-measure x nil)))
   (if (consp x)
       (max (tree-depth (car x))
            (tree-depth-list (cdr x)))
     0))
)

(defun tree-depth-brlens (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the depth of the input tree representation.~/
;  ~/
;  Arguments:
;    (1) x - a tree
;
;  Details: Allows branch lengths.
;           See also tree-depth."
  (declare (xargs :guard t))
  (tree-depth (remove-brlens x)))

#|| EXAMPLES:

(degree-of-tree t '((((a b) c) (d e)) (f ((g h) (i j)))))
(degree-of-tree nil '((a b c d) (E f g h) (i h d f) (e i g p)))
(degree-of-tree nil '((a . 4) ((b . 4) (c . 2)) (e . g)))
(degree-of-tree t '((a . 4) ((b . 4) (c . 2)) (e . g)))

(number-of-internal-nodes '((((a b) c) (d e)) (f ((g h) (i j)))))
(number-of-internal-nodes-brlens
 '((a . 4) ((b . 4) (c . 2)) (e . g)))
(number-of-internal-nodes-brlens '((a b c d) (E f g h) (i h d f) (e i g p)))

(diameter-no-brlens '((((a b) c) (d e)) (f ((g h) (i j)))))
(diameter-no-brlens '((a . 4) ((b . 4) (c . 2)) (e . g)))

(diameter-brlens '((((((a . 4) (b . 5)) . 3) (c . 2)) . 5)
                   (((d . 3) (e . 5)) . 6)
                   (((f . 3)
                     (((((g . 3) (h . 4)) . 5)
                       (((i . 9) (j . 7)) . 4)) . 6)) . 7)
                   ))


(tree-depth '(a b))
(tree-depth 'a)
(tree-depth '((((a b) c) (d e)) (f ((g h) (i j)))))
(tree-depth '((a b c d) (E f g h) (i h d f) (e i g p)))
(tree-depth '((a . 4) ((b . 4) (c . 2)) (e . g)))
(tree-depth-brlens '((a . 4) ((b . 4) (c . 2)) (e . g)))
(tree-depth-brlens '((((a b) c) (d e)) (f ((g h) (i j)))))


||#
