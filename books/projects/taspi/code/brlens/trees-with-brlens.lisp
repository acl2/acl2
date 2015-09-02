(in-package "ACL2")
(include-book "brlens")
(include-book "../gen-trees/tree-predicates")

;; trees-with-brlens defines recognizers for trees with
;; both any atom brlens (treep-brlens x) and requiring
;; only numeric brlens (treep-num-brlens x).  The recognizers
;; allowing brlens do not require brlens, but the recognizers
;; for trees with numeric brlens requires that all brlens are
;; present.

;; There are also functions for several of the likely to be used
;; functions from tree-predicates.lisp, replete.lisp, and
;; fringes.lisp.  These functions generally first remove brlens
;; and then call the functions from tree-predicates.lisp.

;; Examples at the end of the file.

;; A tip with brlens is possibly a cons
(defun tip-p-brlen (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Recognizes whether or not input is a valid leaf.~/
;  ~/
;  Arguments:
;    (1) x - a possible leaf

;  Details: Does allow branch lengths (see also tip-p)."
  (declare (xargs :guard t))
  (if (consp x) ; brlen present
      (and (or (and (symbolp (car x))
                    (not (equal (car x) nil)))
               (integerp (car x)))
           (not (consp (cdr x)))
           (not (equal (cdr x) nil))) ;; any non-nil atom
    (or (and (symbolp x)
             (not (equal x nil)))
        (integerp x))))

(defthm tip-p-brlen-when-not-consp
  (implies (not (consp x))
           (equal (tip-p-brlen x)
                  (or (and (symbolp x)
                           (not (equal x nil)))
                      (integerp x)))))

(defthm tip-p-brlen-of-cons
  (equal (tip-p-brlen (cons first rest))
         (and (or (and (symbolp first)
                       (not (equal first nil)))
                  (integerp first))
              (not (consp rest))
              (not (equal rest nil)))))

(in-theory (disable tip-p-brlen))

;; treep-brlens checks that a tree has good taxa names,
;; arbitrary atom brlens if present, and no singleton subtrees
(mutual-recursion
 (defun treep-brlens (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes well formed trees with no singletons.~/
;   ~/
;   Arguments:
;      (1) x - a potential tree

;   Details: Well formed tips are defined as in tip-p, branch lengths are
;            permitted (see also treep)."
   (declare (xargs :guard t
                   :measure (tree-measure x t)))
   (or (tip-p-brlen x)
       (and (consp x)
            (if (consp (cdr x))
                (tree-listp-brlens x)
              (and (not (equal (cdr x) nil))
                   (if (consp (car x))
                       (not (equal (cdar x) nil)) ; check for singleton
                     t)
                   (tree-listp-brlens (car x)))
               ))))

 (defun tree-listp-brlens (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes a list of well formed trees with no singletons.~/
;   ~/
;   Arguments:
;      (1) list - a list of potential trees

;   Details: Well formed tips are defined as in tip-p, branch lengths are
;            permitted (see also tree-listp)."
   (declare (xargs :guard t
                   :measure (tree-measure list nil)))
   (if (atom list)
       (equal list nil)
     (and (treep-brlens (car list))
          (tree-listp-brlens (cdr list))))))


(defthm treep-brlens-when-not-consp
  (implies (not (consp x))
           (equal (treep-brlens x)
                  (tip-p-brlen x))))

(defthm treep-brlens-of-consp
  (equal (treep-brlens (cons first rest))
         (or (tip-p-brlen (cons first rest))
             (if (consp rest)
                 (tree-listp-brlens (cons first rest))
               (and (not (equal rest nil))
                    (if (consp first)
                        (not (equal (cdr first) nil))
                      t)
                    (tree-listp-brlens first))))))


(defthm tree-listp-brlens-when-not-consp
  (implies (not (consp x))
           (equal (tree-listp-brlens x)
                  (equal x nil))))

(defthm tree-listp-brlens-of-consp
  (equal (tree-listp-brlens (cons first rest))
         (and (treep-brlens first)
              (tree-listp-brlens rest))))

(in-theory (disable treep-brlens tree-listp-brlens))

;; A tip with numeric brlens
(defun tip-p-num-brlen (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Recognizes whether or not input is a leaf with a numeric branch length.~/
;  ~/
;  Arguments:
;    (1) x - a possible leaf

;  Details: Requires a branch length in order to return true.
;           See also tip-p."
  (declare (xargs :guard t))
  (if (consp x) ; brlen must be present
      (and (or (and (symbolp (car x))
                    (not (equal (car x) nil)))
               (integerp (car x)))
           (acl2-numberp (cdr x)))
    nil))

(defthm tip-p-num-brlen-when-not-consp
  (implies (not (consp x))
           (equal (tip-p-num-brlen x)
                  nil)))

(defthm tip-p-num-brlen-of-cons
  (equal (tip-p-num-brlen (cons first rest))
         (and (or (and (symbolp first)
                       (not (equal first nil)))
                  (integerp first))
              (acl2-numberp rest))))

(in-theory (disable tip-p-num-brlen))

;; treep-num-brlens checks that a tree has good taxa names,
;; rational brlens, and no singleton subtrees
(mutual-recursion
 (defun treep-num-brlens (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes well formed trees with numeric branch lengths
;   and no singletons.~/
;   ~/
;   Arguments:
;      (1) x - a potential tree

;   Details: Well formed tips are defined as in tip-p-num-brlen.
;            See also treep."
   (declare (xargs :guard t
                   :measure (tree-measure x t)))
   (or (tip-p-num-brlen x)
       (and (consp x)
            (if (consp (cdr x))
                (tree-listp-num-brlens x)
              (and (rationalp (cdr x)) ; require numeric
                   (if (consp (car x))
                       (not (equal (cdar x) nil)) ; check for singleton
                     t)
                   (tree-listp-num-brlens (car x)))
               ))))

 (defun tree-listp-num-brlens (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Recognizes a list of well formed trees with numeric branch lengths
;   and no singletons.~/
;   ~/
;   Arguments:
;      (1) list - a list of potential trees

;   Details: Well formed tips are defined as in tip-p-num-brlen.
;            See also tree-listp."
   (declare (xargs :guard t
                   :measure (tree-measure list nil)))
   (if (atom list)
       (equal list nil)
     (and (treep-num-brlens (car list))
          (tree-listp-num-brlens (cdr list))))))


(defthm treep-num-brlens-when-not-consp
  (implies (not (consp x))
           (equal (treep-num-brlens x)
                  nil)))

(defthm treep-num-brlens-of-consp
  (equal (treep-num-brlens (cons first rest))
         (or (tip-p-num-brlen (cons first rest))
             (if (consp rest)
                 (tree-listp-num-brlens (cons first rest))
               (and (rationalp rest)
                    (if (consp first)
                        (not (equal (cdr first) nil))
                      t)
                    (tree-listp-num-brlens first))))))

(defthm tree-listp-num-brlens-when-not-consp
  (implies (not (consp x))
           (equal (tree-listp-num-brlens x)
                  (equal x nil))))

(defthm tree-listp-num-brlens-of-consp
  (equal (tree-listp-num-brlens (cons first rest))
         (and (treep-num-brlens first)
              (tree-listp-num-brlens rest))))

(in-theory (disable treep-num-brlens tree-listp-num-brlens))

;; Here is a flag version of the function above, which
;; will probably be useful should I ever actually prove anything
(defun treep-brlens-flg (flg x)
   (declare (xargs :guard t
                   :measure (tree-measure x flg)))
   (if flg
       (or (tip-p-brlen x)
           (and (consp x)
                (if (consp (cdr x))
                    (treep-brlens-flg nil x)
                  (and (not (equal (cdr x) nil))
                       (if (consp (car x))
                           (not (equal (cdar x) nil)) ; check for singleton
                         t)
                       (treep-brlens-flg nil (car x)))
                  )))
     (if (atom x)
         (equal x nil)
       (and (treep-brlens-flg t (car x))
            (treep-brlens-flg nil (cdr x))))))

(defthm equal-treep-defs
  (and (implies (equal flg t)
                (equal (treep-brlens-flg flg a)
                       (treep-brlens a)))
       (implies (equal flg nil)
                (equal (treep-brlens-flg flg a)
                       (tree-listp-brlens a))))
  :hints (("Goal" :in-theory (enable treep-brlens
                                     tree-listp-brlens)
           :induct (treep-brlens-flg flg a))))

;;Here are a few things I would really like to know are true, but have not yet proved:
;; (skip-proofs
;; (defthm SKIP-treep-brlens-remove-treep
;;   (and (implies (treep-brlens x)
;;                 (treep (remove-brlens x)))
;;        (implies (tree-listp-brlens x)
;;                 (tree-listp (remove-brlens-list x))))
;;   :hints (("Goal" :induct (treep-brlens-flg flg
;;                                         (remove-brlens-flg flg x)))))
;; )

;; (skip-proofs
;;  (defthm SKIP-treep-through-remove
;;    (and (implies (treep x)
;;                  (equal (remove-brlens x)
;;                         x))
;;         (implies (tree-listp x)
;;                  (equal (remove-brlens-list x)
;;                         x))))
;; )

;; Functions that first remove-brlens and then call
;; appropriate function from tree-predicates.lisp
(defun subtreep-brlens (a b)
  (declare (xargs :guard t))
  (subtreep (remove-brlens a)
            (remove-brlens b)))

(defun proper-subtreep-brlens (a b)
  (declare (xargs :guard t))
  (proper-subtreep (remove-brlens a)
                   (remove-brlens b)))

(defun taspip-brlens (x)
  (declare (xargs :guard t))
  (taspip t (remove-brlens x)))

(defun taspip-list-brlens (x)
  (declare (xargs :guard t))
  (taspip nil (remove-brlens-list x)))

;; Note - its my belief that count-tips of
;; a tree with brlens and one with brlens removed
;; is the same.  For count-tips-list, things are slightly
;; more complicated.

;(defun tree-depth-brlens (x)
;  (declare (xargs :guard t))
;  (tree-depth (remove-brlens x)))

;(defun balanced-tree-brlens (x)
;  (declare (xargs :guard t))
;  (balanced-tree (remove-brlens x)))

(defun mytips-brlens (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns the taxa names from a tree with or without branch lengths.~/
;   ~/
;   Arguments:
;      (1) tree - a tree

;   Details: Assumes that no taxon has been assigned the name *nil*.
;            See also mytips."
  (declare (xargs :guard t))
  (mytips (remove-brlens x)))

#||
Some examples

(list
 (treep-brlens '(((a b) . 3) c))
 (treep-brlens '(a . 2))
 (treep-brlens '((a . 4)))
 (treep-brlens '(a b))
 (treep-brlens '((A . 4) (b . 2)))
 (treep-brlens '((a . 4) . 2)) ;; bad
 (treep-brlens  '((a . 4) b))
 (treep-brlens '(a . (a . 3))) ;; also bad form!
 (treep-brlens '(((a . 4) (b . 3)) . 5))
 (treep-brlens '((a) . 4)) ;; bad
)

(list
 (treep-num-brlens '(((a b) . 3) c))
 (treep-num-brlens '((((a . 4) (b . 2)) . 3) (c . 6)))
 (treep-num-brlens '(a . b))
 (treep-num-brlens '((a . 4)))
 (treep-num-brlens '(a b))
 (treep-num-brlens '((A . 4) (b . 2)))
 (treep-num-brlens '((a . 4) . 2))
 (treep-num-brlens  '((a . 4) b))
 (treep-num-brlens '(a . (a . 3)))
 (treep-num-brlens '(((a . 4) (b . 3)) . 5))
 (treep-num-brlens '((a) . 4))
)

(list
 (subtreep-brlens '(a b) '(((a . 4) (b . 2)) . 2))
 (subtreep-brlens '((a . 4) (b . 3)) '(((a b) c) (d (e . 4))))
 (subtreep-brlens '((a . 4) (c . 3)) '(((a b) c) (d (e . 4))))
 (subtreep-brlens '((a . 4) (b . 3)) '((((a b) c) . 2) (d (e . 4))))
 (proper-subtreep-brlens '((a . 4) (b . 3)) '(((a b) c) (d (e . 4))))
 (proper-subtreep-brlens '((a . 4) (b . 3)) '(a b))
 (proper-subtreep-brlens '(d e) '((((a b) (c d)) . 4) ((e . 5) f)))
 (proper-subtreep-brlens '((e . 3) (f . 2)) '((((a b) (c d)) . 4) ((e . 5) f)))
)

(taspip-brlens '((((a b) (c d)) . 4) ((e . 5) f)))

(taspip-list-brlens '((((a b) (c d)) . 4) ((e . 5) f)))

(depth-brlens '((((a b) (c d)) . 4) ((e . 5) f)))

(balanced-tree-brlens '((((a b) (c d)) . 4) ((e . 5) f)))

(mytips-brlens '((((a b) (c d)) . 4) ((e . 5) f)))



||#
