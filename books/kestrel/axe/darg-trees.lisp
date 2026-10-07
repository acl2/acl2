; Trees whose leaves are DAG function arguments ("dargs")
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system) ;for myquotep
(include-book "kestrel/utilities/polarity" :dir :system)
;(include-book "darg-listp")
;(include-book "dargp-less-than")
(include-book "bounded-darg-listp")
(include-book "axe-trees")
(include-book "dag-array-builders")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; Darg-trees are like pseudo-terms but with integers (nodenums in some DAG) at
;; the leaves instead of variables.  Constants can also appear at the leaves.
;; TODO: Also make bounded-darg-treep.
(mutual-recursion
 (defun darg-treep (tree)
   (declare (xargs :guard t))
   (if (atom tree)
       (natp tree) ; a nodenum
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           ;; a quoted constant:
           (and (= 1 (len (fargs tree)))
                (true-listp (fargs tree)))
         ;; the application of a function symbol or lambda to args that are darg-trees:
         (let ((args (fargs tree)))
           ;; TODO: Can we require the lambda to be closed?
           (and (darg-tree-listp args)
                (or (symbolp fn)
                    (and (true-listp fn)
                         (equal (len fn) 3)
                         (eq (car fn) 'lambda)
                         (symbol-listp (lambda-formals fn))
                         ;; lambda-body is a regular pseudo-term, not a darg-tree:
                         (pseudo-termp (lambda-body fn))
                         (equal (len (lambda-formals fn))
                                (len args))))))))))
 (defun darg-tree-listp (trees)
   (declare (xargs :guard t))
   (if (atom trees)
       (null trees)
     (and (darg-treep (first trees))
          (darg-tree-listp (rest trees))))))

(defund-inline darg-tree-is-nodenump (tree)
  (declare (xargs :guard (darg-treep tree)))
  (atom tree))

(defund-inline darg-tree-is-quotep (tree)
  (declare (xargs :guard (darg-treep tree)))
  (and (consp tree)
       (eq 'quote (ffn-symb tree))))

(defund-inline darg-tree-is-callp (tree)
  (declare (xargs :guard (darg-treep tree)))
  (and (consp tree)
       (not (eq 'quote (ffn-symb tree)))))

(defund-inline darg-tree-quote-val (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-quotep tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-quotep)))))
  (unquote tree))

(defund-inline darg-tree-call-fn (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-callp tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-callp)))))
  (ffn-symb tree))

(defund-inline darg-tree-call-args (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-callp tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-callp)))))
  (fargs tree))

;; (defthm darg-treep-redef
;;   (equal (darg-treep tree)
;;          (or (natp tree)
;;              (myquotp tree)
;;              (let ((args (fargs tree)))
;;                ;; TODO: Can we require the lambda to be closed?
;;                (and (darg-tree-listp args)
;;                     (or (symbolp fn)
;;                         (and (true-listp fn)
;;                              (equal (len fn) 3)
;;                              (eq (car fn) 'lambda)
;;                              (symbol-listp (lambda-formals fn))
;;                              ;; lambda-body is a regular pseudo-term, not a darg-tree:
;;                              (pseudo-termp (lambda-body fn))
;;                              (equal (len (lambda-formals fn))
;;                                     (len args))))))))
;;   :rule-classes :definition)

(make-flag darg-treep)

(defthm-flag-darg-treep
  (defthm darg-tree-listp-forward-to-true-listp
    (implies (darg-tree-listp trees)
             (true-listp trees))
    :rule-classes :forward-chaining
    :flag darg-tree-listp)
  :skip-others t)

;; Darg-trees are also axe-trees
(defthm-flag-darg-treep
  (defthm axe-treep-when-darg-treep
    (implies (darg-treep tree)
             (axe-treep tree))
    :flag darg-treep)
  (defthm axe-tree-listp-when-darg-tree-listp
    (implies (darg-tree-listp trees)
             (axe-tree-listp trees))
    :flag darg-tree-listp))

(defthmd darg-treep-when-dargp
  (implies (dargp x)
           (darg-treep x))
  :hints (("Goal" :expand (darg-treep x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
