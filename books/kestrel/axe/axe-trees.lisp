; Axe trees
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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
;(include-book "all-dargp")
;(include-book "dargp-less-than")
(include-book "bounded-darg-listp")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; For a related predicate that disallows variables, see darg-treep.
;like pseudo-termp but allows integers (nodenums in some DAG) to also appear
;; TODO: Make a more abstract interface to this (e.g., axe-tree-args instead of cdr)
;; See also bounded-axe-treep.
(mutual-recursion
 (defun axe-treep (tree)
   (declare (xargs :guard t))
   (if (atom tree)
       (or (symbolp tree) ; a variable
           (natp tree) ; a nodenum
           )
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           ;; a quoted constant;
           (and (= 1 (len (fargs tree)))
                (true-listp (fargs tree)))
         ;; the application of a function symbol or lambda to args that are axe trees:
         ;; TODO: Can we require the lambda to be closed?
         (and (axe-tree-listp (fargs tree))
              (or (symbolp fn)
                  (and (true-listp fn)
                       (equal (len fn) 3)
                       (eq (car fn) 'lambda)
                       (symbol-listp (cadr fn))
                       ;; lambda body is a regular, pseudo-term, not an axe-tree:
                       (pseudo-termp (caddr fn))
                       (equal (len (cadr fn))
                              (len (fargs tree))))))))))
 (defun axe-tree-listp (trees)
   (declare (xargs :guard t))
   (if (atom trees)
       (null trees)
     (and (axe-treep (first trees))
          (axe-tree-listp (rest trees))))))

(make-flag axe-treep)

(defthm axe-tree-listp-of-append
  (equal (axe-tree-listp (append x y))
         (and (axe-tree-listp (true-list-fix x))
              (axe-tree-listp y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable axe-tree-listp append))))

(defthm axe-treep-when-symbolp-cheap
  (implies (symbolp tree)
           (axe-treep tree))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd len-of-car-when-axe-treep
  (implies (axe-treep tree)
           (equal (len (car tree))
                  (if (consp (car tree)) ; check for lambda application
                      3
                    0)))
  :hints (("Goal" :expand (AXE-TREEP TREE)
           :in-theory (enable axe-treep))))

(defthmd len-of-lambda-formals-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)) ;it's a lambda
                )
           (equal (len (car (cdr (car tree))))
                  (len (fargs tree))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd true-listp-of-lambda-formals-when-axe-treep
  (implies (and (axe-treep tree)
                ;; (consp (car tree)) ;it's a lambda
                )
           (true-listp (lambda-formals (car tree))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd symbol-listp-of-lambda-formals-when-axe-treep
  (implies (and (axe-treep tree)
                ;; (consp (car tree)) ;it's a lambda
                )
           (symbol-listp (lambda-formals (car tree))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd pseudo-termp-of-lambda-body-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)) ;it's a lambda
                )
           (pseudo-termp (car (cdr (cdr (car tree))))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd len-when-equal-of-car-and-quote-and-axe-treep
  (implies (and (equal 'quote (car tree))
                (axe-treep tree))
           (equal (len tree)
                  2))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthmd consp-of-cdr-when-equal-of-car-and-quote-and-axe-treep
  (implies (and (equal 'quote (car tree))
                (axe-treep tree))
           (consp (cdr tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable axe-treep))))

;; Pseudo-terms are axe-trees.
(defthm-flag-axe-treep
  (defthm axe-treep-when-pseudo-termp
    (implies (pseudo-termp tree)
             (axe-treep tree))
    :flag axe-treep)
  (defthm axe-tree-listp-when-pseudo-term-listp
    (implies (pseudo-term-listp trees)
             (axe-tree-listp trees))
    :flag axe-tree-listp))

;; dargps are axe-trees.
(defthm-flag-axe-treep
  (defthm axe-treep-when-dargp
    (implies (dargp tree)
             (axe-treep tree))
    :flag axe-treep)
  (defthm axe-tree-listp-when-all-dargp
    (implies (all-dargp trees)
             (equal (axe-tree-listp trees)
                    (true-listp trees)))
    :flag axe-tree-listp))

(defthm axe-tree-listp-of-cons
  (equal (axe-tree-listp (cons tree trees))
         (and (axe-treep tree)
              (axe-tree-listp trees)))
  :hints (("Goal" :in-theory (enable axe-tree-listp))))

(defthm axe-tree-listp-forward-to-true-listp
  (implies (axe-tree-listp trees)
           (true-listp trees))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-tree-listp))))

(defthm axe-treep-of-cons
  (implies (and (symbolp fn)
                (not (equal 'quote fn)))
           (equal (axe-treep (cons fn args))
                  (axe-tree-listp args)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthm axe-tree-listp-of-cdr
  (implies (and (axe-treep tree)
                (consp tree)
                (not (equal 'quote (car tree))))
           (axe-tree-listp (cdr tree))))

(defthm axe-tree-listp-of-cdr-2
  (implies (axe-tree-listp trees)
           (axe-tree-listp (cdr trees))))

(defthm axe-treep-of-car
  (implies (and (axe-tree-listp trees)
                ;; (consp trees)
                )
           (axe-treep (car trees))))

(defthm axe-treep-compound-recognizer
  (implies (axe-treep tree)
           (or (and (consp tree)
                    (true-listp tree))
               (symbolp tree)
               (natp tree)))
  :rule-classes :compound-recognizer)

;TODO: disable outside axe
(defthm symbolp-of-car-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (not (consp (car tree))))
           (symbolp (car tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

(defthm len-of-nth-1-of-car-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (equal (len (nth 1 (car tree))) ;the lambda formals
                  (len (cdr tree))         ;the args
                  ))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm len-of-nth-1-of-nth-0-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (equal (len (nth 1 (nth 0 tree))) ;the lambda formals
                  (len (cdr tree))         ;the args
                  ))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm axe-treep-of-nth-2-of-car-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (axe-treep (nth 2 (car tree))) ;the lambda body
           )
  :hints (("Goal" :expand ((axe-treep tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm axe-treep-of-nth-2-of-nth-0-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (consp (nth 0 tree)))
           (axe-treep (nth 2 (nth 0 tree))) ;the lambda body
           )
  :hints (("Goal" :expand ((axe-treep tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm axe-treep-when-equal-of-car-and-quote-cheap
  (implies (equal 'quote (car tree))
           (equal (axe-treep tree)
                  (myquotep tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm symbol-of-nth-0-when-axe-treep
  (implies (axe-treep tree)
           (equal (symbolp (nth 0 tree))
                  (not (consp (nth 0 tree)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm symbol-listp-of-nth1-of-nth-0-when-axe-treep
  (implies (axe-treep tree)
           (symbol-listp (nth 1 (nth 0 tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand ((axe-treep tree))
           :in-theory (enable axe-treep))))

(defthm consp-of-cddr-of-nth-0-when-axe-treep
  (implies (axe-treep tree)
           (equal (consp (cddr (nth 0 tree)))
                  (consp (nth 0 tree))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand ((axe-treep tree))
           :in-theory (enable axe-treep))))

(defthm cdr-of-nth-0-when-axe-treep-iff
  (implies (axe-treep tree)
           (iff (cdr (nth 0 tree))
                (consp (nth 0 tree))))
    :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :expand ((axe-treep tree))
           :in-theory (enable axe-treep))))

(defthm len-of-nth-0-when-axe-treep-cheap
  (implies (axe-treep tree)
           (equal (len (nth 0 tree))
                  (if (consp (nth 0 tree))
                      3
                      0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm axe-treep-of-nth
  (implies (and (axe-tree-listp trees)
                ;; (consp trees)
                )
           (axe-treep (nth n trees)))
  :hints (("Goal" :in-theory (enable axe-tree-listp nth))))

(defthm true-listp-of-nth-1-of-nth-0-when-axe-treep
  (implies (and ;(bounded-axe-treep tree bound2) ;free var
;                (<= bound bound2)
            (axe-treep tree)
            (consp (car tree)))
           (TRUE-LISTP (NTH 1 (NTH 0 TREE))) ;the lambda formals
           )
  :hints (("Goal" :expand ((axe-treep tree)
                           ;;(bounded-axe-treep tree bound2)
                           ))))

(defthm myquotep-when-axe-treep
  (implies (and (syntaxp (want-to-weaken (myquotep x)))
                (axe-treep x))
           (equal (myquotep x)
                  (equal 'quote (car x)))))

(defthm axe-treep-of-cons-strong
  (equal (axe-treep (cons fn args))
         (if (equal 'quote fn)
             (and (= 1 (len args))
                  (true-listp args))
           (and (axe-tree-listp args)
                (true-listp args)
                (or (symbolp fn)
                    (and (true-listp fn)
                         (equal (len fn) 3)
                         (eq (car fn) 'lambda)
                         (symbol-listp (cadr fn))
                         (pseudo-termp (caddr fn))
                         (equal (len (cadr fn))
                                (len args)))))))
  :hints (("Goal" :in-theory (enable axe-treep))))

(defthm axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (all-dargp (strip-cdrs alist))
                ;; (assoc-equal form alist)
                )
           (axe-treep (cdr (assoc-equal form alist))))
  :hints (("Goal" :use (:instance dargp-of-cdr-of-assoc-equal (var form))
           :in-theory (disable dargp-of-cdr-of-assoc-equal))))

(defthm axe-treep-when-not-consp-and-not-symbolp-cheap
  (implies (and (not (consp tree))
                (not (symbolp tree)))
           (equal (axe-treep tree)
                  (natp tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable axe-treep))))

;enable?
(defthmd axe-treep-when-consp-of-car
  (implies (consp (car tree))
           (equal (axe-treep tree)
                  (and (axe-tree-listp (fargs tree))
                       (true-listp (car tree))
                       (equal (len (car tree)) 3)
                       (eq (car (car tree)) 'lambda)
                       (symbol-listp (cadr (car tree)))
                       (pseudo-termp (caddr (car tree))) ;todo: can an axe tree appear here?
                       (equal (len (cadr (car tree)))
                              (len (fargs tree))))))
  :hints (("Goal" :in-theory (enable axe-treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;; Check that all nodenums in TREE are less than BOUND.
 ;; TODO: Perhaps rename to is-bounded-axe-treep.
 ;; TODO: Change this to imply axe-treep, so we don't have to say both.
 (defund bounded-axe-treep (tree bound)
   (declare (xargs :guard (integerp bound)))
   (if (atom tree)
       (or (symbolp tree)   ; a variable
           (and (natp tree) ; a nodenum
                (< tree bound)))
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           ;; a quoted constant;
           (and (= 1 (len (fargs tree)))
                (true-listp (fargs tree)))
         ;; the application of a function symbol or lambda to args that are axe trees:
         ;; TODO: Can we require the lambda to be closed?
         (and (bounded-axe-tree-listp (fargs tree) bound)
              (true-listp (fargs tree))
              (or (symbolp fn)
                  (and (true-listp fn)
                       (equal (len fn) 3)
                       (eq (car fn) 'lambda)
                       (symbol-listp (cadr fn))
                       ;; lambda body is a regular, pseudo-term, not an axe-tree:
                       (pseudo-termp (caddr fn))
                       (equal (len (cadr fn))
                              (len (fargs tree))))))))))

 (defund bounded-axe-tree-listp (trees bound)
   (declare (xargs :guard (integerp bound)))
   (if (atom trees)
       (null trees)
     (and (bounded-axe-treep (first trees) bound)
          (bounded-axe-tree-listp (rest trees) bound)))))

(defthm-flag-axe-treep
  (defthm bounded-axe-treep-forward-to-axe-treep
    (implies (bounded-axe-treep tree bound)
             (axe-treep tree))
    :rule-classes :forward-chaining
    :flag axe-treep)
  (defthm bounded-axe-tree-listp-forward-to-axe-tree-listp
    (implies (bounded-axe-tree-listp trees bound)
             (axe-tree-listp trees))
    :rule-classes :forward-chaining
    :flag axe-tree-listp)
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp
                                     bounded-axe-treep
                                     axe-tree-listp
                                     axe-treep))))

(defthm axe-treep-when-bounded-axe-treep
  (implies (bounded-axe-treep tree bound)
           (axe-treep tree)))

(defthm axe-treep-of-car-when-bounded-axe-tree-listp
  (implies (bounded-axe-tree-listp trees bound)
           (axe-treep (car trees))))

(defthmd bounded-axe-treep-when-natp
  (implies (and (natp tree)
                (< tree bound))
           (bounded-axe-treep tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm bounded-axe-treep-when-natp-forward
  (implies (and (bounded-axe-treep tree bound)
                (natp tree)
                (natp bound))
           (<= tree (+ -1 bound)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthmd bounded-axe-treep-when-dargp-less-than
  (implies (dargp-less-than tree bound)
           (bounded-axe-treep tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep dargp-less-than))))

(defthm bounded-axe-treep-when-dargp-less-than-cheap
  (implies (dargp-less-than item bound)
           (bounded-axe-treep item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep dargp-less-than))))

;; (defthmd bounded-axe-treep-when-not-consp
;;   (implies (and (not (consp tree))
;;                 (axe-treep tree))
;;            (equal (bounded-axe-treep tree bound)
;;                   (or (symbolp tree)
;;                       (dargp-less-than tree bound))))
;;   :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm bounded-axe-treep-of-cons
  (equal (bounded-axe-treep (cons fn args) bound)
         (if (equal 'quote fn)
             (and (= 1 (len args))
                  (true-listp args))
           (and (bounded-axe-tree-listp args bound)
                (or (symbolp fn)
                    (and (true-listp fn)
                         (equal (len fn) 3)
                         (eq (car fn) 'lambda)
                         (symbol-listp (cadr fn))
                         (pseudo-termp (caddr fn))
                         (equal (len (cadr fn))
                                (len args)))))))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm bounded-axe-tree-listp-of-cons
  (equal (bounded-axe-tree-listp (cons tree trees) bound)
         (and (bounded-axe-treep tree bound)
              (bounded-axe-tree-listp trees bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp))))

(defthm bounded-axe-tree-listp-when-all-dargp
  (implies (and (all-dargp items)
                )
           (equal (bounded-axe-tree-listp items bound)
                  (bounded-darg-listp items bound)))
  :hints (("Goal" :expand ((bounded-axe-treep (car items) bound)
                           (bounded-axe-tree-listp items bound))
           :induct t
           :in-theory (enable bounded-axe-tree-listp bounded-darg-listp))))

(defthm bounded-axe-tree-listp-when-not-consp
  (implies (not (consp trees))
           (equal (bounded-axe-tree-listp trees bound)
                  (equal trees nil)))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp))))

;; Pseudo terms have no nodenums in them, so any bound works.
(defthm-flag-axe-treep
  (defthm bounded-axe-treep-when-pseudo-termp
    (implies (pseudo-termp tree)
             (bounded-axe-treep tree bound))
    :flag axe-treep)
  (defthm bounded-axe-tree-listp-when-pseudo-term-listp
    (implies (pseudo-term-listp trees)
             (bounded-axe-tree-listp trees bound))
    :flag axe-tree-listp)
  :hints (("Goal" :in-theory (enable bounded-axe-treep
                                     bounded-axe-tree-listp))))

(defthm-flag-axe-treep
  (defthm bounded-axe-treep-mono
    (implies (and (bounded-axe-treep tree bound2)
                  (<= bound2 bound)
                  ;(axe-treep tree)
                  )
             (bounded-axe-treep tree bound))
    :flag axe-treep)
  (defthm bounded-axe-tree-listp-mono
    (implies (and (bounded-axe-tree-listp trees bound2)
                  (<= bound2 bound)
                  ;(axe-tree-listp trees)
                  )
             (bounded-axe-tree-listp trees bound))
    :flag axe-tree-listp)
  :hints (("Goal" :in-theory (enable bounded-axe-treep
                                     bounded-axe-tree-listp))))

(defthm bounded-axe-tree-listp-of-cdr-2
  (implies (and (bounded-axe-treep tree bound)
                (not (equal 'quote (car tree))))
           (bounded-axe-tree-listp (cdr tree) bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

;todo: disable outside of axe...
(defthm <-when-bounded-axe-treep
  (implies (and (bounded-axe-treep tree bound2)
                (<= bound2 bound)
                ;; or rewrite bounded-axe-treep when these are true:
                (not (consp tree))
                (not (symbolp tree)))
           (< tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm bounded-axe-treep-of-car
  (implies (bounded-axe-tree-listp trees dag-len)
           (bounded-axe-treep (car trees) dag-len))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp))))

(defthm bounded-axe-tree-listp-of-cdr
  (implies (bounded-axe-tree-listp trees dag-len)
           (bounded-axe-tree-listp (cdr trees) dag-len))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp))))

;; because it's a pseudo-term
(defthm bounded-axe-treep-of-nth-2-of-car
  (implies (and ;(bounded-axe-treep tree bound2) ;free var
;                (<= bound bound2)
            (axe-treep tree)
            (consp (car tree)))
           (bounded-axe-treep (nth 2 (car tree)) bound) ;the lambda body
           )
  :hints (("Goal" :expand ((axe-treep tree)
                           ;;(bounded-axe-treep tree bound2)
                           ))))

(defthm bounded-axe-treep-of-nth-2-of-car-alt
  (implies (and ;(bounded-axe-treep tree bound2) ;free var
;                (<= bound bound2)
            (axe-treep tree)
            (consp (car tree)))
           (bounded-axe-treep (nth 2 (nth 0 tree)) bound) ;the lambda body
           )
  :hints (("Goal" :expand ((axe-treep tree)
                           ;;(bounded-axe-treep tree bound2)
                           ))))

(defthm bounded-axe-treep-of-nth
  (implies (bounded-axe-tree-listp trees dag-len)
           (bounded-axe-treep (nth n trees) dag-len))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp nth))))

(defthm bounded-axe-treep-of-nth-gen
  (implies (and (bounded-axe-tree-listp args bound2)
                ;(axe-tree-listp args)
                (<= bound2 bound)
                ;;(< n (len args))
                )
           (bounded-axe-treep (nth n args) bound))
  :hints (("Goal" :expand (bounded-axe-tree-listp args bound2)
           :in-theory (e/d (bounded-axe-tree-listp (:i nth)) ( ;nth-of-cdr
                                                             )))))

(defthm bounded-axe-tree-listp-of-append
  (equal (bounded-axe-tree-listp (append x y) bound)
         (and (bounded-axe-tree-listp (true-list-fix x) bound)
              (bounded-axe-tree-listp y bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-tree-listp append))))

(defthm bounded-axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (bounded-darg-listp (strip-cdrs alist) dag-len)
                ;; (assoc-equal form alist)
                )
           (bounded-axe-treep (cdr (assoc-equal form alist)) dag-len))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

(defthmd bounded-axe-treep-when-natp-strong
  (implies (natp tree)
           (equal (bounded-axe-treep tree bound)
                  (< tree bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))
