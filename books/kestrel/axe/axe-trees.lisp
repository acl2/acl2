; Axe trees
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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
(include-book "all-dargp")
(include-book "dargp-less-than")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;todo: can variables always occur?
;like pseudo-termp but allows integers (nodenums in some DAG) to also appear
;might also need to be able to say that the nodenums are in range
(mutual-recursion
 (defun axe-treep (tree)
   (declare (xargs :guard t))
   (if (atom tree)
       (or (symbolp tree)
           (natp tree) ;a nodenum
           )
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           (and (= 1 (len (fargs tree)))
                (true-listp (fargs tree)))
         (and (all-axe-treep (fargs tree))
              (true-listp (fargs tree))
              (or (symbolp fn)
                  (and (true-listp fn)
                       (equal (len fn) 3)
                       (eq (car fn) 'lambda)
                       (symbol-listp (cadr fn))
                       (pseudo-termp (caddr fn)) ;todo: can an axe tree appear here?
                       (equal (len (cadr fn))
                              (len (fargs tree))))))))))
 (defun all-axe-treep (trees)
   (declare (xargs :guard t))
   (if (atom trees)
       t
     (and (axe-treep (first trees))
          (all-axe-treep (rest trees))))))

(make-flag axe-treep)

(defthm all-axe-treep-of-append
  (equal (all-axe-treep (append x y))
         (and (all-axe-treep x)
              (all-axe-treep y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable all-axe-treep append))))

;; Pseudo-terms are axe-trees.
(defthm-flag-axe-treep
  (defthm axe-treep-when-pseudo-termp
    (implies (pseudo-termp tree)
             (axe-treep tree))
    :flag axe-treep)
  (defthm all-axe-treep-when-pseudo-term-listp
    (implies (pseudo-term-listp trees)
             (all-axe-treep trees))
    :flag all-axe-treep))

;; dargps are axe-trees.
(defthm-flag-axe-treep
  (defthm axe-treep-when-dargp
    (implies (dargp tree)
             (axe-treep tree))
    :flag axe-treep)
  (defthm all-axe-treep-when-all-dargp
    (implies (all-dargp trees)
             (all-axe-treep trees))
    :flag all-axe-treep))

(defthm axe-treep-of-cons
  (implies (and (symbolp fn)
                (not (equal 'quote fn)))
           (equal (axe-treep (cons fn args))
                  (and (all-axe-treep args)
                       (true-listp args))))
  :hints (("Goal" :in-theory (enable axe-treep))))


(mutual-recursion
 ;; Check that all nodenums in TREE are less than BOUND.
 (defun bounded-axe-treep (tree bound)
   (declare (xargs :guard (and (axe-treep tree)
                               (integerp bound))))
   (if (atom tree)
       (if (symbolp tree)
           t
         (< tree bound))
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           t
         (all-bounded-axe-treep (fargs tree) bound) ;todo: can nodenums appear in the lambda body?
         ))))

 (defun all-bounded-axe-treep (trees bound)
   (declare (xargs :guard (and (all-axe-treep trees)
                               (integerp bound))))
   (if (atom trees)
       t
     (and (bounded-axe-treep (first trees) bound)
          (all-bounded-axe-treep (rest trees) bound)))))

(defthmd bounded-axe-treep-when-natp
  (implies (and (natp tree)
                (< tree bound))
           (bounded-axe-treep tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthmd bounded-axe-treep-when-dargp-less-than
  (implies (dargp-less-than tree bound)
           (bounded-axe-treep tree bound))
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
         (if (eq fn 'quote)
             t
           (all-bounded-axe-treep args bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm all-bounded-axe-treep-of-cons
  (equal (all-bounded-axe-treep (cons tree trees) bound)
         (and (bounded-axe-treep tree bound)
              (all-bounded-axe-treep trees bound)))
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep))))

(defthm all-axe-treep-of-cdr
  (implies (and (axe-treep tree)
                (consp tree)
                (not (equal 'quote (car tree))))
           (all-axe-treep (cdr tree))))

(defthm all-axe-treep-of-cdr-2
  (implies (all-axe-treep trees)
           (all-axe-treep (cdr trees))))

(defthm axe-treep-of-car
  (implies (and (all-axe-treep trees)
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

;; Pseudo terms have no nodenums in them, so any bound works.
(defthm-flag-axe-treep
  (defthm bounded-axe-treep-when-pseudo-termp
    (implies (pseudo-termp tree)
             (bounded-axe-treep tree bound))
    :flag axe-treep)
  (defthm all-bounded-axe-treep-when-pseudo-term-listp
    (implies (pseudo-term-listp trees)
             (all-bounded-axe-treep trees bound))
    :flag all-axe-treep))

(defthm-flag-axe-treep
  (defthm bounded-axe-treep-mono
    (implies (and (bounded-axe-treep tree bound2)
                  (<= bound2 bound)
                  (axe-treep tree))
             (bounded-axe-treep tree bound))
    :flag axe-treep)
  (defthm all-bounded-axe-treep-mono
    (implies (and (all-bounded-axe-treep trees bound2)
                  (<= bound2 bound)
                  (all-axe-treep trees))
             (all-bounded-axe-treep trees bound))
    :flag all-axe-treep))

(defthm all-bounded-axe-treep-of-cdr-2
  (implies (and (bounded-axe-treep tree bound)
                (consp tree)
                (not (equal 'quote (car tree))))
           (all-bounded-axe-treep (cdr tree) bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(in-theory (disable bounded-axe-treep
                    all-bounded-axe-treep))

;disable outside axe
(defthm symbolp-of-car-when-axe-treep-cheap
  (implies (and (axe-treep tree)
                (not (consp (car tree))))
           (symbolp (car tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

;todo: disable outside of axe...
(defthm <-when-bounded-axe-treep
  (implies (and (bounded-axe-treep tree bound2)
                (<= bound2 bound)
                (not (consp tree))
                (not (symbolp tree)))
           (< tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

(defthm bounded-axe-treep-of-car
  (implies (all-bounded-axe-treep trees dag-len)
           (bounded-axe-treep (car trees) dag-len))
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep))))

(defthm all-bounded-axe-treep-of-cdr
  (implies (all-bounded-axe-treep trees dag-len)
           (all-bounded-axe-treep (cdr trees) dag-len))
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep))))

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
  (implies (and (all-axe-treep trees)
                ;; (consp trees)
                )
           (axe-treep (nth n trees)))
  :hints (("Goal" :in-theory (enable all-axe-treep nth))))

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

(defthm bounded-axe-treep-of-nth
  (implies (all-bounded-axe-treep trees dag-len)
           (bounded-axe-treep (nth n trees) dag-len))
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep nth))))

(defthm bounded-axe-treep-of-nth-gen
  (implies (and (all-bounded-axe-treep args bound2)
                (all-axe-treep args)
                (<= bound2 bound)
                ;;(< n (len args))
                )
           (bounded-axe-treep (nth n args) bound))
  :hints (("Goal" :expand (all-bounded-axe-treep args bound2)
           :in-theory (e/d (all-bounded-axe-treep (:i nth)) ( ;nth-of-cdr
                                                             )))))

(defthm all-bounded-axe-treep-of-append
  (equal (all-bounded-axe-treep (append x y) bound)
         (and (all-bounded-axe-treep x bound)
              (all-bounded-axe-treep y bound)))
  :hints (("Goal" :in-theory (enable all-bounded-axe-treep append))))

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
           (and (all-axe-treep args)
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
                (assoc-equal form alist))
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

(defthmd bounded-axe-treep-when-natp-strong
  (implies (natp tree)
           (equal (bounded-axe-treep tree bound)
                  (< tree bound)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep))))

;enable?
(defthmd axe-treep-when-consp-of-car
  (implies (consp (car tree))
           (equal (axe-treep tree)
                  (and (all-axe-treep (fargs tree))
                       (true-listp (fargs tree))
                       (true-listp (car tree))
                       (equal (len (car tree)) 3)
                       (eq (car (car tree)) 'lambda)
                       (symbol-listp (cadr (car tree)))
                       (pseudo-termp (caddr (car tree))) ;todo: can an axe tree appear here?
                       (equal (len (cadr (car tree)))
                              (len (fargs tree))))))
  :hints (("Goal" :in-theory (enable axe-treep))))
