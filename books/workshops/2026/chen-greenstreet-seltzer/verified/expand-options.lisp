;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 19th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(define fn-sym-p ((fn acl2::any-p))
  :returns (ok booleanp)
  (and (symbolp fn)
       fn
       (not (equal fn 'quote))
       (not (equal fn 'if))))

(easy-fix fn-sym 'smt::bad-function)
(deflist fn-sym-list
  :elt-type fn-sym-p
  :pred fn-sym-list-p
  :true-listp t)

(local (in-theory (enable fn-sym-p fn-sym-fix pseudo-termp)))
(more-returns fn-sym-p
  (ok :name symbolp-when-fn-sym-p
    (implies ok (symbolp fn))
    :rule-classes (:forward-chaining :rewrite)))

(more-returns fn-sym-fix
  (fix-x :name pseudo-termp-of-call-of-fn-sym-fix
     (implies (pseudo-term-listp args)
	      (pseudo-termp (cons fix-x args))))
  (fix-x :name fn-sym-fix-not-quote
     (not (equal fix-x 'quote)))
  (fix-x :name fn-sym-fix-not-if
     (not (equal fix-x 'if))))
(local (in-theory (disable fn-sym-p fn-sym-fix pseudo-termp)))

(defprod expand-options
  ((functions symbol-smt-function-alist-p)
   (expand-with-vars booleanp)
   (type-recognizers fn-sym-list-p)
   (wrld-fn-len natp)))

(define construct-function-info ((func-lst smt-function-list-p))
  :returns (alst symbol-smt-function-alist-p)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst)
       (name (smt-function->name func-hd)))
    (acons name func-hd (construct-function-info func-tl))))

(define find-acl2types ((acl2types smt-acl2type-list-p) (acc fn-sym-list-p))
  :returns (type-recognizers fn-sym-list-p)
  (b* ((acc (fn-sym-list-fix acc))
       ((unless (consp acl2types)) acc)
       ((cons hd tl) acl2types)
       (recognizer (smt-acl2type->recognizer hd))
       ((unless (fn-sym-p recognizer))
	(cw "bad symbol for type recognizer: ~q0~%" recognizer)))
    (find-acl2types tl (cons recognizer acc))))

(define find-datatypes ((datatypes smt-datatype-list-p) (acc fn-sym-list-p))
  :returns (type-recognizers fn-sym-list-p)
  (b* ((acc (fn-sym-list-fix acc))
       ((unless (consp datatypes)) acc)
       ((cons hd tl) datatypes)
       (recognizer (smt-function->name (smt-datatype->recognizer hd)))
       ((unless (fn-sym-p recognizer))
	(cw "bad symbol for type recognizer: ~q0~%" recognizer)))
    (find-datatypes tl (cons recognizer acc))))

(define find-recognizers ((h smtlink-hint-p))
  :returns (type-recognizers fn-sym-list-p)
  (b* (((smtlink-hint h) (smtlink-hint-fix h)))
    (find-acl2types h.acl2types (find-datatypes h.datatypes nil))))

(define construct-expand-options ((hints smtlink-hint-p))
  :returns (eo expand-options-p)
  (b* (((smtlink-hint h) (smtlink-hint-fix hints))
       (functions (construct-function-info h.functions))
       (type-recognizers (find-recognizers h)))
    (make-expand-options :functions functions
                         :expand-with-vars h.expand-with-vars
			 :type-recognizers type-recognizers
                         :wrld-fn-len h.wrld-fn-len)))
