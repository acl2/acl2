; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ convenience-constructors
  :parents (abstract-syntax)
  :short "Utilities to convniently construct PFCS abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions and macros have short and evocative names,
     to support the concise and readable construction of (constituents of) rules
     in the abstract syntax."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define yyyjoin (fn rev-args)
  :short "Spread a binary function over two or more arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the builtin @('xxxjoin'),
     but it associates left instead of right,
     and arguments are passed reversed."))
  :mode :program
  (if (cdr (cdr rev-args))
      (list fn (yyyjoin fn (cdr rev-args)) (car rev-args))
    (list fn (second rev-args) (first rev-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfconst (c)
  :short "Construct a constant expression."
  `(pfcs::expression-const ,c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfvar (v)
  :short "Construct a variable expression."
  `(pfcs::expression-var ,v))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfmon (c v)
  :short "Construct a monomial, i.e. a product of a constant by a variable."
  `(pfcs::expression-mul (pfcs::expression-const ,c)
                         (pfcs::expression-var ,v)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pf* (&rest exprs)
  :short "Construct a multiplication of any number of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no expressions,
     we return the constant expression 1.")
   (xdoc::p
    "If there is just one expression,
     we return it.")
   (xdoc::p
    "If there are two or more expressions,
     we return their left-associated product."))
  (cond ((endp exprs) '(pfconst 1))
        ((endp (cdr exprs)) (car exprs))
        (t (yyyjoin 'pfcs::expression-mul (rev exprs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pf+ (&rest exprs)
  :short "Construct an addition of any number of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no expressions,
     we return the constant expression 0.")
   (xdoc::p
    "If there is just one expression,
     we return it.")
   (xdoc::p
    "If there are two or more expressions,
     we return their left-associated sum."))
  (cond ((endp exprs) '(pfconst 0))
        ((endp (cdr exprs)) (car exprs))
        (t (yyyjoin 'pfcs::expression-add (rev exprs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pf= (left right)
  :short "Construct an equality constraint."
  `(pfcs::make-constraint-equal :left ,left :right ,right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfdef (defname params &rest constraints)
  :short "Construct a definition with zero or more constraints."
  `(pfcs::make-definition
    :name ,defname
    :para ,params
    :body (list ,@constraints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfcall (name &rest args)
  :short "Construct a relation call constraint."
  `(pfcs::make-constraint-relation :name ,name :args (list ,@args)))
