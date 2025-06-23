; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-trees")

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

(define constraint/constraintlist-p (x)
  :returns (yes/no booleanp)
  :short "Recognize constraints and lists of constraints."
  (or (constraintp x)
      (constraint-listp x))
  ///

  (defrule constraint/constraintlist-p-when-constraintp
    (implies (constraintp x)
             (constraint/constraintlist-p x)))

  (defrule constraint/constraintlist-p-when-constraint-listp
    (implies (constraint-listp x)
             (constraint/constraintlist-p x)))

  (defruled not-constraintp-when-constraint-listp
    (implies (constraint-listp x)
             (not (constraintp x)))
    :enable constraintp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist constraint/constraintlist-listp (x)
  :short "Recognize lists of constraints and lists of constraints."
  (constraint/constraintlist-p x)
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfname (&rest args)
  (declare (xargs :guard (and (consp args)
                              (or (endp (cdr args))
                                  (and (consp (cdr args))
                                       (endp (cddr args)))))))
  :short "Construct a name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro accepts one or two arguments.
     If one argument is passed, it must be a string,
     and the macro returns a simple name containing that string.
     If two arguments are passed, they must be a string and a natural number,
     and the macro returns an indexed name
     containing the string and natural number."))
  (if (consp (cdr args))
      `(name-indexed ,(car args) ,(cadr args))
    `(name-simple ,(car args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfconst (c)
  :short "Construct a constant expression from an integer."
  `(expression-const ,c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfvar (v)
  :short "Construct a variable expression from a name."
  `(expression-var ,v))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfmon (c v)
  :short "Construct a monomial, i.e. a product of a constant by a variable,
          from an integer and a name."
  `(expression-mul (expression-const ,c)
                   (expression-var ,v)))

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
        (t (yyyjoin 'expression-mul (rev exprs)))))

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
        (t (yyyjoin 'expression-add (rev exprs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pf= (left right)
  :short "Construct an equality constraint."
  `(make-constraint-equal :left ,left :right ,right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfdef
  :short "Construct a definition with zero or more constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each of the @('constraints') arguments of this macro may be
     either (a term returning) a single constraint
     or (a term returning) a list of constraints.")
   (xdoc::@def "pfdef"))

  (define pfdef-join ((list constraint/constraintlist-listp))
    :returns (constrs constraint-listp)
    :parents nil
    (b* (((when (endp list)) nil)
         (first (car list)))
      (cond ((constraintp first) (cons first (pfdef-join (cdr list))))
            ((constraint-listp first) (append first (pfdef-join (cdr list))))
            (t (acl2::impossible))))
    :enabled t
    :guard-hints (("Goal" :in-theory (enable constraint/constraintlist-p))))

  (defmacro pfdef (defname params &rest constraints)
    `(make-definition
      :name ,defname
      :para ,params
      :body (pfdef-join (list ,@constraints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ pfcall (name &rest args)
  :short "Construct a relation call constraint."
  `(make-constraint-relation :name ,name :args (list ,@args)))
