; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "initializer-validation")
(include-book "validation-tables")
(include-book "validation-annotations")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (validation)
  :short "Information calculated and used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see validator) calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes.")
   (xdoc::p
    "We also introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: This evaluates the expression, which might be a bit expensive. Ideally
;; we would be annotating expressions with values as we go.
(define expr-null-pointer-constp ((expr exprp) (type typep) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check whether an expression of a given type is potentially a null
          pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring-p
   "A null pointer constant is an integer constant expression with value 0
    or a cast of such an expression to a void pointer [C17:6.3.2.3/3].
    This check is currently overapproximate.
    Our evaluation may yield an unknown value,
    in which case we consider the expression
    to possibly be a null pointer constant.
    Similarly, we don't check that the expression
    is an integer constant expression
    or a cast of an integer constant expression to a void pointer.")
  (type-case
   type
   :unknown t
   :pointer (b* (((unless (or (type-case type.to :void)
                              (type-case type.to :unknown)))
                  nil)
                 (val (const-eval-expr expr ienv)))
              (value-case
                val
                :unknown t
                :pointer (pointer-case
                           val.get
                           :unknown t
                           :non-null nil
                           :null t)
                :otherwise nil))
   :otherwise (b* (((unless (type-integerp type))
                    nil)
                   (val (const-eval-expr expr ienv))
                   ((when (value-case val :unknown))
                    t)
                   (int? (value-to-integer val)))
                (or (not int?)
                    (equal int? 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-expr-null-pointer-constp ((const-expr const-exprp)
                                        (type typep)
                                        (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check whether a constant expression of a given type is potentially a
          null pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee expr-null-pointer-constp)."))
  (b* (((const-expr const-expr) const-expr))
    (expr-null-pointer-constp const-expr.expr type ienv)))
