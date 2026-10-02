; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/string-set" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bound-variable-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for retrieving bound variables from ASTs."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-ispace-vars ((bind bindp))
  :returns (vars ispace-var-setp)
  :short "Set of ispace variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only an ispace binding binds an ispace variable.
     An ispace function binding does not bind ispace variables:
     it binds an expression variable;
     the ispace parameters of the function are handled separately,
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace (set::insert bind.var nil)
   :type nil
   :val nil
   :fun nil
   :tfun nil
   :ifun nil
   :cfun nil))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-ispace-vars ((binds bind-listp))
  :returns (vars ispace-var-setp)
  :short "Set of ispace variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-ispace-vars (car binds))
                       (bind-list-bound-ispace-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-type-vars ((bind bindp))
  :returns (vars type-var-setp)
  :short "Set of type variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only a type binding binds a type variable.
     A type function binding does not bind type variables:
     it binds an expression variable;
     the type parameters of the function are handled separately,
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace nil
   :type (set::insert bind.var nil)
   :val nil
   :fun nil
   :tfun nil
   :ifun nil
   :cfun nil))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-type-vars ((binds bind-listp))
  :returns (vars type-var-setp)
  :short "Set of type variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-type-vars (car binds))
                       (bind-list-bound-type-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-expr-vars ((bind bindp))
  :returns (vars string-setp)
  :short "Set of expression variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value and function bindings each bind an expression variable;
     the ispace and type bindings do not bind expression variables.
     The parameters of the @(':fun') and @(':cfun') bindings
     are not included here:
     they are bound within the function's own body,
     and are handled separately
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace nil
   :type nil
   :val (set::insert bind.var nil)
   :fun (set::insert bind.var nil)
   :tfun (set::insert bind.var nil)
   :ifun (set::insert bind.var nil)
   :cfun (set::insert bind.var nil)))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-expr-vars ((binds bind-listp))
  :returns (vars string-setp)
  :short "Set of expression variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-expr-vars (car binds))
                       (bind-list-bound-expr-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-expr-var-list ((bind bindp))
  :returns (vars string-listp)
  :short "List of the (at most one) expression variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list counterpart of @(tsee bind-bound-expr-vars),
     for use with @(tsee expr-subst-alpha-bound),
     which takes its bound variables as a list.
     The value,
     function,
     type-function,
     ispace-function,
     and combined-function
     bindings each bind an expression variable;
     the ispace and type bindings do not."))
  (bind-case bind
             :val (list bind.var)
             :fun (list bind.var)
             :tfun (list bind.var)
             :ifun (list bind.var)
             :cfun (list bind.var)
             :otherwise nil))
