; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bound-and-free-variable-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for retrieving bound and free variables from ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide operations to collect
     bound, free, and all (i.e. bound and free)
     ispace, type, and expression variables."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-ispace-vars
  :short "Set of free ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The free variables of a binder are the ones
     in the thing that the variable is bound to.
     Thus, for the ispace and combined function binders,
     we remove the parameters,
     because the thing that the variable is bound to
     is like a lambda abstraction.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we need to override the function for @(tsee bind-list)
     to remove, from the free variables of
     the @(tsee cdr) of a non-empty list of bindings,
     the free variable (if any) bound in the @(tsee car) of the list.
     For the body of a @('let') expression,
     we just remove all the variables bound in the bindings."))
  :types (dims
          shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds
          string-dim-map
          string-shape-map)
  :result ispace-var-setp
  :default nil
  :combine set::union
  :override
  ((dim :var (set::insert (ispace-var-dim dim.name) nil))
   (shape :var (set::insert (ispace-var-shape shape.name) nil))
   (type :pi (set::delete type.param (type-free-ispace-vars type.body)))
   (type :pin
         (set::difference (type-free-ispace-vars type.body)
                          (set::mergesort type.params)))
   (type :sigma
         (set::difference (type-free-ispace-vars type.body)
                          (set::mergesort type.params)))
   (expr :unbox
         (set::union (expr-free-ispace-vars expr.target)
                     (set::difference (expr-free-ispace-vars expr.body)
                                      (set::mergesort expr.ispaces))))
   (expr :let
         (set::union
          (bind-list-free-ispace-vars expr.binds)
          (set::difference (expr-free-ispace-vars expr.body)
                           (bind-list-bound-ispace-vars expr.binds))))
   (atom :ilambda (set::delete atom.param (expr-free-ispace-vars atom.body)))
   (atom :ilambdan
         (set::difference (expr-free-ispace-vars atom.body)
                          (set::mergesort atom.params)))
   (bind :ifun
         (set::difference (set::union (type-option-free-ispace-vars bind.type?)
                                      (expr-free-ispace-vars bind.expr))
                          (set::mergesort bind.params)))
   (bind :cfun
         (set::difference (set::union
                           (var+type?-list-free-ispace-vars bind.params)
                           (set::union (type-free-ispace-vars bind.type)
                                       (expr-free-ispace-vars bind.expr)))
                          (ispace-var-list-option-case
                           bind.iparams?
                           :some (set::mergesort bind.iparams?.val)
                           :none nil)))
   (bind-list (b* (((when (endp bind-list)) nil)
                   (bind (car bind-list)))
                (set::union (bind-free-ispace-vars bind)
                            (set::difference
                             (bind-list-free-ispace-vars (cdr bind-list))
                             (bind-bound-ispace-vars bind))))))
  :name ast-free-ispace-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-type-vars
  :short "Set of free type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The free variables of a binder are the ones
     in the thing that the variable is bound to.
     Thus, for the type and combined function binders,
     we remove the parameters,
     because the thing that the variable is bound to
     is like a lambda abstraction.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we need to override the function for @(tsee bind-list)
     to remove, from the free variables of
     the @(tsee cdr) of a non-empty list of bindings,
     the free variable (if any) bound in the @(tsee car) of the list.
     For the body of a @('let') expression,
     we just remove all the variables bound in the bindings."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds
          string-type-map)
  :result type-var-setp
  :default nil
  :combine set::union
  :override
  ((type :var (set::insert type.var nil))
   (type :forall (set::delete type.param (type-free-type-vars type.body)))
   (type :foralln (set::difference (type-free-type-vars type.body)
                                   (set::mergesort type.params)))
   (expr :let
         (set::union (bind-list-free-type-vars expr.binds)
                     (set::difference (expr-free-type-vars expr.body)
                                      (bind-list-bound-type-vars expr.binds))))
   (atom :tlambda (set::delete atom.param (expr-free-type-vars atom.body)))
   (atom :tlambdan
         (set::difference (expr-free-type-vars atom.body)
                          (set::mergesort atom.params)))
   (bind :tfun
         (set::difference (set::union (type-option-free-type-vars bind.type?)
                                      (expr-free-type-vars bind.expr))
                          (set::mergesort bind.params)))
   (bind :cfun
         (set::difference (set::union
                           (var+type?-list-free-type-vars bind.params)
                           (set::union (type-free-type-vars bind.type)
                                       (expr-free-type-vars bind.expr)))
                          (type-var-list-option-case
                           bind.tparams?
                           :some (set::mergesort bind.tparams?.val)
                           :none nil)))
   (bind-list (b* (((when (endp bind-list)) nil)
                   (bind (car bind-list)))
                (set::union (bind-free-type-vars bind)
                            (set::difference
                             (bind-list-free-type-vars (cdr bind-list))
                             (bind-bound-type-vars bind))))))
  :name ast-free-type-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-expr-vars
  :short "Set of free expression variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The free variables of a binder are the ones
     in the thing that the variable is bound to.
     Thus, for the expression and combined function binders,
     we remove the parameters,
     because the thing that the variable is bound to
     is like a lambda abstraction.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we need to override the function for @(tsee bind-list)
     to remove, from the free variables of
     the @(tsee cdr) of a non-empty list of bindings,
     the free variable (if any) bound in the @(tsee car) of the list.
     For the body of a @('let') expression,
     we just remove all the variables bound in the bindings."))
  :types (exprs/atoms/binds
          string-expr-map)
  :result string-setp
  :default nil
  :combine set::union
  :override
  ((expr :var (set::insert expr.name nil))
   (expr :unbox
         (set::union (expr-free-expr-vars expr.target)
                     (set::delete expr.var
                                  (expr-free-expr-vars expr.body))))
   (expr :let
         (set::union
          (bind-list-free-expr-vars expr.binds)
          (set::difference (expr-free-expr-vars expr.body)
                           (bind-list-bound-expr-vars expr.binds))))
   (atom :lambdan
         (set::difference (expr-free-expr-vars atom.body)
                          (set::mergesort (var+type?-list->var atom.params))))
   (bind :fun
         (set::difference (expr-free-expr-vars bind.expr)
                          (set::mergesort (var+type?-list->var bind.params))))
   (bind :cfun
         (set::difference (expr-free-expr-vars bind.expr)
                          (set::mergesort (var+type?-list->var bind.params))))
   (bind-list (b* (((when (endp bind-list)) nil)
                   (bind (car bind-list)))
                (set::union (bind-free-expr-vars bind)
                            (set::difference
                             (bind-list-free-expr-vars (cdr bind-list))
                             (bind-bound-expr-vars bind))))))
  :name ast-free-expr-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce all-ispace-vars
  :short "Set of all (i.e. free and bound) ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the variables that occur anywhere,
     including the parameters of product and sum types
     and the ispace variables introduced by ispace binders."))
  :types (dims
          shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :result ispace-var-setp
  :default nil
  :combine set::union
  :override
  ((dim :var (set::insert (ispace-var-dim dim.name) nil))
   (shape :var (set::insert (ispace-var-shape shape.name) nil))
   (type :pi (set::insert type.param (type-all-ispace-vars type.body)))
   (type :pin
         (set::union (set::mergesort type.params)
                     (type-all-ispace-vars type.body)))
   (type :sigma
         (set::union (set::mergesort type.params)
                     (type-all-ispace-vars type.body)))
   (bind :ifun
         (set::union (set::mergesort bind.params)
                     (set::union (type-option-all-ispace-vars bind.type?)
                                 (expr-all-ispace-vars bind.expr))))
   (bind :cfun
         (set::union
          (ispace-var-list-option-case
           bind.iparams?
           :some (set::mergesort bind.iparams?.val)
           :none nil)
          (set::union (var+type?-list-all-ispace-vars bind.params)
                      (set::union (type-all-ispace-vars bind.type)
                                  (expr-all-ispace-vars bind.expr))))))
  :name ast-all-ispace-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce all-type-vars
  :short "Set of all (i.e. free and bound) type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the variables that occur anywhere,
     including the parameters of universal types
     and the type variables introduced by type binders."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :result type-var-setp
  :default nil
  :combine set::union
  :override
  ((type :var (set::insert type.var nil))
   (type :forall (set::insert type.param (type-all-type-vars type.body)))
   (type :foralln (set::union (set::mergesort type.params)
                              (type-all-type-vars type.body)))
   (atom :tlambda (set::insert atom.param (expr-all-type-vars atom.body)))
   (atom :tlambdan (set::union (set::mergesort atom.params)
                               (expr-all-type-vars atom.body)))
   (bind :type (set::insert bind.var
                            (type-all-type-vars bind.type)))
   (bind :tfun (set::union (set::mergesort bind.params)
                           (set::union (type-option-all-type-vars bind.type?)
                                       (expr-all-type-vars bind.expr))))
   (bind :cfun (set::union
                (type-var-list-option-case
                 bind.tparams?
                 :some (set::mergesort bind.tparams?.val)
                 :none nil)
                (set::union (var+type?-list-all-type-vars bind.params)
                            (set::union (type-all-type-vars bind.type)
                                        (expr-all-type-vars bind.expr))))))
  :name ast-all-type-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce all-expr-vars
  :short "Set of all (i.e. free and bound) expression variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the variables that occur anywhere,
     including the parameters of lambda abstractions,
     the parameters of function bindings,
     and the expression variables introduced by
     @('let') bindings and unboxing expressions."))
  :types (exprs/atoms/binds)
  :result string-setp
  :default nil
  :combine set::union
  :override
  ((expr :var (set::insert expr.name nil))
   (expr :unbox
         (set::insert expr.var
                      (set::union (expr-all-expr-vars expr.target)
                                  (expr-all-expr-vars expr.body))))
   (atom :lambdan
         (set::union (set::mergesort (var+type?-list->var atom.params))
                     (expr-all-expr-vars atom.body)))
   (bind :val
         (set::insert bind.var
                      (expr-all-expr-vars bind.expr)))
   (bind :fun
         (set::insert bind.var
                      (set::union
                       (set::mergesort (var+type?-list->var bind.params))
                       (expr-all-expr-vars bind.expr))))
   (bind :tfun
         (set::insert bind.var
                      (expr-all-expr-vars bind.expr)))
   (bind :ifun
         (set::insert bind.var
                      (expr-all-expr-vars bind.expr)))
   (bind :cfun
         (set::insert bind.var
                      (set::union
                       (set::mergesort (var+type?-list->var bind.params))
                       (expr-all-expr-vars bind.expr)))))
  :name ast-all-expr-vars)
