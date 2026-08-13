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

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

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
   (type :sigma (set::insert type.param (type-all-ispace-vars type.body)))
   (type :sigman
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
   (expr :unboxn
         (set::insert expr.var
                      (set::union (expr-all-expr-vars expr.target)
                                  (expr-all-expr-vars expr.body))))
   (atom :lambda
         (set::insert (var+type?->var atom.param)
                      (expr-all-expr-vars atom.body)))
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
