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

(local (include-book "osets"))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ all-variable-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for retrieving all (bound and free) variables from ASTs."
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
          dim-list-list
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-all-ispace-vars-additional-theorems
  :short "Additional theorems about all ispace variables."

  (defruled dim-list-list-all-ispace-vars-of-list-to-singletons
    (equal (dim-list-list-all-ispace-vars (list-to-singletons dims))
           (dim-list-all-ispace-vars dims))
    :induct t
    :enable (list-to-singletons
             ast-all-ispace-vars-rules))

  (add-to-ruleset ast-all-ispace-vars-rules
                  '(dim-list-list-all-ispace-vars-of-list-to-singletons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection all-type-vars-theorems-about-structurals
  :short "Some theorems about
          all the type variables over some structural operations."

  (local (in-theory (enable* ast-all-type-vars-rules)))

  (defrule atom-list-all-type-vars-of-atom-base-list
    (equal (atom-list-all-type-vars (atom-base-list lits))
           nil)
    :induct t
    :enable atom-base-list)

  (defrule type-list-all-type-vars-of-var+type?-list->type-list-or-err
    (implies (not (reserrp (var+type?-list->type-list-or-err var+type?s)))
             (equal (type-list-all-type-vars
                     (var+type?-list->type-list-or-err var+type?s))
                    (var+type?-list-all-type-vars var+type?s)))
    :induct t
    :enable (var+type?-list->type-list-or-err
             var+type?->type-or-err
             type-list-all-type-vars
             var+type?-list-all-type-vars
             var+type?-all-type-vars
             type-option-all-type-vars
             type-option-some->val))

  (defrule type-all-type-vars-of-nest-fun-types
    (equal (type-all-type-vars (nest-fun-types in out))
           (set::union (type-list-all-type-vars in)
                       (type-all-type-vars out)))
    :induct t
    :enable (nest-fun-types
             type-all-type-vars
             type-list-all-type-vars))

  (defrule type-all-type-vars-of-nest-forall-types
    (equal (type-all-type-vars (nest-forall-types params body))
           (set::union (set::mergesort (type-var-list-fix params))
                       (type-all-type-vars body)))
    :induct t
    :enable (nest-forall-types
             type-all-type-vars
             type-var-list-fix
             mergesort-of-cons))

  (defrule type-all-type-vars-of-nest-pi-types
    (equal (type-all-type-vars (nest-pi-types params body))
           (type-all-type-vars body))
    :induct t
    :enable (nest-pi-types
             type-all-type-vars))

  (defrule type-all-type-vars-of-nest-sigma-types
    (equal (type-all-type-vars (nest-sigma-types params body))
           (type-all-type-vars body))
    :induct t
    :enable (nest-sigma-types
             type-all-type-vars))

  (defrule expr-all-type-vars-of-nest-app-exprs
    (equal (expr-all-type-vars (nest-app-exprs fun args))
           (set::union (expr-all-type-vars fun)
                       (expr-list-all-type-vars args)))
    :induct t
    :enable (nest-app-exprs
             expr-list-all-type-vars))

  (defrule expr-all-type-vars-of-nest-tapp-exprs
    (equal (expr-all-type-vars (nest-tapp-exprs fun args))
           (set::union (expr-all-type-vars fun)
                       (type-list-all-type-vars args)))
    :induct t
    :enable (nest-tapp-exprs
             type-list-all-type-vars))

  (defrule expr-all-type-vars-of-nest-iapp-exprs
    (equal (expr-all-type-vars (nest-iapp-exprs fun args))
           (expr-all-type-vars fun))
    :induct t
    :enable nest-iapp-exprs)

  (defrule expr-all-type-vars-of-nest-lambda-exprs
    (equal (expr-all-type-vars (nest-lambda-exprs params body type?))
           (if (consp params)
               (set::union (var+type?-list-all-type-vars params)
                           (set::union (expr-all-type-vars body)
                                       (type-option-all-type-vars type?)))
             (expr-all-type-vars body)))
    :induct t
    :enable (nest-lambda-exprs
             var+type?-list-all-type-vars))

  (defrule expr-all-type-vars-of-nest-tlambda-exprs
    (equal (expr-all-type-vars (nest-tlambda-exprs params body))
           (set::union (set::mergesort (type-var-list-fix params))
                       (expr-all-type-vars body)))
    :induct t
    :enable (nest-tlambda-exprs
             atom-all-type-vars
             type-var-list-fix
             mergesort-of-cons))

  (defrule expr-all-type-vars-of-nest-ilambda-exprs
    (equal (expr-all-type-vars (nest-ilambda-exprs params body))
           (expr-all-type-vars body))
    :induct t
    :enable nest-ilambda-exprs)

  (defrule expr-all-type-vars-of-nest-unbox-exprs
    (equal (expr-all-type-vars
            (nest-unbox-exprs ispaces var target body type?))
           (if (consp ispaces)
               (set::union (expr-all-type-vars target)
                           (set::union (expr-all-type-vars body)
                                       (type-option-all-type-vars type?)))
             (expr-all-type-vars body)))
    :enable nest-unbox-exprs
    :prep-lemmas
    ((defrule expr-all-type-vars-of-nest-unbox-exprs-loop
       (equal (expr-all-type-vars (nest-unbox-exprs-loop ispaces var body))
              (expr-all-type-vars body))
       :induct t
       :enable nest-unbox-exprs-loop)))

  (defrule expr-all-type-vars-of-nest-box-exprs
    (equal (expr-all-type-vars (nest-box-exprs ispaces body))
           (expr-all-type-vars body))
    :induct t
    :enable nest-box-exprs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection all-expr-vars-theorems-about-structurals
  :short "Some theorems about
          all the expression variables over some structural operations."

  (local (in-theory (enable* ast-all-expr-vars-rules)))

  (defrule atom-list-all-expr-vars-of-atom-base-list
    (equal (atom-list-all-expr-vars (atom-base-list lits))
           nil)
    :induct t
    :enable atom-base-list)

  (defrule expr-all-expr-vars-of-nest-app-exprs
    (equal (expr-all-expr-vars (nest-app-exprs fun args))
           (set::union (expr-all-expr-vars fun)
                       (expr-list-all-expr-vars args)))
    :induct t
    :enable (nest-app-exprs
             expr-list-all-expr-vars))

  (defrule expr-all-expr-vars-of-nest-tapp-exprs
    (equal (expr-all-expr-vars (nest-tapp-exprs fun args))
           (expr-all-expr-vars fun))
    :induct t
    :enable nest-tapp-exprs)

  (defrule expr-all-expr-vars-of-nest-iapp-exprs
    (equal (expr-all-expr-vars (nest-iapp-exprs fun args))
           (expr-all-expr-vars fun))
    :induct t
    :enable nest-iapp-exprs)

  (defrule expr-all-expr-vars-of-nest-lambda-exprs
    (equal (expr-all-expr-vars (nest-lambda-exprs params body type?))
           (set::union (set::mergesort (var+type?-list->var params))
                       (expr-all-expr-vars body)))
    :induct t
    :enable (nest-lambda-exprs
             atom-all-expr-vars
             var+type?-list->var
             mergesort-of-cons))

  (defrule expr-all-expr-vars-of-nest-tlambda-exprs
    (equal (expr-all-expr-vars (nest-tlambda-exprs params body))
           (expr-all-expr-vars body))
    :induct t
    :enable nest-tlambda-exprs)

  (defrule expr-all-expr-vars-of-nest-ilambda-exprs
    (equal (expr-all-expr-vars (nest-ilambda-exprs params body))
           (expr-all-expr-vars body))
    :induct t
    :enable nest-ilambda-exprs)

  (defrule expr-all-expr-vars-of-nest-unbox-exprs
    (equal (expr-all-expr-vars
            (nest-unbox-exprs ispaces var target body type?))
           (if (consp ispaces)
               (set::insert (str-fix var)
                            (set::union (expr-all-expr-vars target)
                                        (expr-all-expr-vars body)))
             (expr-all-expr-vars body)))
    :enable (nest-unbox-exprs
             expr-all-expr-vars)
    :prep-lemmas
    ((defrule expr-all-expr-vars-of-nest-unbox-exprs-loop
       (equal (expr-all-expr-vars (nest-unbox-exprs-loop ispaces var body))
              (if (consp ispaces)
                  (set::insert (str-fix var) (expr-all-expr-vars body))
                (expr-all-expr-vars body)))
       :induct t
       :enable (nest-unbox-exprs-loop
                expr-all-expr-vars))))

  (defrule expr-all-expr-vars-of-nest-box-exprs
    (equal (expr-all-expr-vars (nest-box-exprs ispaces body))
           (expr-all-expr-vars body))
    :induct t
    :enable nest-box-exprs))
