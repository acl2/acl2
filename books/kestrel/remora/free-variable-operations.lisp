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
(include-book "bound-variable-operations")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "osets"))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ free-variable-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for retrieving free variables from ASTs."
  :order-subtopics t
  :default-parent t)

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
          dim-list-list
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
   (type :sigma (set::delete type.param (type-free-ispace-vars type.body)))
   (type :sigman
         (set::difference (type-free-ispace-vars type.body)
                          (set::mergesort type.params)))
   (expr :unbox
         (set::union (expr-free-ispace-vars expr.target)
                     (set::delete expr.ispace
                                  (expr-free-ispace-vars expr.body))))
   (expr :unboxn
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
   (expr :unboxn
         (set::union (expr-free-expr-vars expr.target)
                     (set::delete expr.var
                                  (expr-free-expr-vars expr.body))))
   (expr :let
         (set::union
          (bind-list-free-expr-vars expr.binds)
          (set::difference (expr-free-expr-vars expr.body)
                           (bind-list-bound-expr-vars expr.binds))))
   (atom :lambda
         (set::delete (var+type?->var atom.param)
                      (expr-free-expr-vars atom.body)))
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

(defsection ast-free-ispace-vars-additional-theorems
  :short "Additional theorems about free ispace variables."

  (defruled dim-list-list-free-ispace-vars-of-list-to-singletons
    (equal (dim-list-list-free-ispace-vars (list-to-singletons dims))
           (dim-list-free-ispace-vars dims))
    :induct t
    :enable (list-to-singletons
             ast-free-ispace-vars-rules))

  (add-to-ruleset ast-free-ispace-vars-rules
                  '(dim-list-list-free-ispace-vars-of-list-to-singletons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-ispace-vars-theorems-about-structurals
  :short "Some theorems about
          the free ispace variables over some structural operations."

  (local (in-theory (enable* ast-free-ispace-vars-rules)))

  (defruled shape-list-free-ispace-vars-of-shape-dims-list
    (equal (shape-list-free-ispace-vars (shape-dims-list dimss))
           (dim-list-list-free-ispace-vars dimss))
    :induct t
    :enable shape-dims-list)

  (defrule atom-list-free-ispace-vars-of-atom-base-list
    (equal (atom-list-free-ispace-vars (atom-base-list lits))
           nil)
    :induct t
    :enable atom-base-list)

  (defrule shape-list-free-ispace-vars-of-ispace-shape-list->shape
    (implies (ispace-list-case-shape ispaces)
             (equal (shape-list-free-ispace-vars
                     (ispace-shape-list->shape ispaces))
                    (ispace-list-free-ispace-vars ispaces)))
    :induct t
    :enable (ispace-shape-list->shape
             ispace-free-ispace-vars))

  (defrule type-list-free-ispace-vars-of-var+type?-list->type-list-or-err
    (implies (not (reserrp (var+type?-list->type-list-or-err var+type?s)))
             (equal (type-list-free-ispace-vars
                     (var+type?-list->type-list-or-err var+type?s))
                    (var+type?-list-free-ispace-vars var+type?s)))
    :induct t
    :enable (var+type?-list->type-list-or-err
             var+type?->type-or-err
             type-list-free-ispace-vars
             var+type?-list-free-ispace-vars
             var+type?-free-ispace-vars
             type-option-free-ispace-vars
             type-option-some->val))

  (defrule type-free-ispace-vars-of-nest-fun-types
    (equal (type-free-ispace-vars (nest-fun-types in out))
           (set::union (type-list-free-ispace-vars in)
                       (type-free-ispace-vars out)))
    :induct t
    :enable (nest-fun-types
             type-free-ispace-vars
             type-list-free-ispace-vars))

  (defrule type-free-ispace-vars-of-nest-forall-types
    (equal (type-free-ispace-vars (nest-forall-types params body))
           (type-free-ispace-vars body))
    :induct t
    :enable (nest-forall-types
             type-free-ispace-vars))

  (defrule type-free-ispace-vars-of-nest-pi-types
    (equal (type-free-ispace-vars (nest-pi-types params body))
           (set::difference (type-free-ispace-vars body)
                            (set::mergesort (ispace-var-list-fix params))))
    :induct t
    :enable (nest-pi-types
             type-free-ispace-vars
             ispace-var-list-fix
             mergesort-of-cons))

  (defrule type-free-ispace-vars-of-nest-sigma-types
    (equal (type-free-ispace-vars (nest-sigma-types params body))
           (set::difference (type-free-ispace-vars body)
                            (set::mergesort (ispace-var-list-fix params))))
    :induct t
    :enable (nest-sigma-types
             type-free-ispace-vars
             ispace-var-list-fix
             mergesort-of-cons))

  (defrule expr-free-ispace-vars-of-nest-app-exprs
    (equal (expr-free-ispace-vars (nest-app-exprs fun args))
           (set::union (expr-free-ispace-vars fun)
                       (expr-list-free-ispace-vars args)))
    :induct t
    :enable (nest-app-exprs
             expr-list-free-ispace-vars))

  (defrule expr-free-ispace-vars-of-nest-tapp-exprs
    (equal (expr-free-ispace-vars (nest-tapp-exprs fun args))
           (set::union (expr-free-ispace-vars fun)
                       (type-list-free-ispace-vars args)))
    :induct t
    :enable (nest-tapp-exprs
             type-list-free-ispace-vars))

  (defrule expr-free-ispace-vars-of-nest-iapp-exprs
    (equal (expr-free-ispace-vars (nest-iapp-exprs fun args))
           (set::union (expr-free-ispace-vars fun)
                       (ispace-list-free-ispace-vars args)))
    :induct t
    :enable (nest-iapp-exprs
             ispace-list-free-ispace-vars))

  (defrule expr-free-ispace-vars-of-nest-lambda-exprs
    (equal (expr-free-ispace-vars (nest-lambda-exprs params body type?))
           (if (consp params)
               (set::union (var+type?-list-free-ispace-vars params)
                           (set::union (expr-free-ispace-vars body)
                                       (type-option-free-ispace-vars type?)))
             (expr-free-ispace-vars body)))
    :induct t
    :enable (nest-lambda-exprs
             var+type?-list-free-ispace-vars))

  (defrule expr-free-ispace-vars-of-nest-tlambda-exprs
    (equal (expr-free-ispace-vars (nest-tlambda-exprs params body))
           (expr-free-ispace-vars body))
    :induct t
    :enable nest-tlambda-exprs)

  (defrule expr-free-ispace-vars-of-nest-ilambda-exprs
    (equal (expr-free-ispace-vars (nest-ilambda-exprs params body))
           (set::difference (expr-free-ispace-vars body)
                            (set::mergesort (ispace-var-list-fix params))))
    :induct t
    :enable (nest-ilambda-exprs
             atom-free-ispace-vars
             ispace-var-list-fix
             mergesort-of-cons))

  (defrule expr-free-ispace-vars-of-nest-unbox-exprs
    (equal (expr-free-ispace-vars
            (nest-unbox-exprs ispaces var target body type?))
           (if (consp ispaces)
               (set::union (expr-free-ispace-vars target)
                           (set::difference
                            (expr-free-ispace-vars body)
                            (set::mergesort (ispace-var-list-fix ispaces))))
             (expr-free-ispace-vars body)))
    :enable (nest-unbox-exprs
             expr-free-ispace-vars
             mergesort-of-cons)
    :prep-lemmas
    ((defrule expr-free-ispace-vars-of-nest-unbox-exprs-loop
       (equal (expr-free-ispace-vars
               (nest-unbox-exprs-loop ispaces var body))
              (set::difference (expr-free-ispace-vars body)
                               (set::mergesort (ispace-var-list-fix ispaces))))
       :induct t
       :enable (nest-unbox-exprs-loop
                expr-free-ispace-vars
                ispace-var-list-fix
                mergesort-of-cons))))

  (defrule expr-free-ispace-vars-of-nest-box-exprs
    (equal (expr-free-ispace-vars (nest-box-exprs ispaces body))
           (set::union (ispace-list-free-ispace-vars ispaces)
                       (expr-free-ispace-vars body)))
    :induct t
    :enable (nest-box-exprs
             ispace-list-free-ispace-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-type-vars-theorems-about-structurals
  :short "Some theorems about
          the free type variables over some structural operations."

  (local (in-theory (enable* ast-free-type-vars-rules)))

  (defrule atom-list-free-type-vars-of-atom-base-list
    (equal (atom-list-free-type-vars (atom-base-list lits))
           nil)
    :induct t
    :enable atom-base-list)

  (defrule type-list-free-type-vars-of-var+type?-list->type-list-or-err
    (implies (not (reserrp (var+type?-list->type-list-or-err var+type?s)))
             (equal (type-list-free-type-vars
                     (var+type?-list->type-list-or-err var+type?s))
                    (var+type?-list-free-type-vars var+type?s)))
    :induct t
    :enable (var+type?-list->type-list-or-err
             var+type?->type-or-err
             type-list-free-type-vars
             var+type?-list-free-type-vars
             var+type?-free-type-vars
             type-option-free-type-vars
             type-option-some->val))

  (defrule type-free-type-vars-of-nest-fun-types
    (equal (type-free-type-vars (nest-fun-types in out))
           (set::union (type-list-free-type-vars in)
                       (type-free-type-vars out)))
    :induct t
    :enable (nest-fun-types
             type-free-type-vars
             type-list-free-type-vars))

  (defrule type-free-type-vars-of-nest-forall-types
    (equal (type-free-type-vars (nest-forall-types params body))
           (set::difference (type-free-type-vars body)
                            (set::mergesort (type-var-list-fix params))))
    :induct t
    :enable (nest-forall-types
             type-free-type-vars
             type-var-list-fix
             mergesort-of-cons))

  (defrule type-free-type-vars-of-nest-pi-types
    (equal (type-free-type-vars (nest-pi-types params body))
           (type-free-type-vars body))
    :induct t
    :enable (nest-pi-types
             type-free-type-vars))

  (defrule type-free-type-vars-of-nest-sigma-types
    (equal (type-free-type-vars (nest-sigma-types params body))
           (type-free-type-vars body))
    :induct t
    :enable (nest-sigma-types
             type-free-type-vars))

  (defrule expr-free-type-vars-of-nest-app-exprs
    (equal (expr-free-type-vars (nest-app-exprs fun args))
           (set::union (expr-free-type-vars fun)
                       (expr-list-free-type-vars args)))
    :induct t
    :enable (nest-app-exprs
             expr-list-free-type-vars))

  (defrule expr-free-type-vars-of-nest-tapp-exprs
    (equal (expr-free-type-vars (nest-tapp-exprs fun args))
           (set::union (expr-free-type-vars fun)
                       (type-list-free-type-vars args)))
    :induct t
    :enable (nest-tapp-exprs
             type-list-free-type-vars))

  (defrule expr-free-type-vars-of-nest-iapp-exprs
    (equal (expr-free-type-vars (nest-iapp-exprs fun args))
           (expr-free-type-vars fun))
    :induct t
    :enable nest-iapp-exprs)

  (defrule expr-free-type-vars-of-nest-lambda-exprs
    (equal (expr-free-type-vars (nest-lambda-exprs params body type?))
           (if (consp params)
               (set::union (var+type?-list-free-type-vars params)
                           (set::union (expr-free-type-vars body)
                                       (type-option-free-type-vars type?)))
             (expr-free-type-vars body)))
    :induct t
    :enable (nest-lambda-exprs
             var+type?-list-free-type-vars))

  (defrule expr-free-type-vars-of-nest-tlambda-exprs
    (equal (expr-free-type-vars (nest-tlambda-exprs params body))
           (set::difference (expr-free-type-vars body)
                            (set::mergesort (type-var-list-fix params))))
    :induct t
    :enable (nest-tlambda-exprs
             atom-free-type-vars
             type-var-list-fix
             mergesort-of-cons))

  (defrule expr-free-type-vars-of-nest-ilambda-exprs
    (equal (expr-free-type-vars (nest-ilambda-exprs params body))
           (expr-free-type-vars body))
    :induct t
    :enable nest-ilambda-exprs)

  (defrule expr-free-type-vars-of-nest-unbox-exprs
    (equal (expr-free-type-vars
            (nest-unbox-exprs ispaces var target body type?))
           (if (consp ispaces)
               (set::union (expr-free-type-vars target)
                           (set::union (expr-free-type-vars body)
                                       (type-option-free-type-vars type?)))
             (expr-free-type-vars body)))
    :enable nest-unbox-exprs
    :prep-lemmas
    ((defrule expr-free-type-vars-of-nest-unbox-exprs-loop
       (equal (expr-free-type-vars (nest-unbox-exprs-loop ispaces var body))
              (expr-free-type-vars body))
       :induct t
       :enable nest-unbox-exprs-loop)))

  (defrule expr-free-type-vars-of-nest-box-exprs
    (equal (expr-free-type-vars (nest-box-exprs ispaces body))
           (expr-free-type-vars body))
    :induct t
    :enable nest-box-exprs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-expr-vars-theorems-about-structurals
  :short "Some theorems about
          the free expression variables over some structural operations."

  (local (in-theory (enable* ast-free-expr-vars-rules)))

  (defrule atom-list-free-expr-vars-of-atom-base-list
    (equal (atom-list-free-expr-vars (atom-base-list lits))
           nil)
    :induct t
    :enable atom-base-list)

  (defrule expr-free-expr-vars-of-nest-app-exprs
    (equal (expr-free-expr-vars (nest-app-exprs fun args))
           (set::union (expr-free-expr-vars fun)
                       (expr-list-free-expr-vars args)))
    :induct t
    :enable (nest-app-exprs
             expr-list-free-expr-vars))

  (defrule expr-free-expr-vars-of-nest-tapp-exprs
    (equal (expr-free-expr-vars (nest-tapp-exprs fun args))
           (expr-free-expr-vars fun))
    :induct t
    :enable nest-tapp-exprs)

  (defrule expr-free-expr-vars-of-nest-iapp-exprs
    (equal (expr-free-expr-vars (nest-iapp-exprs fun args))
           (expr-free-expr-vars fun))
    :induct t
    :enable nest-iapp-exprs)

  (defrule expr-free-expr-vars-of-nest-lambda-exprs
    (equal (expr-free-expr-vars (nest-lambda-exprs params body type?))
           (set::difference (expr-free-expr-vars body)
                            (set::mergesort (var+type?-list->var params))))
    :induct t
    :enable (nest-lambda-exprs
             atom-free-expr-vars
             var+type?-list->var
             mergesort-of-cons))

  (defrule expr-free-expr-vars-of-nest-tlambda-exprs
    (equal (expr-free-expr-vars (nest-tlambda-exprs params body))
           (expr-free-expr-vars body))
    :induct t
    :enable nest-tlambda-exprs)

  (defrule expr-free-expr-vars-of-nest-ilambda-exprs
    (equal (expr-free-expr-vars (nest-ilambda-exprs params body))
           (expr-free-expr-vars body))
    :induct t
    :enable nest-ilambda-exprs)

  (defrule expr-free-expr-vars-of-nest-unbox-exprs
    (equal (expr-free-expr-vars
            (nest-unbox-exprs ispaces var target body type?))
           (if (consp ispaces)
               (set::union (expr-free-expr-vars target)
                           (set::delete (str-fix var)
                                        (expr-free-expr-vars body)))
             (expr-free-expr-vars body)))
    :enable (nest-unbox-exprs
             expr-free-expr-vars)
    :prep-lemmas
    ((defrule expr-free-expr-vars-of-nest-unbox-exprs-loop
       (equal (expr-free-expr-vars (nest-unbox-exprs-loop ispaces var body))
              (if (consp ispaces)
                  (set::insert (str-fix var) (expr-free-expr-vars body))
                (expr-free-expr-vars body)))
       :induct t
       :enable (nest-unbox-exprs-loop
                expr-free-expr-vars))))

  (defrule expr-free-expr-vars-of-nest-box-exprs
    (equal (expr-free-expr-vars (nest-box-exprs ispaces body))
           (expr-free-expr-vars body))
    :induct t
    :enable nest-box-exprs))
