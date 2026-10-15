; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "free-variable-operations")
(include-book "all-variable-operations")
(include-book "variable-name-sets")

(local (include-book "osets"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ free-variables-in-all-variables
  :parents (abstract-syntax-variable-operations)
  :short "The free variables of an AST are among all its variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two families of operations are defined by separate folds
     (see @(see free-variable-operations) and
     @(see all-variable-operations)):
     at each binder the free-variable fold removes the bound variables,
     which the all-variable fold instead adds.
     So the former yields a subset of the latter,
     in each of the three namespaces.")
   (xdoc::p
    "The inductions all have the same shape:
     a containment is carried through the set operations
     that the fold applies to its recursive results,
     by the @('subset-lifting-rules') of the @(see osets) extension."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-dims-free-ispace-vars-flag
  (defthm dim-free-ispace-vars-subset-all
    (set::subset (dim-free-ispace-vars dim) (dim-all-ispace-vars dim))
    :flag dim-free-ispace-vars)
  (defthm dim-list-free-ispace-vars-subset-all
    (set::subset (dim-list-free-ispace-vars dim-list)
                 (dim-list-all-ispace-vars dim-list))
    :flag dim-list-free-ispace-vars)
  :hints (("Goal"
           :expand ((dim-free-ispace-vars dim)
                    (dim-list-free-ispace-vars dim-list)
                    (dim-all-ispace-vars dim)
                    (dim-list-all-ispace-vars dim-list))
           :in-theory (enable subset-lifting-rules))))

(defthm-shapes/ispaces-free-ispace-vars-flag
  (defthm shape-free-ispace-vars-subset-all
    (set::subset (shape-free-ispace-vars shape) (shape-all-ispace-vars shape))
    :flag shape-free-ispace-vars)
  (defthm shape-list-free-ispace-vars-subset-all
    (set::subset (shape-list-free-ispace-vars shape-list)
                 (shape-list-all-ispace-vars shape-list))
    :flag shape-list-free-ispace-vars)
  (defthm ispace-free-ispace-vars-subset-all
    (set::subset (ispace-free-ispace-vars ispace)
                 (ispace-all-ispace-vars ispace))
    :flag ispace-free-ispace-vars)
  (defthm ispace-list-free-ispace-vars-subset-all
    (set::subset (ispace-list-free-ispace-vars ispace-list)
                 (ispace-list-all-ispace-vars ispace-list))
    :flag ispace-list-free-ispace-vars)
  :hints (("Goal"
           :expand ((shape-free-ispace-vars shape)
                    (shape-list-free-ispace-vars shape-list)
                    (ispace-free-ispace-vars ispace)
                    (ispace-list-free-ispace-vars ispace-list)
                    (shape-all-ispace-vars shape)
                    (shape-list-all-ispace-vars shape-list)
                    (ispace-all-ispace-vars ispace)
                    (ispace-list-all-ispace-vars ispace-list))
           :in-theory (enable subset-lifting-rules))))

(defrule ispace-list-option-free-ispace-vars-subset-all
  (set::subset (ispace-list-option-free-ispace-vars ispaces?)
               (ispace-list-option-all-ispace-vars ispaces?))
  :enable (ispace-list-option-free-ispace-vars
           ispace-list-option-all-ispace-vars))

(defthm-types-free-ispace-vars-flag
  (defthm type-free-ispace-vars-subset-all
    (set::subset (type-free-ispace-vars type) (type-all-ispace-vars type))
    :flag type-free-ispace-vars)
  (defthm type-list-free-ispace-vars-subset-all
    (set::subset (type-list-free-ispace-vars type-list)
                 (type-list-all-ispace-vars type-list))
    :flag type-list-free-ispace-vars)
  :hints (("Goal"
           :expand ((type-free-ispace-vars type)
                    (type-list-free-ispace-vars type-list)
                    (type-all-ispace-vars type)
                    (type-list-all-ispace-vars type-list))
           :in-theory (enable subset-lifting-rules))))

(defrule type-option-free-ispace-vars-subset-all
  (set::subset (type-option-free-ispace-vars type?)
               (type-option-all-ispace-vars type?))
  :enable (type-option-free-ispace-vars type-option-all-ispace-vars))

(defrule type-list-option-free-ispace-vars-subset-all
  (set::subset (type-list-option-free-ispace-vars types?)
               (type-list-option-all-ispace-vars types?))
  :enable (type-list-option-free-ispace-vars
           type-list-option-all-ispace-vars))

(defrule var+type?-free-ispace-vars-subset-all
  (set::subset (var+type?-free-ispace-vars param)
               (var+type?-all-ispace-vars param))
  :enable (var+type?-free-ispace-vars var+type?-all-ispace-vars))

(defrule var+type?-list-free-ispace-vars-subset-all
  (set::subset (var+type?-list-free-ispace-vars params)
               (var+type?-list-all-ispace-vars params))
  :induct t
  :enable (var+type?-list-free-ispace-vars
           var+type?-list-all-ispace-vars
           subset-lifting-rules))

(defthm-exprs/atoms/binds-free-ispace-vars-flag
  (defthm expr-free-ispace-vars-subset-all
    (set::subset (expr-free-ispace-vars expr) (expr-all-ispace-vars expr))
    :flag expr-free-ispace-vars)
  (defthm expr-list-free-ispace-vars-subset-all
    (set::subset (expr-list-free-ispace-vars expr-list)
                 (expr-list-all-ispace-vars expr-list))
    :flag expr-list-free-ispace-vars)
  (defthm atom-free-ispace-vars-subset-all
    (set::subset (atom-free-ispace-vars atom) (atom-all-ispace-vars atom))
    :flag atom-free-ispace-vars)
  (defthm atom-list-free-ispace-vars-subset-all
    (set::subset (atom-list-free-ispace-vars atom-list)
                 (atom-list-all-ispace-vars atom-list))
    :flag atom-list-free-ispace-vars)
  (defthm bind-free-ispace-vars-subset-all
    (set::subset (bind-free-ispace-vars bind) (bind-all-ispace-vars bind))
    :flag bind-free-ispace-vars)
  (defthm bind-list-free-ispace-vars-subset-all
    (set::subset (bind-list-free-ispace-vars bind-list)
                 (bind-list-all-ispace-vars bind-list))
    :flag bind-list-free-ispace-vars)
  :hints (("Goal"
           :expand ((expr-free-ispace-vars expr)
                    (expr-list-free-ispace-vars expr-list)
                    (atom-free-ispace-vars atom)
                    (atom-list-free-ispace-vars atom-list)
                    (bind-free-ispace-vars bind)
                    (bind-list-free-ispace-vars bind-list)
                    (expr-all-ispace-vars expr)
                    (expr-list-all-ispace-vars expr-list)
                    (atom-all-ispace-vars atom)
                    (atom-list-all-ispace-vars atom-list)
                    (bind-all-ispace-vars bind)
                    (bind-list-all-ispace-vars bind-list))
           :in-theory (enable subset-lifting-rules))))

(defthm-types-free-type-vars-flag
  (defthm type-free-type-vars-subset-all
    (set::subset (type-free-type-vars type) (type-all-type-vars type))
    :flag type-free-type-vars)
  (defthm type-list-free-type-vars-subset-all
    (set::subset (type-list-free-type-vars type-list)
                 (type-list-all-type-vars type-list))
    :flag type-list-free-type-vars)
  :hints (("Goal"
           :expand ((type-free-type-vars type)
                    (type-list-free-type-vars type-list)
                    (type-all-type-vars type)
                    (type-list-all-type-vars type-list))
           :in-theory (enable subset-lifting-rules))))

(defrule type-option-free-type-vars-subset-all
  (set::subset (type-option-free-type-vars type?)
               (type-option-all-type-vars type?))
  :enable (type-option-free-type-vars type-option-all-type-vars))

(defrule type-list-option-free-type-vars-subset-all
  (set::subset (type-list-option-free-type-vars types?)
               (type-list-option-all-type-vars types?))
  :enable (type-list-option-free-type-vars
           type-list-option-all-type-vars))

(defrule var+type?-free-type-vars-subset-all
  (set::subset (var+type?-free-type-vars param)
               (var+type?-all-type-vars param))
  :enable (var+type?-free-type-vars var+type?-all-type-vars))

(defrule var+type?-list-free-type-vars-subset-all
  (set::subset (var+type?-list-free-type-vars params)
               (var+type?-list-all-type-vars params))
  :induct t
  :enable (var+type?-list-free-type-vars
           var+type?-list-all-type-vars
           subset-lifting-rules))

(defthm-exprs/atoms/binds-free-type-vars-flag
  (defthm expr-free-type-vars-subset-all
    (set::subset (expr-free-type-vars expr) (expr-all-type-vars expr))
    :flag expr-free-type-vars)
  (defthm expr-list-free-type-vars-subset-all
    (set::subset (expr-list-free-type-vars expr-list)
                 (expr-list-all-type-vars expr-list))
    :flag expr-list-free-type-vars)
  (defthm atom-free-type-vars-subset-all
    (set::subset (atom-free-type-vars atom) (atom-all-type-vars atom))
    :flag atom-free-type-vars)
  (defthm atom-list-free-type-vars-subset-all
    (set::subset (atom-list-free-type-vars atom-list)
                 (atom-list-all-type-vars atom-list))
    :flag atom-list-free-type-vars)
  (defthm bind-free-type-vars-subset-all
    (set::subset (bind-free-type-vars bind) (bind-all-type-vars bind))
    :flag bind-free-type-vars)
  (defthm bind-list-free-type-vars-subset-all
    (set::subset (bind-list-free-type-vars bind-list)
                 (bind-list-all-type-vars bind-list))
    :flag bind-list-free-type-vars)
  :hints (("Goal"
           :expand ((expr-free-type-vars expr)
                    (expr-list-free-type-vars expr-list)
                    (atom-free-type-vars atom)
                    (atom-list-free-type-vars atom-list)
                    (bind-free-type-vars bind)
                    (bind-list-free-type-vars bind-list)
                    (expr-all-type-vars expr)
                    (expr-list-all-type-vars expr-list)
                    (atom-all-type-vars atom)
                    (atom-list-all-type-vars atom-list)
                    (bind-all-type-vars bind)
                    (bind-list-all-type-vars bind-list))
           :in-theory (enable subset-lifting-rules))))

(defthm-exprs/atoms/binds-free-expr-vars-flag
  (defthm expr-free-expr-vars-subset-all
    (set::subset (expr-free-expr-vars expr) (expr-all-expr-vars expr))
    :flag expr-free-expr-vars)
  (defthm expr-list-free-expr-vars-subset-all
    (set::subset (expr-list-free-expr-vars expr-list)
                 (expr-list-all-expr-vars expr-list))
    :flag expr-list-free-expr-vars)
  (defthm atom-free-expr-vars-subset-all
    (set::subset (atom-free-expr-vars atom) (atom-all-expr-vars atom))
    :flag atom-free-expr-vars)
  (defthm atom-list-free-expr-vars-subset-all
    (set::subset (atom-list-free-expr-vars atom-list)
                 (atom-list-all-expr-vars atom-list))
    :flag atom-list-free-expr-vars)
  (defthm bind-free-expr-vars-subset-all
    (set::subset (bind-free-expr-vars bind) (bind-all-expr-vars bind))
    :flag bind-free-expr-vars)
  (defthm bind-list-free-expr-vars-subset-all
    (set::subset (bind-list-free-expr-vars bind-list)
                 (bind-list-all-expr-vars bind-list))
    :flag bind-list-free-expr-vars)
  :hints (("Goal"
           :expand ((expr-free-expr-vars expr)
                    (expr-list-free-expr-vars expr-list)
                    (atom-free-expr-vars atom)
                    (atom-list-free-expr-vars atom-list)
                    (bind-free-expr-vars bind)
                    (bind-list-free-expr-vars bind-list)
                    (expr-all-expr-vars expr)
                    (expr-list-all-expr-vars expr-list)
                    (atom-all-expr-vars atom)
                    (atom-list-all-expr-vars atom-list)
                    (bind-all-expr-vars bind)
                    (bind-list-all-expr-vars bind-list))
           :in-theory (enable subset-lifting-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consequences for the name strings of the variable sets: a containment of
; the names of all the variables carries to the names of the free ones.

(defrule subset-names-of-expr-free-ispace-vars-when-all
  (implies (set::subset (ispace-var-set-names (expr-all-ispace-vars e)) a)
           (set::subset (ispace-var-set-names (expr-free-ispace-vars e)) a))
  :use ((:instance subset-ispace-var-set-names-when-subset
                   (vars (expr-free-ispace-vars e))
                   (vars2 (expr-all-ispace-vars e)))))

(defrule subset-names-of-expr-free-type-vars-when-all
  (implies (set::subset (type-var-set-names (expr-all-type-vars e)) a)
           (set::subset (type-var-set-names (expr-free-type-vars e)) a))
  :use ((:instance subset-type-var-set-names-when-subset
                   (vars (expr-free-type-vars e))
                   (vars2 (expr-all-type-vars e)))))

(defrule subset-expr-free-expr-vars-when-all
  (implies (set::subset (expr-all-expr-vars e) a)
           (set::subset (expr-free-expr-vars e) a))
  :use ((:instance set::subset-transitive
                   (x (expr-free-expr-vars e))
                   (y (expr-all-expr-vars e))
                   (z a))))

(defrule subset-names-of-type-option-free-ispace-vars-when-all
  (implies (set::subset (ispace-var-set-names
                         (type-option-all-ispace-vars ty?)) a)
           (set::subset (ispace-var-set-names
                         (type-option-free-ispace-vars ty?)) a))
  :use ((:instance subset-ispace-var-set-names-when-subset
                   (vars (type-option-free-ispace-vars ty?))
                   (vars2 (type-option-all-ispace-vars ty?)))))

(defrule subset-names-of-type-option-free-type-vars-when-all
  (implies (set::subset (type-var-set-names
                         (type-option-all-type-vars ty?)) a)
           (set::subset (type-var-set-names
                         (type-option-free-type-vars ty?)) a))
  :use ((:instance subset-type-var-set-names-when-subset
                   (vars (type-option-free-type-vars ty?))
                   (vars2 (type-option-all-type-vars ty?)))))

(defrule subset-names-of-type-free-ispace-vars-when-all
  (implies (set::subset (ispace-var-set-names (type-all-ispace-vars ty)) a)
           (set::subset (ispace-var-set-names (type-free-ispace-vars ty)) a))
  :use ((:instance subset-ispace-var-set-names-when-subset
                   (vars (type-free-ispace-vars ty))
                   (vars2 (type-all-ispace-vars ty)))))

(defrule subset-names-of-type-free-type-vars-when-all
  (implies (set::subset (type-var-set-names (type-all-type-vars ty)) a)
           (set::subset (type-var-set-names (type-free-type-vars ty)) a))
  :use ((:instance subset-type-var-set-names-when-subset
                   (vars (type-free-type-vars ty))
                   (vars2 (type-all-type-vars ty)))))

(defrule subset-names-of-var+type?-list-free-ispace-vars-when-all
  (implies (set::subset (ispace-var-set-names
                         (var+type?-list-all-ispace-vars params)) a)
           (set::subset (ispace-var-set-names
                         (var+type?-list-free-ispace-vars params)) a))
  :use ((:instance subset-ispace-var-set-names-when-subset
                   (vars (var+type?-list-free-ispace-vars params))
                   (vars2 (var+type?-list-all-ispace-vars params)))))

(defrule subset-names-of-var+type?-list-free-type-vars-when-all
  (implies (set::subset (type-var-set-names
                         (var+type?-list-all-type-vars params)) a)
           (set::subset (type-var-set-names
                         (var+type?-list-free-type-vars params)) a))
  :use ((:instance subset-type-var-set-names-when-subset
                   (vars (var+type?-list-free-type-vars params))
                   (vars2 (var+type?-list-all-type-vars params)))))

(defrule subset-names-of-bind-list-free-ispace-vars-when-all
  (implies (set::subset (ispace-var-set-names
                         (bind-list-all-ispace-vars binds)) a)
           (set::subset (ispace-var-set-names
                         (bind-list-free-ispace-vars binds)) a))
  :use ((:instance subset-ispace-var-set-names-when-subset
                   (vars (bind-list-free-ispace-vars binds))
                   (vars2 (bind-list-all-ispace-vars binds)))))

(defrule subset-names-of-bind-list-free-type-vars-when-all
  (implies (set::subset (type-var-set-names
                         (bind-list-all-type-vars binds)) a)
           (set::subset (type-var-set-names
                         (bind-list-free-type-vars binds)) a))
  :use ((:instance subset-type-var-set-names-when-subset
                   (vars (bind-list-free-type-vars binds))
                   (vars2 (bind-list-all-type-vars binds)))))

(defrule subset-bind-list-free-expr-vars-when-all
  (implies (set::subset (bind-list-all-expr-vars binds) a)
           (set::subset (bind-list-free-expr-vars binds) a))
  :use ((:instance set::subset-transitive
                   (x (bind-list-free-expr-vars binds))
                   (y (bind-list-all-expr-vars binds))
                   (z a))))
