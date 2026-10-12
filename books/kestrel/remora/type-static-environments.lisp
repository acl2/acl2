; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-static-environments")
(include-book "variable-substitution-alpha-operations")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable typep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-static-environments
  :parents (static-environments)
  :short "Type static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see static-environments) first."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-senv
  :short "Fixtype of type static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type static environment is
     a map from the type variables in scope to optional types.
     This corresponds to @($\\Delta$);
     since our type variables include their own kind,
     the keys suffice to capture the kinds,
     as opposed to a map from variables to kinds.
     The optional type associated to a variable:
     is absent when the variable is bound by an abstraction,
     i.e. it does not stand for any specific type;
     it is present when the variable is bound by a @('let')
     to a specific type, which is then its definition."))
  ((types type-var-type-option-map))
  :pred type-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-type-senv ()
  :returns (tenv type-senvp)
  :short "Initial type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, type static environment.
     It is empty."))
  (type-senv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-var ((var type-varp) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add a type variable to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated type,
     because it does not stand for any specific type;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-type-senv tenv
                    :types (omap::update (type-var-fix var)
                                         nil
                                         (type-senv->types tenv))))

;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-vars ((vars type-var-listp) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add zero or more type variables to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee type-senv-add-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (type-senv-fix tenv))
       (tenv (type-senv-add-var (car vars) tenv)))
    (type-senv-add-vars (cdr vars) tenv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-def ((var type-varp) (type typep) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add a type variable with its type definition
          to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated type,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-type-senv tenv
                    :types (omap::update (type-var-fix var)
                                         (type-fix type)
                                         (type-senv->types tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-type-subst ((map type-var-type-option-mapp))
  :returns (subst string-type-map-pairp)
  :short "Turn a map from type variables to optional types
          into the type variable substitution
          determined by the definitions in the map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn
     the map in a type static environment
     into an atom-kind type substitution and an array-kind type substitution,
     consisting of the variables that have a definition
     (i.e. a present optional type);
     variables without a type do not contribute.
     An atom type variable maps to its (atom-kind) type,
     and an array type variable maps to its (array-kind) type.")
   (xdoc::p
    "It should never be the case that the map violates kinds,
     i.e. associates an atom type variable to an array-kind type
     or an array type variable to an atom-kind type.
     But we do not have that static invariant yet,
     so we defensively throw an error if that happens."))
  (b* (((when (omap::emptyp (type-var-type-option-map-fix map)))
        (make-string-type-map-pair :1st nil :2nd nil))
       ((mv var type?) (omap::head map))
       ((string-type-map-pair subst-rest)
        (type-senv-type-subst (omap::tail map))))
    (type-option-case
     type?
     :none subst-rest
     :some
     (type-var-case
      var
      :atom (if (type-atom-kindp type?.val)
                (change-string-type-map-pair
                 subst-rest
                 :1st (omap::update var.name type?.val subst-rest.1st))
              (prog2$ (raise "Internal error: ~
                              atom type variable ~x0 ~
                              is associated with ~
                              array-kind type ~x1."
                             var type?.val)
                      subst-rest))
      :array (if (type-atom-kindp type?.val)
                 (prog2$ (raise "Internal error: ~
                                 array type variable ~x0 ~
                                 is associated with ~
                                 atom-kind type ~x1."
                                var type?.val)
                         subst-rest)
               (change-string-type-map-pair
                subst-rest
                :2nd (omap::update var.name type?.val subst-rest.2nd))))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-expand-type ((type typep)
                               (ienv ispace-senvp)
                               (tenv type-senvp))
  :returns (new-type type-resultp)
  :short "Expand a type using the definitions in the static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined type variable and ispace variable in the type
     with its definition
     (see @(tsee type-senv-type-subst) and @(tsee ispace-senv-ispace-subst)).
     We substitute the type variables first, and the ispace variables second.
     Since types may contain ispaces but not vice versa,
     substituting the type definitions first may expose
     additional ispace variables, occurring in those definitions,
     which the subsequent ispace substitution then replaces.
     Since the definitions in the static environments are fully expanded
     (i.e. they contain no defined variables),
     the result would be the same with the opposite order;
     but this order does not rely on
     the definitions in the static environments being fully expanded.")
   (xdoc::p
    "Because types contain binders (universal, product, and sum types),
     the substitution could result in variable capture;
     the capture-avoiding substitutions
     @(tsee type-subst-type-vars-alpha) and @(tsee type-subst-ispace-vars-alpha)
     automatically alpha-rename the bound variables as needed to avoid it."))
  (b* (((string-type-map-pair tsubst)
        (type-senv-type-subst (type-senv->types tenv)))
       (type (type-subst-type-vars-alpha type tsubst.1st tsubst.2nd))
       ((stringdimmap+stringshapemap isubst)
        (ispace-senv-ispace-subst (ispace-senv->ispaces ienv))))
    (type-subst-ispace-vars-alpha type isubst.dim-map isubst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(define type-senv-expand-type-list ((types type-listp)
                                    (ienv ispace-senvp)
                                    (tenv type-senvp))
  :returns (new-types type-list-resultp
                      :hints
                      (("Goal"
                        :induct t
                        :in-theory (enable type-listp-when-result-not-error))))
  :short "Lift @(tsee type-senv-expand-type) to lists."
  (b* (((when (endp types)) nil)
       ((ok type) (type-senv-expand-type (car types) ienv tenv))
       ((ok types) (type-senv-expand-type-list (cdr types) ienv tenv)))
    (cons type types))
  :verify-guards :after-returns)
