; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-validator")
(include-book "abstract-syntax-constructors")
(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-matching-operations")
(include-book "abstract-syntax-variable-operations")
(include-book "type-equivalence-checker")
(include-book "type-matcher")
(include-book "nat-lists")

(include-book "kestrel/fty/string-string-map-pair-result" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/fix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory
  (enable shapep-when-result-not-error
          shape-listp-when-result-not-error
          typep-when-result-not-error
          type-listp-when-result-not-error
          acl2::string-string-map-pairp-when-result-not-error
          type+ispace-p-when-result-not-error
          type+ispace-listp-when-result-not-error
          type+type-p-when-result-not-error
          typelist+type-p-when-result-not-error
          ispacevar+type-p-when-result-not-error
          ispacevarlist+type-p-when-result-not-error
          ispace+expr-p-when-result-not-error
          typevar+type-p-when-result-not-error
          typevarlist+type-p-when-result-not-error
          stringdimmap+stringshapemap-p-when-result-not-error
          string-type-mapp-when-result-not-error
          string-type-map-pairp-when-result-not-error
          expr-senvp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-checker
  :parents (static-semantics)
  :short "A type checker for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a high-level executable type checker
     that is meant to enforce exactly the inference rules
     that define the static semantics of Remora
     in [thesis] and [arxiv].")
   (xdoc::p
    "This type checker is not designed for efficiency
     or to provide informative error messages.
     It is designed for simplicity.")
   (xdoc::p
    "Besides checking, this type checker performs
     a limited form of type inference:
     when a function with a universal or product type
     is applied to an argument
     without explicit type and ispace applications,
     the type and ispace arguments are inferred from the argument type,
     and the corresponding applications are added to the expression
     (see @(tsee check/infer-app)).
     We plan to extend this inference."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type ((type typep) (ienv ispace-senvp) (tenv type-senvp))
    :returns (yes/no booleanp)
    :parents (type-checker check-types)
    :short "Check a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "A base type is always valid.")
     (xdoc::p
      "An array type is valid iff
       its element type is valid and atom-kinded (i.e. not an array type),
       and its ispace is valid.")
     (xdoc::p
      "A bracket type is valid iff
       its element type is valid and atom-kinded (i.e. not an array type),
       and its ispaces are valid.")
     (xdoc::p
      "The atom-kind requirement on the element type of
       an array or bracket type is the only kind constraint:
       as explained in @(tsee type),
       an atom-kinded type may otherwise be used
       wherever an array-kinded type is expected,
       being auto-lifted to a zero-rank array type.")
     (xdoc::p
      "A function type is valid iff
       its input types and its output type are all valid.")
     (xdoc::p
      "A universal type is valid iff its body is valid
       in the environment extended with the bound type variables.")
     (xdoc::p
      "A product type is valid iff its body is valid
       in the environment extended with the bound ispace variables.")
     (xdoc::p
      "A sum type is valid iff its body is valid
       in the environment extended with the bound ispace variables."))
    (type-case
     type
     :var (consp (omap::assoc type.var (type-senv->types tenv)))
     :base t
     :array (and (check-type type.elem ienv tenv)
                 (type-atom-kindp type.elem)
                 (check-ispace type.ispace ienv))
     :bracket (and (check-type type.elem ienv tenv)
                   (type-atom-kindp type.elem)
                   (check-ispace-list type.ispaces ienv))
     :fun (and (check-type type.in ienv tenv)
               (check-type type.out ienv tenv))
     :funn (and (check-type-list type.in ienv tenv)
                (check-type type.out ienv tenv))
     :forall (check-type type.body ienv (type-senv-add-var type.param tenv))
     :foralln (check-type type.body ienv (type-senv-add-vars type.params tenv))
     :pi (check-type type.body (ispace-senv-add-var type.param ienv) tenv)
     :pin (check-type type.body (ispace-senv-add-vars type.params ienv) tenv)
     :sigma (check-type type.body (ispace-senv-add-var type.param ienv) tenv)
     :sigman (check-type type.body
                         (ispace-senv-add-vars type.params ienv)
                         tenv))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type-list ((types type-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp))
    :returns (yes/no booleanp)
    :parents (type-checker check-types)
    :short "Check a list of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each type in turn,
       returning @('t') iff they are all valid."))
    (or (endp types)
        (and (check-type (car types) ienv tenv)
             (check-type-list (cdr types) ienv tenv)))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-type-of-base-lit ((lit base-litp))
  :returns (btype base-typep)
  :short "Base type of a base value."
  (base-lit-case
   lit
   :bool (base-type-bool)
   :int (base-type-int)
   :float (base-type-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-shape-suffix ((shape shapep) (suffix shapep))
  :returns (prefix shape-resultp
                   :hints
                   (("Goal" :in-theory (enable check-list-suffix-alt-def))))
  :short "Check if a shape has another shape as suffix,
          returning the prefix shape if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for a term application: see @(tsee check-expr).
     Each of the shapes of the input types of the function expression
     must be a suffix of the shape of the type of
     the argument expression corresponding to the function input.
     In [arxiv] and [thesis],
     the shape of the argument is denoted
     @($(\\mathtt{++}\\ \\iota_a\\ \\iota)\\ldots$),
     and the shape of the input is denoted @($\\iota$);
     they use ispaces in general,
     but the ispaces are shapes,
     and our formalization directly uses shapes.
     This function takes the argument shape as the formal @('shape'),
     and the input type shape as the formal @('suffix'),
     and returns @($\\iota_a$) if successful,
     which is the prefix.")
   (xdoc::p
    "To perform this check, we need to normalize both shapes,
     which results into two concatenations of
     lists of variables and single-dimension shapes.
     We use @(tsee check-list-suffix) to check whether
     the second list is a suffix of the first list,
     obtaining the prefix if so,
     which we return as a concatenation."))
  (b* ((shape-elements (shape-append->shapes (normalize-shape shape)))
       (suffix-elements (shape-append->shapes (normalize-shape suffix)))
       ((mv suffixp prefix-elements)
        (check-list-suffix shape-elements suffix-elements))
       ((unless suffixp) (reserr nil)))
    (shape-append prefix-elements))
  :guard-hints (("Goal" :in-theory (enable check-list-suffix-alt-def nfix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-shape-suffixes ((shapes shape-listp) (suffixes shape-listp))
  :guard (equal (len suffixes) (len shapes))
  :returns (prefixes shape-list-resultp)
  :short "Check if each shape in a list has
          the corresponding shape in another list as suffix,
          returning each prefix if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee check-shape-suffix) to lists,
     which all have the same lengths (if successful)."))
  (b* (((when (endp shapes)) nil)
       ((unless (mbt (consp suffixes))) (reserr nil))
       ((ok prefix) (check-shape-suffix (car shapes) (car suffixes)))
       ((ok prefixes) (check-shape-suffixes (cdr shapes) (cdr suffixes))))
    (cons prefix prefixes))

  ///

  (defret len-of-check-shape-suffixes
    (implies (not (reserrp prefixes))
             (equal (len prefixes)
                    (len shapes)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-shapes ((shapes shape-listp))
  :returns (shape shape-resultp)
  :short "Calculate the least upper bound of a list of shapes,
          with respect to prefix as partial order."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for a term application; see @(tsee check-expr).
     After having calculated all the prefixes @($\\iota_a\\ldots$),
     we need to calculate the join (i.e. least upper bound)
     of those shapes and of the shape @($\\iota_f$) of the function expression.
     The partial order in question is the prefix relation:
     @($\\iota\\sqsubseteq\\iota'$) iff @($\\iota$) is a prefix of @($\\iota'$)
     (including the case @($\\iota=\\iota'$)).")
   (xdoc::p
    "The order of the list is irrelevant to the result.
     If the list is empty, the result is the empty concatenation,
     which is the bottom of the partial order.
     If the list is a singleton, the result is its only element.
     Otherwise, we normalize every shape (see @(tsee normalize-shape-list)),
     we extract the elements of the resulting concatenations
     (see @(tsee shape-append-list->shapes)),
     and we use @(tsee list-prefix-join)
     to join those lists of variables and single-dimension shapes:
     if they do not form a chain under the prefix order, there is no join;
     otherwise the result is the longest of them,
     turned back into a concatenation."))
  (b* (((when (endp shapes)) (shape-append nil))
       ((when (endp (cdr shapes))) (shape-fix (car shapes)))
       (element-lists
        (shape-append-list->shapes (normalize-shape-list shapes)))
       ((mv joinp join) (list-prefix-join element-lists)))
    (if joinp
        (shape-append join)
      (reserr nil)))
  :verify-guards :after-returns
  :guard-hints
  (("Goal" :in-theory (enable true-list-listp-when-shape-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ispace-params-and-args ((params ispace-var-listp)
                                      (args ispace-listp))
  :returns (maps stringdimmap+stringshapemap-resultp)
  :short "Check whether a list of ispace parameters
          and a list of ispace arguments match."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same number of elements,
     and each parameter must have the same sort as the corresponding argument.
     If the check succeeds, we return two maps,
     one from the names of the dimension parameters
     to the corresponding dimension arguments,
     and one from the names of the shape parameters
     to the corresponding shape arguments."))
  (b* (((when (endp params))
        (if (endp args)
            (make-stringdimmap+stringshapemap
             :dim-map nil
             :shape-map nil)
          (reserr nil)))
       ((when (endp args)) (reserr nil))
       ((ok (stringdimmap+stringshapemap maps))
        (check-ispace-params-and-args (cdr params) (cdr args)))
       (param (car params))
       (arg (car args)))
    (ispace-var-case
     param
     :dim (ispace-case
           arg
           :dim (make-stringdimmap+stringshapemap
                 :dim-map (omap::update param.name
                                        arg.dim
                                        maps.dim-map)
                 :shape-map maps.shape-map)
           :shape (reserr nil))
     :shape (ispace-case
             arg
             :dim (reserr nil)
             :shape (make-stringdimmap+stringshapemap
                     :dim-map maps.dim-map
                     :shape-map (omap::update param.name
                                              arg.shape
                                              maps.shape-map)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-params-and-args ((params type-var-listp)
                                    (args type-listp))
  :returns (maps string-type-map-pair-resultp)
  :short "Check whether a list of type parameters
          and a list of type arguments match."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same number of elements,
     and each parameter must have the same kind as the corresponding argument.
     If the check succeeds, we return two maps,
     one from the names of the atom type parameters
     to the corresponding atom-kinded type arguments,
     and one from the names of the array type parameters
     to the corresponding array-kinded type arguments."))
  (b* (((when (endp params))
        (if (endp args)
            (make-string-type-map-pair
             :1st nil
             :2nd nil)
          (reserr nil)))
       ((when (endp args)) (reserr nil))
       ((ok (string-type-map-pair maps))
        (check-type-params-and-args (cdr params) (cdr args)))
       (param (car params))
       (arg (type-fix (car args))))
    (type-var-case
     param
     :atom (if (type-atom-kindp arg)
               (make-string-type-map-pair
                :1st (omap::update param.name arg maps.1st)
                :2nd maps.2nd)
             (reserr nil))
     :array (if (type-atom-kindp arg)
                (reserr nil)
              (make-string-type-map-pair
               :1st maps.1st
               :2nd (omap::update param.name arg maps.2nd)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ispace-var-renaming ((vars1 ispace-var-listp)
                                   (vars2 ispace-var-listp))
  :returns (dim-and-shape-maps string-string-map-pair-resultp)
  :short "Check if two lists of ispace variables match in number and sorts,
          and if so return maps between the dimension and shape variables."
  (b* (((when (endp vars1))
        (if (endp vars2)
            (make-string-string-map-pair :1st nil :2nd nil)
          (reserr nil)))
       ((when (endp vars2)) (reserr nil))
       ((ok (string-string-map-pair maps))
        (check-ispace-var-renaming (cdr vars1) (cdr vars2)))
       (var1 (car vars1))
       (var2 (car vars2)))
    (ispace-var-case
     var1
     :dim (ispace-var-case
           var2
           :dim (make-string-string-map-pair
                 :1st (omap::update var1.name var2.name maps.1st)
                 :2nd maps.2nd)
           :shape (reserr nil))
     :shape (ispace-var-case
             var2
             :dim (reserr nil)
             :shape (make-string-string-map-pair
                     :1st maps.1st
                     :2nd (omap::update var1.name var2.name maps.2nd)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-ispace-subst ((map ispace-var-ispace-option-mapp))
  :returns (subst stringdimmap+stringshapemap-p)
  :short "Turn a map from ispace variables to optional ispaces
          into the ispace variable substitution
          determined by the definitions in the map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn
     the map in an ispace static environment
     into a dimension substitution and a shape substitution,
     consisting of the variables that have a definition
     (i.e. a present optional ispace);
     variables without an ispace do not contribute.
     A dimension variable maps to the dimension of its (dimension) ispace,
     and a shape variable maps to the shape of its (shape) ispace.")
   (xdoc::p
    "It should never be the case that the map violates sorts,
     i.e. associates a dimension variable to a shape ispace
     or a shape variable to a dimension ispace.
     But we do not have that static invariant yet,
     so we defensively throw an error if that happens."))
  (b* (((when (omap::emptyp (ispace-var-ispace-option-map-fix map)))
        (make-stringdimmap+stringshapemap :dim-map nil :shape-map nil))
       ((mv var ispace?) (omap::head map))
       ((stringdimmap+stringshapemap subst-rest)
        (senv-ispace-subst (omap::tail map))))
    (ispace-option-case
     ispace?
     :none subst-rest
     :some
     (ispace-var-case
      var
      :dim (ispace-case
            ispace?.val
            :dim (change-stringdimmap+stringshapemap
                  subst-rest
                  :dim-map (omap::update var.name
                                         ispace?.val.dim
                                         subst-rest.dim-map))
            :shape (prog2$ (raise "Internal error: ~
                                   dimension variable ~x0 ~
                                   is associated with ~
                                   shape ispace ~x1."
                                  var ispace?.val)
                           subst-rest))
      :shape (ispace-case
              ispace?.val
              :dim (prog2$ (raise "Internal error: ~
                                   shape variable ~x0 ~
                                   is associated with ~
                                   dimension ispace ~x1."
                                  var ispace?.val)
                           subst-rest)
              :shape (change-stringdimmap+stringshapemap
                      subst-rest
                      :shape-map (omap::update var.name
                                               ispace?.val.shape
                                               subst-rest.shape-map))))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-type-subst ((map type-var-type-option-mapp))
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
        (senv-type-subst (omap::tail map))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-shape ((shape shapep) (ienv ispace-senvp))
  :returns (new-shape shapep)
  :short "Expand a shape using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the shape
     with its definition (see @(tsee senv-ispace-subst)).
     Since shapes contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (shape-subst-ispace-vars shape subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-ispace ((ispace ispacep) (ienv ispace-senvp))
  :returns (new-ispace ispacep)
  :short "Expand an ispace using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the ispace
     with its definition (see @(tsee senv-ispace-subst)).
     Since ispaces contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (ispace-subst-ispace-vars ispace subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection senv-expand-ispace-list ((x ispace-listp)
                                             (ienv ispace-senvp))
  :returns (new-ispaces ispace-listp)
  :short "Lift @(tsee senv-expand-ispace) to lists of ispaces."
  (senv-expand-ispace x ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type ((type typep) (ienv ispace-senvp) (tenv type-senvp))
  :returns (new-type type-resultp)
  :short "Expand a type using the definitions in the static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined type variable and ispace variable in the type
     with its definition
     (see @(tsee senv-type-subst) and @(tsee senv-ispace-subst)).
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
        (senv-type-subst (type-senv->types tenv)))
       (type (type-subst-type-vars-alpha type tsubst.1st tsubst.2nd))
       ((stringdimmap+stringshapemap isubst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (type-subst-ispace-vars-alpha type isubst.dim-map isubst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type-list ((types type-listp)
                               (ienv ispace-senvp)
                               (tenv type-senvp))
  :returns (new-types type-list-resultp)
  :short "Lift @(tsee senv-expand-type) to lists."
  (b* (((when (endp types)) nil)
       ((ok type) (senv-expand-type (car types) ienv tenv))
       ((ok types) (senv-expand-type-list (cdr types) ienv tenv)))
    (cons type types))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-app ((fun-type typep) (arg-type typep))
  :returns (type type-resultp)
  :short "Check a unary term application,
          given the type of the function and the type of the argument."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the function must be
     an array type of a function type,
     with at least one input.
     We use @(tsee type-match-fun) to peel off
     the first input type of the function type,
     obtaining that input type and the rest of the function type:
     the function type over the remaining inputs,
     or the output type if there are no other inputs.")
   (xdoc::p
    "In [thesis], term application is n-ary,
     applying the function to all its arguments at once;
     our core form of term application is unary (see @(tsee expr)),
     so our code implements the rule specialized to one argument.")
   (xdoc::p
    "The input type and the argument type must be array types,
     with equivalent atom types.
     Following the rank-polymorphic application semantics,
     the input shape must be a suffix of the argument shape
     (see @(tsee check-shape-suffix)),
     and the remaining prefix is the frame of the argument.
     The principal shape (ispace) is the join
     of the function shape and this frame
     (see @(tsee join-shapes)),
     denoted @($\\iota_p$) in [arxiv] and [thesis].")
   (xdoc::p
    "The result is the rest of the function type,
     lifted over the principal shape.
     The rest must be an array type,
     possibly via the automatic lifting of atom types
     performed by @(tsee type-match-array),
     which lifts the residual function type, if any,
     to a zero-rank array:
     we return the array type
     whose atom type is the one of the rest,
     and whose shape is the principal shape
     followed by the shape of the rest.")
   (xdoc::p
    "In [arxiv] and [thesis],
     @($\\tau$) and @($\\iota$) correspond to
     the element type and shape of the input type @('in-type'),
     @($\\iota_a$) corresponds to @('prefix-shape'),
     @($\\iota_f$) corresponds to @('fun-shape'),
     and @($\\tau'$) and @($\\iota'$) correspond to
     the element type and shape of @('rest-type')."))
  (b* (((ok fun-type+ispace) (type-match-array fun-type))
       (fun-type (type+ispace->type fun-type+ispace))
       (fun-ispace (type+ispace->ispace fun-type+ispace))
       (fun-shape (shape-from-ispace fun-ispace))
       ((ok in+rest) (type-match-fun fun-type))
       (in-type (type+type->type1 in+rest))
       (rest-type (type+type->type2 in+rest))
       ((ok in-type+ispace) (type-match-array in-type))
       (in-atom-type (type+ispace->type in-type+ispace))
       (in-ispace (type+ispace->ispace in-type+ispace))
       (in-shape (shape-from-ispace in-ispace))
       ((ok arg-type+ispace) (type-match-array arg-type))
       (arg-atom-type (type+ispace->type arg-type+ispace))
       (arg-ispace (type+ispace->ispace arg-type+ispace))
       (arg-shape (shape-from-ispace arg-ispace))
       ((unless (type-equivp arg-atom-type in-atom-type)) (reserr nil))
       ((ok prefix-shape) (check-shape-suffix arg-shape in-shape))
       ((ok principal-shape) (join-shapes (list fun-shape prefix-shape)))
       ((ok rest-type+ispace) (type-match-array rest-type))
       (rest-atom-type (type+ispace->type rest-type+ispace))
       (rest-ispace (type+ispace->ispace rest-type+ispace))
       (rest-shape (shape-from-ispace rest-ispace)))
    (make-type-array
     :elem rest-atom-type
     :ispace (ispace-shape (shape-append (list principal-shape rest-shape))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-appn ((fun-type typep) (arg-types type-listp))
  :returns (type type-resultp)
  :short "Check an n-ary term application,
          given the type of the function and the types of the arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An n-ary term application is sugar for
     a left-nested chain of unary term applications (see @(tsee expr)).
     Accordingly, we check it by folding @(tsee check-app)
     over the argument types, from left to right.
     If there are no arguments, we return the type of the function;
     but note that well-formed n-ary term applications
     have two or more arguments (see @(tsee expr))."))
  (b* (((when (endp arg-types)) (type-fix fun-type))
       ((ok type) (check-app fun-type (car arg-types))))
    (check-appn type (cdr arg-types)))
  :measure (len arg-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tapp ((fun-type typep)
                    (arg typep)
                    (ienv ispace-senvp)
                    (tenv type-senvp))
  :returns (type type-resultp)
  :short "Check a unary type application,
          given the type of the function and the type argument."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the function must be
     an array type of a universal type,
     with at least one bound type variable.
     We use @(tsee type-match-forall) to peel off
     the first bound variable of the universal type,
     obtaining that variable and the rest of the universal type.
     We check that the type argument is valid and
     that its kind matches the one of the variable,
     using @(tsee check-type-params-and-args) on singleton lists,
     which yields two type maps (for atom and array kinds),
     one of which is empty,
     whose only entry associates the argument to the variable.")
   (xdoc::p
    "In [thesis], type application is n-ary,
     instantiating all the bound variables
     @($(x\\ k)\\ldots$) of the universal type at once;
     our core form of type application is unary (see @(tsee expr)),
     so our code implements the rule specialized to one bound variable.")
   (xdoc::p
    "We apply the substitution to the whole rest of the universal type;
     the substitution avoids variable capture
     by automatically alpha-renaming bound variables as needed
     (see @(tsee type-subst-type-vars-alpha)).
     Besides the type binders,
     this also alpha-renames the ispace binders in the rest,
     which could otherwise capture free ispace variables of the type argument.
     The substituted rest must be an array type,
     possibly via the automatic lifting of atom types
     performed by @(tsee type-match-array):
     we return the array type
     whose atom type is the one of the substituted rest,
     and whose shape is the function shape
     followed by the shape of the substituted rest.")
   (xdoc::p
    "In the rule and [thesis],
     @($(x\\ k)\\ldots$) corresponds to @('var') in our code,
     @($\\tau_u$) corresponds to the element type of @('rest-type'),
     @($\\iota_u$) corresponds to the ispace of @('rest-type'),
     and @($\\iota_f$) corresponds to @('fun-ispace')."))
  (b* (((ok fun-type+ispace) (type-match-array fun-type))
       (fun-type (type+ispace->type fun-type+ispace))
       (fun-ispace (type+ispace->ispace fun-type+ispace))
       (fun-shape (shape-from-ispace fun-ispace))
       ((ok fun-var+type) (type-match-forall fun-type))
       (var (typevar+type->var fun-var+type))
       (rest-type (typevar+type->type fun-var+type))
       ((unless (check-type arg ienv tenv)) (reserr nil))
       ((ok arg) (senv-expand-type arg ienv tenv))
       ((ok (string-type-map-pair type-maps))
        (check-type-params-and-args (list var) (list arg)))
       (rest-type-subst
        (type-subst-type-vars-alpha rest-type
                                    type-maps.1st
                                    type-maps.2nd))
       ((ok rest-type+ispace) (type-match-array rest-type-subst))
       (rest-atom-type (type+ispace->type rest-type+ispace))
       (rest-ispace (type+ispace->ispace rest-type+ispace))
       (rest-shape (shape-from-ispace rest-ispace)))
    (make-type-array
     :elem rest-atom-type
     :ispace (ispace-shape (shape-append (list fun-shape rest-shape))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tappn ((fun-type typep)
                     (args type-listp)
                     (ienv ispace-senvp)
                     (tenv type-senvp))
  :returns (type type-resultp)
  :short "Check an n-ary type application,
          given the type of the function and the type arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An n-ary type application is sugar for
     a left-nested chain of unary type applications (see @(tsee expr)).
     Accordingly, we check it by folding @(tsee check-tapp)
     over the type arguments, from left to right.
     If there are no arguments, we return the type of the function;
     but note that well-formed n-ary type applications
     have two or more arguments (see @(tsee expr))."))
  (b* (((when (endp args)) (type-fix fun-type))
       ((ok type) (check-tapp fun-type (car args) ienv tenv)))
    (check-tappn type (cdr args) ienv tenv))
  :measure (len args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-iapp ((fun-type typep) (arg ispacep) (ienv ispace-senvp))
  :returns (type type-resultp)
  :short "Check a unary ispace application,
          given the type of the function and the ispace argument."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the function must be
     an array type of a product type,
     with at least one bound ispace variable.
     We use @(tsee type-match-product) to peel off
     the first bound variable of the product type,
     obtaining that variable and the rest of the product type.
     We check that the ispace argument is valid and
     that its sort matches the one of the variable,
     using @(tsee check-ispace-params-and-args) on singleton lists,
     which yields two ispace maps (for dimensions and shapes),
     one of which is empty,
     whose only entry associates the argument to the variable.")
   (xdoc::p
    "In [thesis], ispace application is n-ary,
     instantiating all the bound variables
     @($(x\\ \\gamma)\\ldots$) of the product type at once;
     our core form of ispace application is unary (see @(tsee expr)),
     so our code implements the rule specialized to one bound variable.")
   (xdoc::p
    "We apply the substitution to the whole rest of the product type;
     the substitution avoids variable capture
     by automatically alpha-renaming bound variables as needed
     (see @(tsee type-subst-ispace-vars-alpha)).
     The substituted rest must be an array type,
     possibly via the automatic lifting of atom types
     performed by @(tsee type-match-array):
     we return the array type
     whose atom type is the one of the substituted rest,
     and whose shape is the function shape
     followed by the shape of the substituted rest.")
   (xdoc::p
    "In the rule in [thesis],
     @($(x\\ \\gamma)\\ldots$) corresponds to @('var') in our code,
     @($\\tau_p$) corresponds to the element type of @('rest-type'),
     @($\\iota_p$) corresponds to the ispace of @('rest-type'),
     and @($\\iota_f$) corresponds to @('fun-ispace')."))
  (b* (((ok fun-type+ispace) (type-match-array fun-type))
       (fun-type (type+ispace->type fun-type+ispace))
       (fun-ispace (type+ispace->ispace fun-type+ispace))
       (fun-shape (shape-from-ispace fun-ispace))
       ((ok fun-var+type) (type-match-product fun-type))
       (var (ispacevar+type->var fun-var+type))
       (rest-type (ispacevar+type->type fun-var+type))
       ((unless (check-ispace arg ienv)) (reserr nil))
       (arg (senv-expand-ispace arg ienv))
       ((ok (stringdimmap+stringshapemap ispace-maps))
        (check-ispace-params-and-args (list var) (list arg)))
       (rest-type-subst
        (type-subst-ispace-vars-alpha rest-type
                                      ispace-maps.dim-map
                                      ispace-maps.shape-map))
       ((ok rest-type+ispace) (type-match-array rest-type-subst))
       (rest-atom-type (type+ispace->type rest-type+ispace))
       (rest-ispace (type+ispace->ispace rest-type+ispace))
       (rest-shape (shape-from-ispace rest-ispace)))
    (make-type-array
     :elem rest-atom-type
     :ispace (ispace-shape (shape-append (list fun-shape rest-shape))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-iappn ((fun-type typep) (args ispace-listp) (ienv ispace-senvp))
  :returns (type type-resultp)
  :short "Check an n-ary ispace application,
          given the type of the function and the ispace arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An n-ary ispace application is sugar for
     a left-nested chain of unary ispace applications (see @(tsee expr)).
     Accordingly, we check it by folding @(tsee check-iapp)
     over the ispace arguments, from left to right.
     If there are no arguments, we return the type of the function;
     but note that well-formed n-ary ispace applications
     have two or more arguments (see @(tsee expr))."))
  (b* (((when (endp args)) (type-fix fun-type))
       ((ok type) (check-iapp fun-type (car args) ienv)))
    (check-iappn type (cdr args) ienv))
  :measure (len args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-bind-type-annotation ((anno-type type-optionp)
                                    (expr-type typep)
                                    (ienv ispace-senvp)
                                    (tenv type-senvp))
  :returns (yes/no booleanp)
  :short "Check the optional type annotation of a binding
          against an expression type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Several kinds of bindings have an optional type annotation
     (see @(tsee bind)),
     which must be equivalent to the type of the expression
     that the type annotation pertains to.
     If the type annotation is absent, there is nothing to check.
     If it is present, it must be a valid type that,
     once expanded against the definitions in the static environments
     (see @(tsee senv-expand-type)),
     and once lifted to a scalar array type if it is an atom type,
     is equivalent to the calculated expression type passed as argument
     (which is already expanded).
     The lifting to a scalar array is needed because
     the expression type is always an array type,
     while the annotating type may be an atom type.
     The lifting must be done after the expansion,
     because otherwise if the annotating type is an array type variable,
     its lifting would fail,
     but if it expands to a non-variable instead,
     then lifting would succeed."))
  (type-option-case
   anno-type
   :none t
   :some (b* (((unless (check-type anno-type.val ienv tenv)) nil)
              (anno-type (senv-expand-type anno-type.val ienv tenv))
              ((when (reserrp anno-type)) nil)
              (anno-type (type-ensure-array anno-type)))
           (type-equivp expr-type anno-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type+expr
  :short "Fixtype of pairs consisting of a type and an expression."
  ((type type)
   (expr expr))
  :pred type+expr-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+expr-result
  :short "Fixtype of (i) pairs consisting of a type and an expression
          and (ii) errors."
  :ok type+expr
  :pred type+expr-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod types+exprs
  :short "Fixtype of pairs consisting of
          a list of types and a list of expressions."
  ((types type-list)
   (exprs expr-list))
  :pred types+exprs-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult types+exprs-result
  :short "Fixtype of
          (i) pairs consisting of a list of types and a list of expressions
          and (ii) errors."
  :ok types+exprs
  :pred types+exprs-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type+atom
  :short "Fixtype of pairs consisting of a type and an atom."
  ((type type)
   (atom atom))
  :pred type+atom-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+atom-result
  :short "Fixtype of (i) pairs consisting of a type and an atom
          and (ii) errors."
  :ok type+atom
  :pred type+atom-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod types+atoms
  :short "Fixtype of pairs consisting of
          a list of types and a list of atoms."
  ((types type-list)
   (atoms atom-list))
  :pred types+atoms-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult types+atoms-result
  :short "Fixtype of
          (i) pairs consisting of a list of types and a list of atoms
          and (ii) errors."
  :ok types+atoms
  :pred types+atoms-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senvs+bind
  :short "Fixtype of tuples consisting of
          the three static environments and a binding."
  ((ienv ispace-senv)
   (tenv type-senv)
   (eenv expr-senv)
   (bind bind))
  :pred senvs+bind-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult senvs+bind-result
  :short "Fixtype of
          (i) tuples consisting of the three static environments and a binding
          and (ii) errors."
  :ok senvs+bind
  :pred senvs+bind-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senvs+binds
  :short "Fixtype of tuples consisting of
          the three static environments and a list of bindings."
  ((ienv ispace-senv)
   (tenv type-senv)
   (eenv expr-senv)
   (binds bind-list))
  :pred senvs+binds-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult senvs+binds-result
  :short "Fixtype of
          (i) tuples consisting of
          the three static environments and a list of bindings
          and (ii) errors."
  :ok senvs+binds
  :pred senvs+binds-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory
  (enable type+expr-p-when-result-not-error
          types+exprs-p-when-result-not-error
          type+atom-p-when-result-not-error
          types+atoms-p-when-result-not-error
          senvs+bind-p-when-result-not-error
          senvs+binds-p-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check/infer-app ((fun-type typep)
                         (fun-expr exprp)
                         (arg-type typep)
                         (arg-expr exprp)
                         (ienv ispace-senvp)
                         (tenv type-senvp))
  :returns (type+expr type+expr-resultp)
  :short "Check a unary term application,
          inferring the type and ispace applications of the function if needed;
          if successful,
          return the type of the application and the application expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is given the types and the (already checked) expressions
     of the function and of the argument.")
   (xdoc::p
    "If the type of the function has
     no leading universal or product binders (see @(tsee type-peel-binders)),
     we just use @(tsee check-app),
     and we return the application of the function to the argument.")
   (xdoc::p
    "Otherwise, we infer the type and ispace arguments
     that instantiate those binders.
     The type under the binders must be a function type with an input:
     the argument type must match its first input type,
     with the peeled variables as the only pattern variables
     (see @(tsee type-match-vars)).
     Each peeled variable must be bound by the resulting substitutions,
     i.e. it must occur in the input type;
     otherwise, the argument does not determine its instantiation,
     and we fail.
     We instantiate the binders in order,
     via @(tsee check-tapp) and @(tsee check-iapp),
     which validate the inferred arguments and calculate the resulting types,
     while we wrap the function expression
     in the corresponding type and ispace applications.
     Finally, we use @(tsee check-app) on the instantiated function type,
     and we return the application of the wrapped function to the argument.")
   (xdoc::p
    "This inference is limited for now:
     the argument type must match the whole input type
     (i.e. without any frame prefix)."))
  (b* (((mv vars rest) (type-peel-binders fun-type))
       ((unless (consp vars))
        (b* (((ok type) (check-app fun-type arg-type)))
          (make-type+expr :type type
                          :expr (make-expr-app :fun fun-expr :arg arg-expr))))
       ((ok in+rest) (type-match-fun rest))
       (in-type (type+type->type1 in+rest))
       ((mv ivars tvars) (type/ispace-var-list-to-sets vars))
       ((mv okp dim-subst shape-subst atom-subst array-subst)
        (type-match-vars arg-type in-type ivars tvars))
       ((unless okp) (reserr nil))
       ((ok (type+expr fun)) (check/infer-app-loop vars
                                                   fun-type
                                                   fun-expr
                                                   dim-subst
                                                   shape-subst
                                                   atom-subst
                                                   array-subst
                                                   ienv
                                                   tenv))
       ((ok type) (check-app fun.type arg-type)))
    (make-type+expr :type type
                    :expr (make-expr-app :fun fun.expr :arg arg-expr)))

  :prepwork

  ((define check/infer-app-loop ((vars type/ispace-var-listp)
                                 (fun-type typep)
                                 (fun-expr exprp)
                                 (dim-subst string-dim-mapp)
                                 (shape-subst string-shape-mapp)
                                 (atom-subst string-type-mapp)
                                 (array-subst string-type-mapp)
                                 (ienv ispace-senvp)
                                 (tenv type-senvp))
     :returns (type+expr type+expr-resultp)
     :parents nil
     (b* (((when (endp vars))
           (make-type+expr :type fun-type :expr fun-expr))
          (var (car vars)))
       (type/ispace-var-case
        var
        :type
        (b* ((type? (atom/array-subst-lookup var.var atom-subst array-subst)))
          (type-option-case
           type?
           :none (reserr nil)
           :some (b* (((ok fun-type) (check-tapp fun-type type?.val ienv tenv))
                      (fun-expr (make-expr-tapp :fun fun-expr :arg type?.val)))
                   (check/infer-app-loop (cdr vars)
                                         fun-type
                                         fun-expr
                                         dim-subst
                                         shape-subst
                                         atom-subst
                                         array-subst
                                         ienv
                                         tenv))))
        :ispace
        (b* ((ispace? (dim/shape-subst-lookup var.var dim-subst shape-subst)))
          (ispace-option-case
           ispace?
           :none (reserr nil)
           :some (b* (((ok fun-type) (check-iapp fun-type ispace?.val ienv))
                      (fun-expr (make-expr-iapp :fun fun-expr
                                                :arg ispace?.val)))
                   (check/infer-app-loop (cdr vars)
                                         fun-type
                                         fun-expr
                                         dim-subst
                                         shape-subst
                                         atom-subst
                                         array-subst
                                         ienv
                                         tenv))))))
     :measure (len vars)
     :verify-guards :after-returns
     :hooks ((:fix :hints (("Goal"
                            :induct t
                            :in-theory (enable type/ispace-var-list-fix))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-exprs/atoms/binds
  :short "Check expressions, atoms, and lists thereof,
          returning the input ASTs augmented with some type information."
  :long
  (xdoc::topstring
   (xdoc::p
    "Because of type equivalence,
     an expression or atom may not have a unique type,
     but rather a set of possible equivalent types.
     Our checking functions return a particular type,
     based on the syntactic specifics of the expression or atom.
     Type equivalence is used to compare types,
     e.g. the type of an argument against the type of a parameter.
     This approach should be equivalent to the typing rules,
     which may assign multiple equivalent types to an expression or an atom;
     but we should formally prove all of this.")
   (xdoc::p
    "These functions maintain the invariant that
     every type they return is fully expanded
     with respect to the definitions in the static environments
     (see @(tsee senv-expand-type)):
     that is, every ispace or type variable
     that a @('let') binds to a definition
     has been replaced with that definition.
     The invariant is established by
     expanding every syntactic type or ispace as it enters the checker
     (in the empty array and frame expressions,
     the lambda and box atoms,
     the type and ispace application arguments,
     the combined function binding type,
     and the binding type annotations),
     and by expanding the type associated to a variable when it is looked up;
     every other case builds its result from
     already-checked, and thus already-expanded, sub-results
     (possibly combined with the expanded syntactic pieces just mentioned),
     which preserves the invariant.
     Thanks to this invariant,
     the operations that match the structure of a type
     (@(tsee type-match-array) and similar)
     and that test type equivalence (@(tsee type-equivp) and similar)
     never need to expand their inputs,
     because those inputs are always results of these checking functions.
     We should prove this invariant as a theorem,
     saying that type expansion is a no-op on the results of these functions.")
   (xdoc::p
    "In addition to the type(s)
     (or the static environments, in the case of bindings),
     each of these functions also returns
     the expression, atom, or binding being checked,
     possibly augmented with some type information."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr ((expr exprp)
                      (ienv ispace-senvp)
                      (tenv type-senvp)
                      (eenv expr-senvp))
    :returns (type+expr type+expr-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check an expression; if successful,
            return its type and the type-augmented expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the expression static environment.")
     (xdoc::p
      "An atom expression is an atom auto-lifted to a rank-0 (scalar) array.
       We check the atom, and return the array type
       whose element type is the atom type and whose shape is empty.")
     (xdoc::p
      "For a (non-empty) array, there must be no zero dimension,
       and the number of atoms must match the product of the dimensions.
       We type-check all the atoms,
       which must have all equivalent types.
       We pick the first type from the list of types (which must be non-empty)
       as the atom type for the array type.
       We form a shape with the dimensions,
       and we return the array type.")
     (xdoc::p
      "For an empty array, there must be a 0 dimension.
       The type must be valid and atom-kinded.
       We form a shape with the dimensions, and we return the array type.")
     (xdoc::p
      "A (non-empty) frame is similar to a (non-empty) array,
       but the expressions must have all equivalent array types,
       and the shape of the resulting array type is
       the concatenation of the dimensions with
       the shape of the array type of the expressions
       (we pick the first one).")
     (xdoc::p
      "An empty frame is similar to an empty array,
       but the type must be an explicit array type (not an array type variable),
       whose shape is concatenated after the frame's dimensions.")
     (xdoc::p
      "A string is always statically valid.
       It is syntactic sugar for a mono-dimensional array of integers,
       where the size is the number of character literals.")
     (xdoc::p
      "For a unary term application,
       first we check the function and argument expressions,
       and then we use @(tsee check/infer-app) to check
       the argument type against the function type,
       inferring type and ispace applications of the function if needed,
       and to obtain the type of the application expression
       along with the (possibly augmented) application expression.
       For an n-ary term application,
       we check the function and argument expressions,
       and then we use @(tsee check-appn),
       which performs no inference for now.")
     (xdoc::p
      "For a unary type application,
       first we check the function expression,
       and then we use @(tsee check-tapp) to check
       the type argument against the function type,
       and to obtain the type of the application expression.
       For an n-ary type application, we proceed the same way,
       but via @(tsee check-tappn).")
     (xdoc::p
      "For a unary ispace application,
       first we check the function expression,
       and then we use @(tsee check-iapp) to check
       the ispace argument against the function type,
       and to obtain the type of the application expression.
       For an n-ary ispace application, we proceed the same way,
       but via @(tsee check-iappn).")
     (xdoc::p
      "A combined application combines, in order,
       a type application (if type arguments are present),
       an ispace application (if ispace arguments are present),
       and a term application (see @(tsee expr)).
       So, after checking the function expression,
       we thread the type of the function
       through @(tsee check-tappn), @(tsee check-iappn), and @(tsee check-appn),
       in this order,
       skipping the type and ispace applications
       when the respective arguments are absent.")
     (xdoc::p
      "For an unboxing expression,
       first we check that the ispace variables have no duplicates;
       two variables with the same name but different sorts
       (one dimension and one shape) count as distinct.
       This no-duplicates check is omitted for unary unboxing expressions.
       We check the target expression,
       which must be an array type of a sum type.
       In [arxiv] and [thesis],
       @($\\iota_s$) corresponds to @('sum-shape') in our code,
       @($(x'\\ \\gamma)\\ldots$) corresponds to @('sum-vars'),
       and @($\\tau_s$) corresponds to @('sum-body-type').
       The number of bound variables in the sum type must be the same as
       the number of the ispace variables in the unboxing expression.
       In the sum type body,
       we rename the bound variables to the ispace variables,
       avoiding variable capture by alpha-renaming as needed
       (see @(tsee type-rename-ispace-vars-alpha)):
       we associate the resulting type
       to the term variable of the unboxing expression,
       and we extend the static environments
       with that association and with the ispace variables.
       We check the body expression of the unboxing expression
       in the extended static environments;
       we must get an explicit array type.
       In [arxiv] and [thesis],
       the latter array has atom type @($\\tau_b$) and ispace @($\\iota_b$),
       which correspond to @('body-atom-type') and @('body-ispace') in our code.
       This array type must not contain occurrences of
       the ispace variables bound in the unboxing expression,
       which do not exist outside the unboxing expression.
       [thesis] explains this condition in text,
       but it expresses in the inference rule by saying that
       the type must be well-formed
       in the type enviroment prior to its extension with the ispace bindings;
       but this check is not reliable in case the prior environment
       happens to bind ispace variables that are shadowed by
       the ones bound in the unboxing expression.
       The type of the unboxing expression is the array type consisting of
       the @($\\tau_b$) type as atom
       and the concatenation of @($\\iota_s$) and @($\\iota_b$) as ispace.
       We store this type into the optional type slot of
       the returned unboxing expression.")
     (xdoc::p
      "A bracket expression is syntactic sugar for a (non-empty) frame
       whose dimensions consist of a single dimension,
       namely the number of sub-expressions (see @(tsee expr));
       so we check it like a (non-empty) frame.
       There must be at least one sub-expression;
       bracket expressions cannot be empty.
       The sub-expressions must have all equivalent array types,
       and the shape of the resulting array type is
       the single dimension, given by the number of sub-expressions,
       concatenated with the shape of the array type of the sub-expressions
       (we pick the first one).")
     (xdoc::p
      "For a @('let') expression,
       we check the bindings,
       which extend the static environments (see @(tsee check-bind-list)),
       and then we check the body in the extended static environments."))
    (expr-case
     expr
     :var
     (b* ((name+type (omap::assoc expr.name (expr-senv->exprs eenv)))
          ((unless name+type) (reserr nil))
          ((ok type) (senv-expand-type (cdr name+type) ienv tenv)))
       (make-type+expr :type type :expr (expr-fix expr)))
     :atom
     (b* (((ok (type+atom ta)) (check-atom expr.atom ienv tenv eenv)))
       (make-type+expr
        :type (make-type-array :elem ta.type
                               :ispace (ispace-shape (shape-dims nil)))
        :expr (make-expr-atom :atom ta.atom)))
     :array
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.atoms)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok (types+atoms tas)) (check-atom-list expr.atoms ienv tenv eenv))
          ((unless (type-list-all-equivp tas.types)) (reserr nil))
          (type (car tas.types)))
       (make-type+expr
        :type (make-type-array :elem type
                               :ispace (ispace-shape
                                        (shape-dims (dim-const-list expr.dims))))
        :expr (make-expr-array :dims expr.dims :atoms tas.atoms)))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((unless (check-type expr.type ienv tenv)) (reserr nil))
          ((unless (type-atom-kindp expr.type)) (reserr nil))
          ((ok elem) (senv-expand-type expr.type ienv tenv)))
       (make-type+expr
        :type (make-type-array :elem elem
                               :ispace (ispace-shape
                                        (shape-dims (dim-const-list expr.dims))))
        :expr (expr-fix expr)))
     :frame
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.exprs)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok (types+exprs tes)) (check-expr-list expr.exprs ienv tenv eenv))
          ((unless (type-list-all-equivp tes.types)) (reserr nil))
          (type (car tes.types))
          ((ok (type+ispace array)) (type-match-array type)))
       (make-type+expr
        :type (make-type-array
               :elem array.type
               :ispace (ispace-shape
                        (shape-append
                         (list (shape-dims (dim-const-list expr.dims))
                               (shape-from-ispace array.ispace)))))
        :expr (make-expr-frame :dims expr.dims :exprs tes.exprs)))
     :frame-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((unless (check-type expr.type ienv tenv)) (reserr nil))
          ((ok type) (senv-expand-type expr.type ienv tenv))
          ((ok (type+ispace array)) (type-match-array type)))
       (make-type+expr
        :type (make-type-array
               :elem array.type
               :ispace (ispace-shape
                        (shape-append
                         (list (shape-dims (dim-const-list expr.dims))
                               (shape-from-ispace array.ispace)))))
        :expr (expr-fix expr)))
     :string
     (make-type+expr
      :type (make-type-array :elem (type-base (base-type-int))
                             :ispace (ispace-shape
                                      (shape-dims
                                       (list (dim-const (len expr.chars))))))
      :expr (expr-fix expr))
     :app
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok (type+expr ae)) (check-expr expr.arg ienv tenv eenv)))
       (check/infer-app fe.type fe.expr ae.type ae.expr ienv tenv))
     :appn
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok (types+exprs aes)) (check-expr-list expr.args ienv tenv eenv))
          ((ok type) (check-appn fe.type aes.types)))
       (make-type+expr :type type
                       :expr (make-expr-appn :fun fe.expr :args aes.exprs)))
     :tapp
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok type) (check-tapp fe.type expr.arg ienv tenv)))
       (make-type+expr :type type
                       :expr (make-expr-tapp :fun fe.expr :arg expr.arg)))
     :tappn
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok type) (check-tappn fe.type expr.args ienv tenv)))
       (make-type+expr :type type
                       :expr (make-expr-tappn :fun fe.expr :args expr.args)))
     :iapp
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok type) (check-iapp fe.type expr.arg ienv)))
       (make-type+expr :type type
                       :expr (make-expr-iapp :fun fe.expr :arg expr.arg)))
     :iappn
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          ((ok type) (check-iappn fe.type expr.args ienv)))
       (make-type+expr :type type
                       :expr (make-expr-iappn :fun fe.expr :args expr.args)))
     :capp
     (b* (((ok (type+expr fe)) (check-expr expr.fun ienv tenv eenv))
          (fun-type fe.type)
          ((ok fun-type)
           (type-list-option-case
            expr.targs
            :some (check-tappn fun-type expr.targs.val ienv tenv)
            :none fun-type))
          ((ok fun-type)
           (ispace-list-option-case
            expr.iargs
            :some (check-iappn fun-type expr.iargs.val ienv)
            :none fun-type))
          ((ok (types+exprs aes)) (check-expr-list expr.args ienv tenv eenv))
          ((ok type) (check-appn fun-type aes.types)))
       (make-type+expr
        :type type
        :expr (make-expr-capp :fun fe.expr
                              :targs expr.targs
                              :iargs expr.iargs
                              :args aes.exprs)))
     :unbox
     (b* (((ok (type+expr targ)) (check-expr expr.target ienv tenv eenv))
          ((ok target-arr-type+ispace) (type-match-array targ.type))
          (sum-type (type+ispace->type target-arr-type+ispace))
          (sum-ispace (type+ispace->ispace target-arr-type+ispace))
          (sum-shape (shape-from-ispace sum-ispace))
          ((ok sum-vars+type) (type-match-sum sum-type))
          (sum-vars (ispacevarlist+type->vars sum-vars+type))
          (sum-body-type (ispacevarlist+type->type sum-vars+type))
          ((unless (= 1 (len sum-vars))) (reserr nil))
          ((ok (string-string-map-pair renaming))
           (check-ispace-var-renaming sum-vars (list expr.ispace)))
          (sum-body-type-renam
           (type-rename-ispace-vars-alpha sum-body-type
                                          renaming.1st
                                          renaming.2nd))
          (ienv (ispace-senv-add-var expr.ispace ienv))
          (eenv (expr-senv-add-var expr.var sum-body-type-renam eenv))
          ((ok (type+expr be)) (check-expr expr.body ienv tenv eenv))
          ((unless (set::emptyp
                    (set::intersect (set::insert expr.ispace nil)
                                    (type-free-ispace-vars be.type))))
           (reserr nil))
          ((ok arr-type+ispace) (type-match-array be.type))
          (body-atom-type (type+ispace->type arr-type+ispace))
          (body-ispace (type+ispace->ispace arr-type+ispace))
          (body-shape (shape-from-ispace body-ispace))
          (type (make-type-array :elem body-atom-type
                                 :ispace (ispace-shape
                                          (shape-append
                                           (list sum-shape body-shape))))))
       (make-type+expr
        :type type
        :expr (make-expr-unbox :ispace expr.ispace
                               :var expr.var
                               :target targ.expr
                               :body be.expr
                               :type? type)))
     :unboxn
     (b* (((unless (no-duplicatesp-equal expr.ispaces)) (reserr nil))
          ((ok (type+expr targ)) (check-expr expr.target ienv tenv eenv))
          ((ok target-arr-type+ispace) (type-match-array targ.type))
          (sum-type (type+ispace->type target-arr-type+ispace))
          (sum-ispace (type+ispace->ispace target-arr-type+ispace))
          (sum-shape (shape-from-ispace sum-ispace))
          ((ok sum-vars+type) (type-match-sum sum-type))
          (sum-vars (ispacevarlist+type->vars sum-vars+type))
          (sum-body-type (ispacevarlist+type->type sum-vars+type))
          ((unless (= (len expr.ispaces) (len sum-vars))) (reserr nil))
          ((ok (string-string-map-pair renaming))
           (check-ispace-var-renaming sum-vars expr.ispaces))
          (sum-body-type-renam
           (type-rename-ispace-vars-alpha sum-body-type
                                          renaming.1st
                                          renaming.2nd))
          (ienv (ispace-senv-add-vars expr.ispaces ienv))
          (eenv (expr-senv-add-var expr.var sum-body-type-renam eenv))
          ((ok (type+expr be)) (check-expr expr.body ienv tenv eenv))
          ((unless (set::emptyp
                    (set::intersect (set::mergesort expr.ispaces)
                                    (type-free-ispace-vars be.type))))
           (reserr nil))
          ((ok arr-type+ispace) (type-match-array be.type))
          (body-atom-type (type+ispace->type arr-type+ispace))
          (body-ispace (type+ispace->ispace arr-type+ispace))
          (body-shape (shape-from-ispace body-ispace))
          (type (make-type-array :elem body-atom-type
                                 :ispace (ispace-shape
                                          (shape-append
                                           (list sum-shape body-shape))))))
       (make-type+expr
        :type type
        :expr (make-expr-unboxn :ispaces expr.ispaces
                                :var expr.var
                                :target targ.expr
                                :body be.expr
                                :type? type)))
     :bracket
     (b* (((ok (types+exprs es)) (check-expr-list expr.exprs ienv tenv eenv))
          ((unless (type-list-all-equivp es.types)) (reserr nil))
          (type (car es.types))
          ((ok (type+ispace array)) (type-match-array type)))
       (make-type+expr
        :type (make-type-array
               :elem array.type
               :ispace (ispace-shape
                        (shape-append
                         (list (shape-dims
                                (dim-const-list (list (len expr.exprs))))
                               (shape-from-ispace array.ispace)))))
        :expr (make-expr-bracket :exprs es.exprs)))
     :let
     (b* (((ok (senvs+binds sbs))
           (check-bind-list expr.binds ienv tenv eenv))
          ((ok (type+expr be))
           (check-expr expr.body sbs.ienv sbs.tenv sbs.eenv)))
       (make-type+expr :type be.type
                       :expr (make-expr-let :binds sbs.binds :body be.expr))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr-list ((exprs expr-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp)
                           (eenv expr-senvp))
    :returns (types+exprs types+exprs-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check a list of expressions; if successful,
            return their types and the type-augmented expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the expressions."))
    (b* (((when (endp exprs))
          (make-types+exprs :types nil :exprs nil))
         ((ok (type+expr te)) (check-expr (car exprs) ienv tenv eenv))
         ((ok (types+exprs tes))
          (check-expr-list (cdr exprs) ienv tenv eenv)))
      (make-types+exprs :types (cons te.type tes.types)
                        :exprs (cons te.expr tes.exprs)))
    :measure (expr-list-count exprs)

    ///

    (defret len-of-check-expr-list
      (implies (not (reserrp types+exprs))
               (equal (len (types+exprs->types types+exprs))
                      (len exprs)))
      :hints (("Goal" :induct (len exprs) :in-theory (enable len))))

    (defret check-expr-list-iff-not-zp-len-exprs
      (implies (not (reserrp types+exprs))
               (iff (types+exprs->types types+exprs)
                    (not (zp (len exprs)))))
      :hints (("Goal" :induct (len exprs) :in-theory (enable len))))

    (defret consp-of-exprs-of-check-expr-list
      (implies (and (not (reserrp types+exprs))
                    (consp exprs))
               (consp (types+exprs->exprs types+exprs)))
      :hints (("Goal" :expand ((check-expr-list exprs ienv tenv eenv))))
      :rule-classes ((:rewrite) (:type-prescription)))

    (defret len-of-exprs-of-check-expr-list
      (implies (not (reserrp types+exprs))
               (equal (len (types+exprs->exprs types+exprs))
                      (len exprs)))
      :hints (("Goal" :induct (len exprs) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom ((atom atomp)
                      (ienv ispace-senvp)
                      (tenv type-senvp)
                      (eenv expr-senvp))
    :returns (type+atom type+atom-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check an atom; if successful,
            return its type and the type-augmented atom."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value
       is independent from the static environments,
       and determined via separate functions.")
     (xdoc::p
      "For an n-ary term abstraction,
       first we check that there are no duplicate bound variable names.
       We check that the types of the parameters are valid
       (see @(tsee check-type-list)).
       We extend the expression static environment with the bound variables,
       and we check the body of the abstraction
       in the extended static environment.
       Its type is the output type of the function type of the abstraction,
       and its input types are the ones of the bound variables.
       We store the body's type into the optional type slot of
       the returned lambda atom.
       A unary term abstraction is checked in the same way,
       except that there is no duplicate check
       (there is just one bound variable),
       and its type is the unary function type
       whose input type is the one of the parameter.")
     (xdoc::p
      "For an n-ary type abstraction,
       first we check that there are no duplicate bound variables;
       two variables with the same name but different kinds
       (one atom and one array) count as distinct.
       We check the body of the abstraction in the extended environment.
       The resulting type is the body of the universal type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.
       A unary type abstraction is checked in the same way,
       except that there is no duplicate check
       (there is just one bound variable),
       and its type is the unary universal type over that variable.")
     (xdoc::p
      "For an n-ary ispace abstraction,
       first we check that there are no duplicate bound variables;
       two variables with the same name but different sorts
       (one dimension and one shape) count as distinct.
       We check the body of the abstraction.
       The resulting type is the body of the product type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.
       A unary ispace abstraction is checked in the same way,
       except that there is no duplicate check
       (there is just one bound variable),
       and its type is the unary product type over that variable.")
     (xdoc::p
      "For a unary boxing atom,
       the ispace must be valid (see @(tsee check-ispace)),
       and the type, which is optional in the abstract syntax,
       must be present, valid (see @(tsee check-type)), and a sum type;
       an unannotated unary boxing atom
       (an inner box of the nest that an n-ary boxing atom desugars to)
       is only accepted within an annotated one,
       via @(tsee check-box-inner).
       We peel off the first parameter of the sum type,
       we check that the ispace has the same sort,
       obtaining a dimension or shape substitution,
       and we apply the substitution to the rest of the sum type;
       the substitution avoids variable capture
       by automatically alpha-renaming bound variables as needed
       (see @(tsee type-subst-ispace-vars-alpha)).
       The array expression is checked against the resulting type
       by @(tsee check-box-inner),
       which also handles the inner boxes of
       desugared n-ary boxing atoms.
       The type of the boxing atom is the sum type.
       This treatment corresponds to @('checkAtom') in [impl].")
     (xdoc::p
      "For an n-ary boxing atom, the treatment is analogous,
       including the requirement that the type be present,
       but all the parameters of the sum type are matched
       against the ispaces of the boxing atom at once,
       and the array expression is checked directly."))
    (atom-case
     atom
     :base
     (make-type+atom
      :type (type-base (base-type-of-base-lit atom.lit))
      :atom (atom-fix atom))
     :lambda
     (b* (((ok type) (var+type?->type-or-err atom.param))
          ((unless (check-type type ienv tenv)) (reserr nil))
          ((ok type) (senv-expand-type type ienv tenv))
          ((ok eenv)
           (expr-senv-add-var (var+type?->var atom.param) type eenv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-fun :in type :out be.type)
        :atom (make-atom-lambda :param atom.param
                                :body be.expr
                                :type? be.type)))
     :lambdan
     (b* (((unless (no-duplicatesp-equal (var+type?-list->var atom.params)))
           (reserr nil))
          ((ok types) (var+type?-list->type-list-or-err atom.params))
          ((unless (check-type-list types ienv tenv)) (reserr nil))
          ((ok types) (senv-expand-type-list types ienv tenv))
          ((ok eenv)
           (expr-senv-add-vars
            (var+type?-list-set-types types atom.params)
            eenv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-funn :in types :out be.type)
        :atom (make-atom-lambdan :params atom.params
                                 :body be.expr
                                 :type? be.type)))
     :tlambda
     (b* ((tenv (type-senv-add-var atom.param tenv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-forall :param atom.param :body be.type)
        :atom (make-atom-tlambda :param atom.param :body be.expr)))
     :tlambdan
     (b* (((unless (no-duplicatesp-equal atom.params)) (reserr nil))
          (tenv (type-senv-add-vars atom.params tenv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-foralln :params atom.params :body be.type)
        :atom (make-atom-tlambdan :params atom.params :body be.expr)))
     :ilambda
     (b* ((ienv (ispace-senv-add-var atom.param ienv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-pi :param atom.param :body be.type)
        :atom (make-atom-ilambda :param atom.param :body be.expr)))
     :ilambdan
     (b* (((unless (no-duplicatesp-equal atom.params)) (reserr nil))
          (ienv (ispace-senv-add-vars atom.params ienv))
          ((ok (type+expr be)) (check-expr atom.body ienv tenv eenv)))
       (make-type+atom
        :type (make-type-pin :params atom.params :body be.type)
        :atom (make-atom-ilambdan :params atom.params :body be.expr)))
     :box
     (b* (((unless (check-ispace atom.ispace ienv)) (reserr nil))
          (ispace (senv-expand-ispace atom.ispace ienv))
          ((ok type) (type-option-case atom.type?
                                       :some atom.type?.val
                                       :none (reserr nil)))
          ((unless (type-atom-kindp type)) (reserr nil))
          ((unless (check-type type ienv tenv)) (reserr nil))
          ((ok box-type) (senv-expand-type type ienv tenv))
          ((ok vars+type) (type-match-sum box-type))
          (vars (ispacevarlist+type->vars vars+type))
          (body-type (ispacevarlist+type->type vars+type))
          ((ok (stringdimmap+stringshapemap maps))
           (check-ispace-params-and-args (list (car vars)) (list ispace)))
          (rest-type (sigma-curried-body vars body-type))
          (rest-type-subst
           (type-subst-ispace-vars-alpha rest-type
                                         maps.dim-map
                                         maps.shape-map))
          ((ok (type+expr ae)) (check-box-inner rest-type-subst
                                                atom.array
                                                ienv
                                                tenv
                                                eenv)))
       (make-type+atom
        :type box-type
        :atom (make-atom-box :ispace atom.ispace
                             :array ae.expr
                             :type? atom.type?)))
     :boxn
     (b* (((unless (check-ispace-list atom.ispaces ienv)) (reserr nil))
          (ispaces (senv-expand-ispace-list atom.ispaces ienv))
          ((ok type) (type-option-case atom.type?
                                       :some atom.type?.val
                                       :none (reserr nil)))
          ((unless (type-atom-kindp type)) (reserr nil))
          ((unless (check-type type ienv tenv)) (reserr nil))
          ((ok box-type) (senv-expand-type type ienv tenv))
          ((ok vars+type) (type-match-sum box-type))
          (vars (ispacevarlist+type->vars vars+type))
          (body-type (ispacevarlist+type->type vars+type))
          ((ok (stringdimmap+stringshapemap maps))
           (check-ispace-params-and-args vars ispaces))
          (body-type-subst
           (type-subst-ispace-vars-alpha body-type
                                         maps.dim-map
                                         maps.shape-map))
          ((ok (type+expr ae)) (check-expr atom.array ienv tenv eenv))
          ((unless (type-equivp ae.type body-type-subst)) (reserr nil)))
       (make-type+atom
        :type box-type
        :atom (make-atom-boxn :ispaces atom.ispaces
                              :array ae.expr
                              :type? atom.type?))))
    :measure (atom-count atom))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-box-inner ((type typep)
                           (body exprp)
                           (ienv ispace-senvp)
                           (tenv type-senvp)
                           (eenv expr-senvp))
    :returns (type+expr type+expr-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check the array expression of a unary boxing atom
            against the expected type."
    :long
    (xdoc::topstring
     (xdoc::p
      "The expected type is the body of
       the sum type of the enclosing boxing atom,
       with the first parameter of the sum type
       replaced with the ispace of the boxing atom.")
     (xdoc::p
      "If the expression is an inner box of
       the nest that an n-ary boxing atom desugars to,
       i.e. a zero-rank array of a single unannotated unary boxing atom
       (see @(tsee expr-match-unannotated-box)),
       the expected type must be a sum type:
       we peel off its first parameter,
       we check that the (valid) ispace of the boxing atom has the same sort,
       and we recursively check the array expression of the boxing atom
       against the rest of the sum type with the parameter substituted;
       the boxing atom is annotated with the expected type,
       which is also its type.
       Otherwise, we check the expression normally,
       and its type must be equivalent to the expected type."))
    (b* ((ie (expr-match-unannotated-box body))
         ((when (reserrp ie))
          (b* (((ok (type+expr te)) (check-expr body ienv tenv eenv))
               ((unless (type-equivp te.type type)) (reserr nil)))
            (make-type+expr :type te.type :expr te.expr)))
         ((ispace+expr ie) ie)
         ((ok vars+type) (type-match-sum type))
         (vars (ispacevarlist+type->vars vars+type))
         (body-type (ispacevarlist+type->type vars+type))
         ((unless (check-ispace ie.ispace ienv)) (reserr nil))
         (ispace (senv-expand-ispace ie.ispace ienv))
         ((ok (stringdimmap+stringshapemap maps))
          (check-ispace-params-and-args (list (car vars)) (list ispace)))
         (rest-type (sigma-curried-body vars body-type))
         (rest-type-subst
          (type-subst-ispace-vars-alpha rest-type
                                        maps.dim-map
                                        maps.shape-map))
         ((ok (type+expr inner)) (check-box-inner rest-type-subst
                                                  ie.expr
                                                  ienv
                                                  tenv
                                                  eenv)))
      (make-type+expr
       :type (type-fix type)
       :expr (make-expr-array
              :dims nil
              :atoms (list (make-atom-box :ispace ie.ispace
                                          :array inner.expr
                                          :type? (type-fix type))))))
    :measure (+ 1 (expr-count body)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom-list ((atoms atom-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp)
                           (eenv expr-senvp))
    :returns (types+atoms types+atoms-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check a list of atoms; if successful,
            return their types and the type-augmented atoms."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the atoms."))
    (b* (((when (endp atoms))
          (make-types+atoms :types nil :atoms nil))
         ((ok (type+atom ta)) (check-atom (car atoms) ienv tenv eenv))
         ((ok (types+atoms tas))
          (check-atom-list (cdr atoms) ienv tenv eenv)))
      (make-types+atoms :types (cons ta.type tas.types)
                        :atoms (cons ta.atom tas.atoms)))
    :measure (atom-list-count atoms)

    ///

    (defret len-of-check-atom-list
      (implies (not (reserrp types+atoms))
               (equal (len (types+atoms->types types+atoms))
                      (len atoms)))
      :hints (("Goal" :induct (len atoms) :in-theory (enable len))))

    (defret check-atom-list-iff-not-zp-len-atoms
      (implies (not (reserrp types+atoms))
               (iff (types+atoms->types types+atoms)
                    (not (zp (len atoms)))))
      :hints (("Goal" :induct (len atoms) :in-theory (enable len))))

    (defret consp-of-atoms-of-check-atom-list
      (implies (and (not (reserrp types+atoms))
                    (consp atoms))
               (consp (types+atoms->atoms types+atoms)))
      :hints (("Goal" :expand ((check-atom-list atoms ienv tenv eenv))))
      :rule-classes ((:rewrite) (:type-prescription))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-bind ((bind bindp)
                      (ienv ispace-senvp)
                      (tenv type-senvp)
                      (eenv expr-senvp))
    :returns (senvs+bind senvs+bind-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check a binding; if successful,
            extend the static environments
            and return the type-augmented binding."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used for @('let') expressions; see @(tsee check-expr).
       If the binding is valid,
       we return the static environments extended according to the binding.")
     (xdoc::p
      "For a value binding,
       we check the bound expression, obtaining its type,
       and we extend the expression static environment
       to associate that type to the bound variable.
       If the optional type is present,
       we check that it is valid
       and equivalent to the type of the bound expression.")
     (xdoc::p
      "For a function binding,
       which is syntactic sugar for binding the variable
       to a term abstraction (see @(tsee expr)),
       we check it like a term abstraction (see @(tsee check-atom)),
       obtaining a function type,
       and we extend the expression static environment
       to associate that function type to the bound variable.
       If the optional result type is present,
       we check that it is valid and equivalent to
       the type of the body of the abstraction.
       A function binding with no parameters
       is treated as a plain value binding:
       the variable is bound to the type of the body,
       not wrapped in any function type.
       This is consistent with [impl],
       whose parser turns such a binding
       directly into a value binding.")
     (xdoc::p
      "A type function binding and an ispace function binding
       are treated similarly to a function binding,
       but as syntactic sugar for binding the variable
       to a type abstraction or an ispace abstraction,
       so their types are a universal type or a product type.
       A type function binding or an ispace function binding with no parameters
       is treated as a plain value binding,
       as done for a function binding.")
     (xdoc::p
      "A combined function binding
       is syntactic sugar for binding the variable
       to a term abstraction,
       nested in an ispace abstraction if there are ispace parameters,
       nested in a type abstraction if there are type parameters;
       its type is the corresponding nesting of
       a function type, a product type, and a universal type.
       We check the body in the static environments
       extended with all the parameters,
       and we check that its type is equivalent to the declared result type.
       Each layer is present only if
       the corresponding parameters are present;
       an absent parameter list and an empty one are treated alike,
       consistently with [impl].
       In particular, with no value parameters
       there is no function type layer,
       and with no parameters at all
       the binding is treated as a plain value binding,
       with the variable bound to the type of the body.")
     (xdoc::p
      "For an ispace binding,
       we check that the bound ispace is valid,
       and that its sort matches the bound variable
       (a dimension variable is bound to a dimension,
       a shape variable is bound to a shape).
       We expand the ispace against the ispace static environment's definitions
       (see @(tsee senv-expand-ispace)),
       so that the stored definition is itself fully expanded,
       and we extend the ispace static environment
       to associate that definition to the bound variable.")
     (xdoc::p
      "A type binding is treated similarly,
       checking instead that the kind of the bound type
       matches the bound variable
       (an atom-kind variable is bound to an atom-kind type,
       an array-kind variable is bound to an array-kind type).
       These definitions are taken into account
       by the expansion performed throughout @(tsee check-expr)."))
    (bind-case
     bind
     :ispace
     (b* (((unless (check-ispace bind.ispace ienv)) (reserr nil))
          ((unless (ispace-var-case
                    bind.var
                    :dim (ispace-case bind.ispace :dim)
                    :shape (ispace-case bind.ispace :shape)))
           (reserr nil))
          (ispace (senv-expand-ispace bind.ispace ienv)))
       (make-senvs+bind
        :ienv (ispace-senv-add-def bind.var ispace ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-fix eenv)
        :bind (bind-fix bind)))
     :type
     (b* (((unless (check-type bind.type ienv tenv)) (reserr nil))
          ((unless (type-var-case
                    bind.var
                    :atom (type-atom-kindp bind.type)
                    :array (not (type-atom-kindp bind.type))))
           (reserr nil))
          ((ok type) (senv-expand-type bind.type ienv tenv)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-add-def bind.var type tenv)
        :eenv (expr-senv-fix eenv)
        :bind (bind-fix bind)))
     :val
     (b* (((ok (type+expr ee)) (check-expr bind.expr ienv tenv eenv))
          ((unless (check-bind-type-annotation bind.type? ee.type ienv tenv))
           (reserr nil)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-add-var bind.var ee.type eenv)
        :bind (make-bind-val :var bind.var
                             :type? bind.type?
                             :expr ee.expr)))
     :fun
     (b* (((unless (no-duplicatesp-equal (var+type?-list->var bind.params)))
           (reserr nil))
          ((ok types) (var+type?-list->type-list-or-err bind.params))
          ((unless (check-type-list types ienv tenv)) (reserr nil))
          ((ok types) (senv-expand-type-list types ienv tenv))
          ((ok eenv-body)
           (expr-senv-add-vars
            (var+type?-list-set-types types bind.params)
            eenv))
          ((ok (type+expr ee)) (check-expr bind.expr ienv tenv eenv-body))
          ((unless (check-bind-type-annotation bind.type? ee.type ienv tenv))
           (reserr nil))
          (type (if (consp types)
                    (make-type-array
                     :elem (if (endp (cdr types))
                               (make-type-fun :in (car types) :out ee.type)
                             (make-type-funn :in types :out ee.type))
                     :ispace (ispace-shape (shape-dims nil)))
                  ee.type)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-add-var bind.var type eenv)
        :bind (make-bind-fun :var bind.var
                             :params bind.params
                             :type? bind.type?
                             :expr ee.expr)))
     :tfun
     (b* (((unless (no-duplicatesp-equal bind.params)) (reserr nil))
          (tenv-body (type-senv-add-vars bind.params tenv))
          ((ok (type+expr ee)) (check-expr bind.expr ienv tenv-body eenv))
          ((unless (check-bind-type-annotation bind.type?
                                               ee.type
                                               ienv
                                               tenv-body))
           (reserr nil))
          (type (if (consp bind.params)
                    (make-type-array
                     :elem (make-type-forall/foralln bind.params ee.type)
                     :ispace (ispace-shape (shape-dims nil)))
                  ee.type)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-add-var bind.var type eenv)
        :bind (make-bind-tfun :var bind.var
                              :params bind.params
                              :type? bind.type?
                              :expr ee.expr)))
     :ifun
     (b* (((unless (no-duplicatesp-equal bind.params)) (reserr nil))
          (ienv-body (ispace-senv-add-vars bind.params ienv))
          ((ok (type+expr ee)) (check-expr bind.expr ienv-body tenv eenv))
          ((unless (check-bind-type-annotation bind.type?
                                               ee.type
                                               ienv-body
                                               tenv))
           (reserr nil))
          (type (if (consp bind.params)
                    (make-type-array
                     :elem (make-type-pi/pin bind.params ee.type)
                     :ispace (ispace-shape (shape-dims nil)))
                  ee.type)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-add-var bind.var type eenv)
        :bind (make-bind-ifun :var bind.var
                              :params bind.params
                              :type? bind.type?
                              :expr ee.expr)))
     :cfun
     (b* ((tparams (type-var-list-option-case
                    bind.tparams? :some bind.tparams?.val :none nil))
          (iparams (ispace-var-list-option-case
                    bind.iparams? :some bind.iparams?.val :none nil))
          ((unless (no-duplicatesp-equal tparams)) (reserr nil))
          ((unless (no-duplicatesp-equal iparams)) (reserr nil))
          ((unless (no-duplicatesp-equal (var+type?-list->var bind.params)))
           (reserr nil))
          (tenv-params (type-senv-add-vars tparams tenv))
          (ienv-params (ispace-senv-add-vars iparams ienv))
          ((ok types) (var+type?-list->type-list-or-err bind.params))
          ((unless (check-type-list types ienv-params tenv-params))
           (reserr nil))
          ((unless (check-type bind.type ienv-params tenv-params))
           (reserr nil))
          ((ok btype) (senv-expand-type bind.type ienv-params tenv-params))
          ((ok types) (senv-expand-type-list types ienv-params tenv-params))
          ((ok eenv-body)
           (expr-senv-add-vars
            (var+type?-list-set-types types bind.params)
            eenv))
          ((ok (type+expr ee))
           (check-expr bind.expr ienv-params tenv-params eenv-body))
          ((unless (type-equivp ee.type btype)) (reserr nil))
          (fun-type (if (consp types)
                        (if (endp (cdr types))
                            (make-type-fun :in (car types) :out btype)
                          (make-type-funn :in types :out btype))
                      ee.type))
          (fun-type (if (consp iparams)
                        (make-type-pi/pin iparams fun-type)
                      fun-type))
          (fun-type (if (consp tparams)
                        (make-type-forall/foralln tparams fun-type)
                      fun-type))
          (type (if (or (consp types) (consp iparams) (consp tparams))
                    (make-type-array
                     :elem fun-type
                     :ispace (ispace-shape (shape-dims nil)))
                  ee.type)))
       (make-senvs+bind
        :ienv (ispace-senv-fix ienv)
        :tenv (type-senv-fix tenv)
        :eenv (expr-senv-add-var bind.var type eenv)
        :bind (make-bind-cfun :var bind.var
                              :tparams? bind.tparams?
                              :iparams? bind.iparams?
                              :params bind.params
                              :type bind.type
                              :expr ee.expr))))
    :measure (bind-count bind))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-bind-list ((binds bind-listp)
                           (ienv ispace-senvp)
                           (tenv type-senvp)
                           (eenv expr-senvp))
    :returns (senvs+binds senvs+binds-resultp)
    :parents (type-checker check-exprs/atoms/binds)
    :short "Check a list of bindings; if successful,
            extend the static environments
            and return the type-augmented bindings."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each binding in turn,
       threading through and extending the static environments as we go."))
    (b* (((when (endp binds))
          (make-senvs+binds :ienv (ispace-senv-fix ienv)
                            :tenv (type-senv-fix tenv)
                            :eenv (expr-senv-fix eenv)
                            :binds nil))
         ((ok (senvs+bind sb)) (check-bind (car binds) ienv tenv eenv))
         ((ok (senvs+binds sbs))
          (check-bind-list (cdr binds) sb.ienv sb.tenv sb.eenv)))
      (make-senvs+binds :ienv sbs.ienv
                        :tenv sbs.tenv
                        :eenv sbs.eenv
                        :binds (cons sb.bind sbs.binds)))
    :measure (bind-list-count binds)

    ///

    (defret consp-of-binds-of-check-bind-list
      (implies (and (not (reserrp senvs+binds))
                    (consp binds))
               (consp (senvs+binds->binds senvs+binds)))
      :hints (("Goal" :expand ((check-bind-list binds ienv tenv eenv))))
      :rule-classes ((:rewrite) (:type-prescription))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ///

  (verify-guards check-expr)

  (fty::deffixequiv-mutual check-exprs/atoms/binds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-top-expr ((expr exprp))
  :returns (type+expr type+expr-resultp)
  :short "Check a standalone (top-level) expression,
          returning its type and the expression if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the expression, using the initial static environments.
     We return its type, together with the expression, if successful;
     the returned expression is currently identical to the input,
     as in @(tsee check-exprs/atoms/binds)."))
  (check-expr expr (init-ispace-senv) (init-type-senv) (init-expr-senv)))
