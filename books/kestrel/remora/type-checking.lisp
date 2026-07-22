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
(include-book "abstract-syntax-constructors")
(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-matching-operations")
(include-book "abstract-syntax-variable-operations")
(include-book "type-equivalence")
(include-book "static-environments")
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
          typelist+type-p-when-result-not-error
          ispacevar+type-p-when-result-not-error
          ispacevarlist+type-p-when-result-not-error
          typevar+type-p-when-result-not-error
          typevarlist+type-p-when-result-not-error
          stringdimmap+stringshapemap-p-when-result-not-error
          string-type-mapp-when-result-not-error
          string-type-map-pairp-when-result-not-error
          senvp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-checking
  :parents (static-semantics)
  :short "Type checking of Remora."
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
     It is designed for simplicity."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-dims
  :short "Check dimensions and lists of dimensions."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dim ((dim dimp) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-dims)
    :short "Check a dimension."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "Any constant is valid.")
     (xdoc::p
      "Any addition of valid dimensions is valid.")
     (xdoc::p
      "Any multiplication of valid dimensions is valid.")
     (xdoc::p
      "Any non-empty subtraction of valid dimensions is valid."))
    (dim-case
     dim
     :var (consp (omap::assoc (ispace-var-dim dim.name)
                              (senv->ispace-vars senv)))
     :const t
     :add (check-dim-list dim.dims senv)
     :mul (check-dim-list dim.dims senv)
     :sub (and (check-dim-list dim.dims senv)
               (consp dim.dims)))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-dim-list ((dims dim-listp) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-dims)
    :short "Check a list of dimensions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each dimension in turn,
       returning @('t') iff they are all valid."))
    (or (endp dims)
        (and (check-dim (car dims) senv)
             (check-dim-list (cdr dims) senv)))
    :measure (dim-list-count dims))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-dims))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-shapes/ispaces
  :short "Check shapes, ispaces, and lists thereof."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-shape ((shape shapep) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-shapes/ispaces)
    :short "Check a shape."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return @('t') if the check is successful, otherwise @('nil').")
     (xdoc::p
      "A variable must be in the environment.")
     (xdoc::p
      "A shape consisting of dimensions is valid
       iff all the dimensions are valid.")
     (xdoc::p
      "A concatenation of shapes is valid
       iff all the shapes are valid.")
     (xdoc::p
      "A splicing of ispaces is valid
       iff all the ispaces are valid."))
    (shape-case
     shape
     :var (consp (omap::assoc (ispace-var-shape shape.name)
                              (senv->ispace-vars senv)))
     :dims (check-dim-list shape.dims senv)
     :append (check-shape-list shape.shapes senv)
     :splice (check-ispace-list shape.ispaces senv))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-shape-list ((shapes shape-listp) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-shapes/ispaces)
    :short "Check a list of shapes."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each shape in turn,
       returning @('t') iff they are all valid."))
    (or (endp shapes)
        (and (check-shape (car shapes) senv)
             (check-shape-list (cdr shapes) senv)))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-ispace ((ispace ispacep) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-shapes/ispaces)
    :short "Check an ispace."
    :long
    (xdoc::topstring
     (xdoc::p
      "An ispace that is a dimension is valid
       iff the dimension is valid.")
     (xdoc::p
      "An ispace that is a shape is valid
       iff the shape is valid."))
    (ispace-case
     ispace
     :dim (check-dim ispace.dim senv)
     :shape (check-shape ispace.shape senv))
    :measure (ispace-count ispace))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-ispace-list ((ispaces ispace-listp) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-shapes/ispaces)
    :short "Check a list of ispaces."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each ispace in turn,
       returning @('t') iff they are all valid."))
    (or (endp ispaces)
        (and (check-ispace (car ispaces) senv)
             (check-ispace-list (cdr ispaces) senv)))
    :measure (ispace-list-count ispaces))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (fty::deffixequiv-mutual check-shapes/ispaces))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type ((type typep) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-types)
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
     :var (consp (omap::assoc type.var (senv->type-vars senv)))
     :base t
     :array (and (check-type type.elem senv)
                 (type-atomp type.elem)
                 (check-ispace type.ispace senv))
     :bracket (and (check-type type.elem senv)
                   (type-atomp type.elem)
                   (check-ispace-list type.ispaces senv))
     :fun (and (check-type-list type.in senv)
               (check-type type.out senv))
     :forall (check-type type.body (senv-add-type-var type.param senv))
     :foralln (check-type type.body (senv-add-type-vars type.params senv))
     :pi (check-type type.body (senv-add-ispace-var type.param senv))
     :pin (check-type type.body (senv-add-ispace-vars type.params senv))
     :sigma (check-type type.body (senv-add-ispace-vars type.params senv)))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-type-list ((types type-listp) (senv senvp))
    :returns (yes/no booleanp)
    :parents (type-checking check-types)
    :short "Check a list of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each type in turn,
       returning @('t') iff they are all valid."))
    (or (endp types)
        (and (check-type (car types) senv)
             (check-type-list (cdr types) senv)))
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
  (b* (((unless (and (shape-addp shape)
                     (shape-addp suffix)))
        (reserr nil)) ; not supported
       (shape-elements (shape-append->shapes (normalize-shape shape)))
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
       ((unless (shape-list-addp shapes)) (reserr nil)) ; not supported
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
     :atom (if (type-atomp arg)
               (make-string-type-map-pair
                :1st (omap::update param.name arg maps.1st)
                :2nd maps.2nd)
             (reserr nil))
     :array (if (type-atomp arg)
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
     the @('ispace-vars') component of a static environment
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
     the @('type-vars') component of a static environment
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
      :atom (if (type-atomp type?.val)
                (change-string-type-map-pair
                 subst-rest
                 :1st (omap::update var.name type?.val subst-rest.1st))
              (prog2$ (raise "Internal error: ~
                              atom type variable ~x0 ~
                              is associated with ~
                              array-kind type ~x1."
                             var type?.val)
                      subst-rest))
      :array (if (type-atomp type?.val)
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

(define senv-expand-shape ((shape shapep) (senv senvp))
  :returns (new-shape shapep)
  :short "Expand a shape using the ispace definitions
          in the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the shape
     with its definition (see @(tsee senv-ispace-subst)).
     Since shapes contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (senv->ispace-vars senv))))
    (shape-subst-ispace-vars shape subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-ispace ((ispace ispacep) (senv senvp))
  :returns (new-ispace ispacep)
  :short "Expand an ispace using the ispace definitions
          in the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the ispace
     with its definition (see @(tsee senv-ispace-subst)).
     Since ispaces contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (senv->ispace-vars senv))))
    (ispace-subst-ispace-vars ispace subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection senv-expand-ispace-list ((x ispace-listp) (senv senvp))
  :returns (new-ispaces ispace-listp)
  :short "Lift @(tsee senv-expand-ispace) to lists of ispaces."
  (senv-expand-ispace x senv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type ((type typep) (senv senvp))
  :returns (new-type type-resultp)
  :short "Expand a type using the definitions in the static environment."
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
     Since the definitions in the static environment are fully expanded
     (i.e. they contain no defined variables),
     the result would be the same with the opposite order;
     but this order does not rely on
     the definitions in the static environment being fully expanded.")
   (xdoc::p
    "Because types contain binders (universal, product, and sum types),
     the substitution could result in variable capture;
     the capture-avoiding substitutions
     @(tsee type-subst-type-vars-alpha) and @(tsee type-subst-ispace-vars-alpha)
     automatically alpha-rename the bound variables as needed to avoid it."))
  (b* (((string-type-map-pair tsubst)
        (senv-type-subst (senv->type-vars senv)))
       (type (type-subst-type-vars-alpha type tsubst.1st tsubst.2nd))
       ((stringdimmap+stringshapemap isubst)
        (senv-ispace-subst (senv->ispace-vars senv))))
    (type-subst-ispace-vars-alpha type isubst.dim-map isubst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type-list ((types type-listp) (senv senvp))
  :returns (new-types type-list-resultp)
  :short "Lift @(tsee senv-expand-type) to lists."
  (b* (((when (endp types)) nil)
       ((ok type) (senv-expand-type (car types) senv))
       ((ok types) (senv-expand-type-list (cdr types) senv)))
    (cons type types))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-app ((fun-type typep) (arg-types type-listp))
  :returns (type type-resultp)
  :short "Check a term application,
          given the type of the function sub-expression
          and the types of the argument sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the function sub-expression
     must be an explicit array type of a function type,
     whose input and output types are all explicit array types.
     The atom input and output types
     are denoted @($\\tau\\ldots$) and @($\\tau'$),
     and their shapes are denoted @($\\iota\\ldots$) and @($\\iota'$),
     in [arxiv] and [thesis];
     our code uses
     @('in-atom-types'), @('out-atom-type'),
     @('in-shape'), and @('out-shape').
     The shape of the array type of the function expression
     is denoted @($\\iota_f$) in [arxiv] and [thesis];
     our code uses @('fun-shape').
     The argument types must all be array types,
     whose atom types must be equal to
     the input atom types of the function expression.
     The shapes of the argument types,
     for which our code uses @('arg-shapes'),
     are denoted @($(\\mathtt{++}\\ \\iota_a\\ \\iota)\\ldots$),
     which means that the shapes @($\\iota\\ldots$)
     of the corresponding inputs types must be suffixes,
     and that we need to extract the prefixes @($\\iota_a\\ldots$);
     we do that via @(tsee check-shape-suffixes) (see its documentation).
     Then we take the join of all those prefixes and the function shape
     (see documentation of @(tsee join-shapes)):
     that is the principal shape (ispace), in Remora's terminology,
     denoted @($\\iota_p$) in [arxiv] and [thesis].
     Finally we return the type of the term application expression,
     which is the array type consisting of
     the function output atom type
     and the concatenation of the principal shape
     with the function output shape."))
  (b* (((ok fun-type+ispace) (type-match-array fun-type))
       (fun-type (type+ispace->type fun-type+ispace))
       (fun-ispace (type+ispace->ispace fun-type+ispace))
       (fun-shape (shape-from-ispace fun-ispace))
       ((ok fun-types+type) (type-match-fun fun-type))
       (in-types (typelist+type->types fun-types+type))
       (out-type (typelist+type->type fun-types+type))
       ((ok in-types+ispaces) (type-list-match-array in-types))
       (in-atom-types (type+ispace-list->type in-types+ispaces))
       (in-ispaces (type+ispace-list->ispace in-types+ispaces))
       (in-shapes (shape-list-from-ispace-list in-ispaces))
       ((ok out-type+ispace) (type-match-array out-type))
       (out-atom-type (type+ispace->type out-type+ispace))
       (out-ispace (type+ispace->ispace out-type+ispace))
       (out-shape (shape-from-ispace out-ispace))
       ((ok arg-types+ispaces) (type-list-match-array arg-types))
       (arg-atom-types (type+ispace-list->type arg-types+ispaces))
       (arg-ispaces (type+ispace-list->ispace arg-types+ispaces))
       (arg-shapes (shape-list-from-ispace-list arg-ispaces))
       ((unless (type-list-equivp arg-atom-types in-atom-types))
        (reserr nil))
       ((ok prefix-shapes) (check-shape-suffixes arg-shapes in-shapes))
       ((ok principal-shape) (join-shapes (cons fun-shape prefix-shapes))))
    (make-type-array
     :elem out-atom-type
     :ispace (ispace-shape
              (shape-append (list principal-shape out-shape)))))
  :guard-hints
  (("Goal"
    :use (:instance same-len-when-type-list-equivp
                    (types1 (type+ispace-list->type
                             (type-list-match-array arg-types)))
                    (types2 (type+ispace-list->type
                             (type-list-match-array
                              (typelist+type->types
                               (type-match-fun
                                (type+ispace->type
                                 (type-match-array fun-type)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tapp ((fun-type typep) (arg typep) (senv senvp))
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
       ((unless (check-type arg senv)) (reserr nil))
       ((ok arg) (senv-expand-type arg senv))
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

(define check-tappn ((fun-type typep) (args type-listp) (senv senvp))
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
       ((ok type) (check-tapp fun-type (car args) senv)))
    (check-tappn type (cdr args) senv))
  :measure (len args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-iapp ((fun-type typep) (arg ispacep) (senv senvp))
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
       ((unless (check-ispace arg senv)) (reserr nil))
       (arg (senv-expand-ispace arg senv))
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

(define check-iappn ((fun-type typep) (args ispace-listp) (senv senvp))
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
       ((ok type) (check-iapp fun-type (car args) senv)))
    (check-iappn type (cdr args) senv))
  :measure (len args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-bind-type-annotation ((anno-type type-optionp)
                                    (expr-type typep)
                                    (senv senvp))
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
     once expanded against the static environment's definitions
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
   :some (b* (((unless (check-type anno-type.val senv)) nil)
              (anno-type (senv-expand-type anno-type.val senv))
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

(fty::defprod senv+bind
  :short "Fixtype of pairs consisting of
          a static environment and a binding."
  ((senv senv)
   (bind bind))
  :pred senv+bind-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult senv+bind-result
  :short "Fixtype of
          (i) pairs consisting of a static environment and a binding
          and (ii) errors."
  :ok senv+bind
  :pred senv+bind-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv+binds
  :short "Fixtype of pairs consisting of
          a static environment and a list of bindings."
  ((senv senv)
   (binds bind-list))
  :pred senv+binds-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult senv+binds-result
  :short "Fixtype of
          (i) pairs consisting of a static environment and a list of bindings
          and (ii) errors."
  :ok senv+binds
  :pred senv+binds-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory
  (enable type+expr-p-when-result-not-error
          types+exprs-p-when-result-not-error
          type+atom-p-when-result-not-error
          types+atoms-p-when-result-not-error
          senv+bind-p-when-result-not-error
          senv+binds-p-when-result-not-error)))

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
     with respect to the definitions in the static environment
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
     (or the static environment, in the case of bindings),
     each of these functions also returns
     the expression, atom, or binding being checked,
     possibly augmented with some type information."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr ((expr exprp) (senv senvp))
    :returns (type+expr type+expr-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check an expression; if successful,
            return its type and the type-augmented expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the static environment.")
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
      "For a term application,
       first we check the function and argument expressions,
       and then we use @(tsee check-app) to check
       the argument types against the function type,
       and to obtain the type of the application expression.")
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
       through @(tsee check-tappn), @(tsee check-iappn), and @(tsee check-app),
       in this order,
       skipping the type and ispace applications
       when the respective arguments are absent.")
     (xdoc::p
      "For an unboxing expression,
       first we check that the ispace variables have no duplicates;
       two variables with the same name but different sorts
       (one dimension and one shape) count as distinct.
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
       and we extend the static environment with that association.
       We check the body expression of the unboxing expression
       in the extended static environment;
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
       which extend the static environment (see @(tsee check-bind-list)),
       and then we check the body in the extended static environment."))
    (expr-case
     expr
     :var
     (b* ((name+type (omap::assoc expr.name (senv->expr-vars senv)))
          ((unless name+type) (reserr nil))
          ((ok type) (senv-expand-type (cdr name+type) senv)))
       (make-type+expr :type type :expr (expr-fix expr)))
     :atom
     (b* (((ok (type+atom ta)) (check-atom expr.atom senv)))
       (make-type+expr
        :type (make-type-array :elem ta.type
                               :ispace (ispace-shape (shape-dims nil)))
        :expr (make-expr-atom :atom ta.atom)))
     :array
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.atoms)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok (types+atoms tas)) (check-atom-list expr.atoms senv))
          ((unless (type-list-all-equivp tas.types)) (reserr nil))
          (type (car tas.types)))
       (make-type+expr
        :type (make-type-array :elem type
                               :ispace (ispace-shape
                                        (shape-dims (dim-const-list expr.dims))))
        :expr (make-expr-array :dims expr.dims :atoms tas.atoms)))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((unless (check-type expr.type senv)) (reserr nil))
          ((unless (type-atomp expr.type)) (reserr nil))
          ((ok elem) (senv-expand-type expr.type senv)))
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
          ((ok (types+exprs tes)) (check-expr-list expr.exprs senv))
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
          ((unless (check-type expr.type senv)) (reserr nil))
          ((ok type) (senv-expand-type expr.type senv))
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
     :app (reserr :todo)
     :appn
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          ((ok (types+exprs aes)) (check-expr-list expr.args senv))
          ((ok type) (check-app fe.type aes.types)))
       (make-type+expr :type type
                       :expr (make-expr-appn :fun fe.expr :args aes.exprs)))
     :tapp
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          ((ok type) (check-tapp fe.type expr.arg senv)))
       (make-type+expr :type type
                       :expr (make-expr-tapp :fun fe.expr :arg expr.arg)))
     :tappn
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          ((ok type) (check-tappn fe.type expr.args senv)))
       (make-type+expr :type type
                       :expr (make-expr-tappn :fun fe.expr :args expr.args)))
     :iapp
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          ((ok type) (check-iapp fe.type expr.arg senv)))
       (make-type+expr :type type
                       :expr (make-expr-iapp :fun fe.expr :arg expr.arg)))
     :iappn
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          ((ok type) (check-iappn fe.type expr.args senv)))
       (make-type+expr :type type
                       :expr (make-expr-iappn :fun fe.expr :args expr.args)))
     :capp
     (b* (((ok (type+expr fe)) (check-expr expr.fun senv))
          (fun-type fe.type)
          ((ok fun-type)
           (type-list-option-case
            expr.targs
            :some (check-tappn fun-type expr.targs.val senv)
            :none fun-type))
          ((ok fun-type)
           (ispace-list-option-case
            expr.iargs
            :some (check-iappn fun-type expr.iargs.val senv)
            :none fun-type))
          ((ok (types+exprs aes)) (check-expr-list expr.args senv))
          ((ok type) (check-app fun-type aes.types)))
       (make-type+expr
        :type type
        :expr (make-expr-capp :fun fe.expr
                              :targs expr.targs
                              :iargs expr.iargs
                              :args aes.exprs)))
     :unbox
     (b* (((unless (no-duplicatesp-equal expr.ispaces)) (reserr nil))
          ((ok (type+expr targ)) (check-expr expr.target senv))
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
          (senv (senv-add-ispace-vars expr.ispaces senv))
          (senv (senv-add-var+type expr.var sum-body-type-renam senv))
          ((ok (type+expr be)) (check-expr expr.body senv))
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
        :expr (make-expr-unbox :ispaces expr.ispaces
                               :var expr.var
                               :target targ.expr
                               :body be.expr
                               :type? type)))
     :bracket
     (b* (((unless (consp expr.exprs)) (reserr nil))
          ((ok (types+exprs es)) (check-expr-list expr.exprs senv))
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
     (b* (((ok (senv+binds sbs)) (check-bind-list expr.binds senv))
          ((ok (type+expr be)) (check-expr expr.body sbs.senv)))
       (make-type+expr :type be.type
                       :expr (make-expr-let :binds sbs.binds :body be.expr))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr-list ((exprs expr-listp) (senv senvp))
    :returns (types+exprs types+exprs-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check a list of expressions; if successful,
            return their types and the type-augmented expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the expressions."))
    (b* (((when (endp exprs))
          (make-types+exprs :types nil :exprs nil))
         ((ok (type+expr te)) (check-expr (car exprs) senv))
         ((ok (types+exprs tes)) (check-expr-list (cdr exprs) senv)))
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
      :hints (("Goal" :induct (len exprs) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom ((atom atomp) (senv senvp))
    :returns (type+atom type+atom-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check an atom; if successful,
            return its type and the type-augmented atom."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value
       is independent from the static environment,
       and determined via separate functions.")
     (xdoc::p
      "For a term abstraction,
       first we check that there are no duplicate bound variable names.
       We check that the types of the parameters are valid
       (see @(tsee check-type-list)).
       We extend the static environment with the bound variables,
       and we check the body of the abstraction
       in the extended static environment.
       Its type is the output type of the function type of the abstraction,
       and its input types are the ones of the bound variables.
       We store the body's type into the optional type slot of
       the returned lambda atom.")
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
      "For a boxing atom,
       the ispaces must be valid (see @(tsee check-ispace-list)),
       and the type that is part of its syntax must be a sum type.
       The type must be valid (see @(tsee check-type)).
       We check that the ispaces in the boxing atom have the same sorts
       as the bound variables of the sum type,
       obtaining a dimension substitution and a shape substitution.
       In the body type of the sum type,
       we apply those substitutions;
       the resulting type must be equivalent to
       the type of the body expression of the box.
       The type of the boxing atom is the sum type.
       The substitution avoids variable capture
       by automatically alpha-renaming bound variables as needed
       (see @(tsee type-subst-ispace-vars-alpha))."))
    (atom-case
     atom
     :base
     (make-type+atom
      :type (type-base (base-type-of-base-lit atom.lit))
      :atom (atom-fix atom))
     :lambda
     (b* (((unless (no-duplicatesp-equal (var+type?-list->var atom.params)))
           (reserr nil))
          ((ok types) (var+type?-list->type-list-or-err atom.params))
          ((unless (check-type-list types senv)) (reserr nil))
          ((ok types) (senv-expand-type-list types senv))
          ((ok senv) (senv-add-vars+types atom.params senv))
          ((ok (type+expr be)) (check-expr atom.body senv)))
       (make-type+atom
        :type (make-type-fun :in types :out be.type)
        :atom (make-atom-lambda :params atom.params
                                :body be.expr
                                :type? be.type)))
     :tlambda
     (b* ((senv (senv-add-type-var atom.param senv))
          ((ok (type+expr be)) (check-expr atom.body senv)))
       (make-type+atom
        :type (make-type-forall :param atom.param :body be.type)
        :atom (make-atom-tlambda :param atom.param :body be.expr)))
     :tlambdan
     (b* (((unless (no-duplicatesp-equal atom.params))
           (reserr nil))
          (senv (senv-add-type-vars atom.params senv))
          ((ok (type+expr be)) (check-expr atom.body senv)))
       (make-type+atom
        :type (make-type-foralln :params atom.params :body be.type)
        :atom (make-atom-tlambdan :params atom.params :body be.expr)))
     :ilambda
     (b* ((senv (senv-add-ispace-var atom.param senv))
          ((ok (type+expr be)) (check-expr atom.body senv)))
       (make-type+atom
        :type (make-type-pi :param atom.param :body be.type)
        :atom (make-atom-ilambda :param atom.param :body be.expr)))
     :ilambdan
     (b* (((unless (no-duplicatesp-equal atom.params))
           (reserr nil))
          (senv (senv-add-ispace-vars atom.params senv))
          ((ok (type+expr be)) (check-expr atom.body senv)))
       (make-type+atom
        :type (make-type-pin :params atom.params :body be.type)
        :atom (make-atom-ilambdan :params atom.params :body be.expr)))
     :box
     (b* (((unless (check-ispace-list atom.ispaces senv)) (reserr nil))
          (ispaces (senv-expand-ispace-list atom.ispaces senv))
          ((unless (type-atomp atom.type)) (reserr nil))
          ((unless (check-type atom.type senv)) (reserr nil))
          ((ok box-type) (senv-expand-type atom.type senv))
          ((ok vars+type) (type-match-sum box-type))
          (vars (ispacevarlist+type->vars vars+type))
          (body-type (ispacevarlist+type->type vars+type))
          ((ok (stringdimmap+stringshapemap maps))
           (check-ispace-params-and-args vars ispaces))
          (body-type-subst
           (type-subst-ispace-vars-alpha body-type
                                         maps.dim-map
                                         maps.shape-map))
          ((ok (type+expr ae)) (check-expr atom.array senv))
          ((unless (type-equivp ae.type body-type-subst)) (reserr nil)))
       (make-type+atom
        :type box-type
        :atom (make-atom-box :ispaces atom.ispaces
                             :array ae.expr
                             :type atom.type))))
    :measure (atom-count atom))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom-list ((atoms atom-listp) (senv senvp))
    :returns (types+atoms types+atoms-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check a list of atoms; if successful,
            return their types and the type-augmented atoms."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the atoms."))
    (b* (((when (endp atoms))
          (make-types+atoms :types nil :atoms nil))
         ((ok (type+atom ta)) (check-atom (car atoms) senv))
         ((ok (types+atoms tas)) (check-atom-list (cdr atoms) senv)))
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
      :hints (("Goal" :induct (len atoms) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-bind ((bind bindp) (senv senvp))
    :returns (senv+bind senv+bind-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check a binding; if successful,
            extend the static environment
            and return the type-augmented binding."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used for @('let') expressions; see @(tsee check-expr).
       If the binding is valid,
       we return the static environment extended according to the binding.")
     (xdoc::p
      "For a value binding,
       we check the bound expression, obtaining its type,
       and we extend the static environment
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
       and we extend the static environment
       to associate that function type to the bound variable.
       If the optional result type is present,
       we check that it is valid and equivalent to
       the type of the body of the abstraction.")
     (xdoc::p
      "A type function binding and an ispace function binding
       are treated similarly to a function binding,
       but as syntactic sugar for binding the variable
       to a type abstraction or an ispace abstraction,
       so their types are a universal type or a product type.")
     (xdoc::p
      "A combined function binding
       is syntactic sugar for binding the variable
       to a term abstraction,
       nested in an ispace abstraction if there are ispace parameters,
       nested in a type abstraction if there are type parameters;
       its type is the corresponding nesting of
       a function type, a product type, and a universal type.
       We check the body in the static environment
       extended with all the parameters,
       and we check that its type is equivalent to the declared result type.")
     (xdoc::p
      "For an ispace binding,
       we check that the bound ispace is valid,
       and that its sort matches the bound variable
       (a dimension variable is bound to a dimension,
       a shape variable is bound to a shape).
       We expand the ispace against the static environment's definitions
       (see @(tsee senv-expand-ispace)),
       so that the stored definition is itself fully expanded,
       and we extend the static environment
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
     (b* (((unless (check-ispace bind.ispace senv)) (reserr nil))
          ((unless (ispace-var-case
                    bind.var
                    :dim (ispace-case bind.ispace :dim)
                    :shape (ispace-case bind.ispace :shape)))
           (reserr nil))
          (ispace (senv-expand-ispace bind.ispace senv)))
       (make-senv+bind
        :senv (senv-add-ispace-def bind.var ispace senv)
        :bind (bind-fix bind)))
     :type
     (b* (((unless (check-type bind.type senv)) (reserr nil))
          ((unless (type-var-case
                    bind.var
                    :atom (type-atomp bind.type)
                    :array (not (type-atomp bind.type))))
           (reserr nil))
          ((ok type) (senv-expand-type bind.type senv)))
       (make-senv+bind
        :senv (senv-add-type-def bind.var type senv)
        :bind (bind-fix bind)))
     :val
     (b* (((ok (type+expr ee)) (check-expr bind.expr senv))
          ((unless (check-bind-type-annotation bind.type? ee.type senv))
           (reserr nil)))
       (make-senv+bind
        :senv (senv-add-var+type bind.var ee.type senv)
        :bind (make-bind-val :var bind.var
                             :type? bind.type?
                             :expr ee.expr)))
     :fun
     (b* (((unless (no-duplicatesp-equal (var+type?-list->var bind.params)))
           (reserr nil))
          ((ok types) (var+type?-list->type-list-or-err bind.params))
          ((unless (check-type-list types senv)) (reserr nil))
          ((ok senv-body) (senv-add-vars+types bind.params senv))
          ((ok (type+expr ee)) (check-expr bind.expr senv-body))
          ((unless (check-bind-type-annotation bind.type? ee.type senv))
           (reserr nil)))
       (make-senv+bind
        :senv (senv-add-var+type bind.var
                                 (make-type-array
                                  :elem (make-type-fun
                                         :in types
                                         :out ee.type)
                                  :ispace (ispace-shape (shape-dims nil)))
                                 senv)
        :bind (make-bind-fun :var bind.var
                             :params bind.params
                             :type? bind.type?
                             :expr ee.expr)))
     :tfun
     (b* (((unless (no-duplicatesp-equal bind.params)) (reserr nil))
          (senv-body (senv-add-type-vars bind.params senv))
          ((ok (type+expr ee)) (check-expr bind.expr senv-body))
          ((unless (check-bind-type-annotation bind.type? ee.type senv-body))
           (reserr nil)))
       (make-senv+bind
        :senv (senv-add-var+type bind.var
                                 (make-type-array
                                  :elem (make-type-foralln
                                         :params bind.params
                                         :body ee.type)
                                  :ispace (ispace-shape (shape-dims nil)))
                                 senv)
        :bind (make-bind-tfun :var bind.var
                              :params bind.params
                              :type? bind.type?
                              :expr ee.expr)))
     :ifun
     (b* (((unless (no-duplicatesp-equal bind.params)) (reserr nil))
          (senv-body (senv-add-ispace-vars bind.params senv))
          ((ok (type+expr ee)) (check-expr bind.expr senv-body))
          ((unless (check-bind-type-annotation bind.type? ee.type senv-body))
           (reserr nil)))
       (make-senv+bind
        :senv (senv-add-var+type bind.var
                                 (make-type-array
                                  :elem (make-type-pin
                                         :params bind.params
                                         :body ee.type)
                                  :ispace (ispace-shape (shape-dims nil)))
                                 senv)
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
          (senv-tparams (senv-add-type-vars tparams senv))
          (senv-iparams (senv-add-ispace-vars iparams senv-tparams))
          ((ok types) (var+type?-list->type-list-or-err bind.params))
          ((unless (check-type-list types senv-iparams)) (reserr nil))
          ((unless (check-type bind.type senv-iparams)) (reserr nil))
          ((ok btype) (senv-expand-type bind.type senv-iparams))
          ((ok senv-body) (senv-add-vars+types bind.params senv-iparams))
          ((ok (type+expr ee)) (check-expr bind.expr senv-body))
          ((unless (type-equivp ee.type btype)) (reserr nil))
          (fun-type (make-type-fun :in types :out btype))
          (fun-type (ispace-var-list-option-case
                     bind.iparams?
                     :some (make-type-pin :params bind.iparams?.val
                                          :body fun-type)
                     :none fun-type))
          (fun-type (type-var-list-option-case
                     bind.tparams?
                     :some (make-type-foralln :params bind.tparams?.val
                                              :body fun-type)
                     :none fun-type)))
       (make-senv+bind
        :senv (senv-add-var+type bind.var
                                 (make-type-array
                                  :elem fun-type
                                  :ispace (ispace-shape (shape-dims nil)))
                                 senv)
        :bind (make-bind-cfun :var bind.var
                              :tparams? bind.tparams?
                              :iparams? bind.iparams?
                              :params bind.params
                              :type bind.type
                              :expr ee.expr))))
    :measure (bind-count bind))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-bind-list ((binds bind-listp) (senv senvp))
    :returns (senv+binds senv+binds-resultp)
    :parents (type-checking check-exprs/atoms/binds)
    :short "Check a list of bindings; if successful,
            extend the static environment
            and return the type-augmented bindings."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check each binding in turn,
       threading through and extending the static environment as we go."))
    (b* (((when (endp binds))
          (make-senv+binds :senv (senv-fix senv) :binds nil))
         ((ok (senv+bind sb)) (check-bind (car binds) senv))
         ((ok (senv+binds sbs)) (check-bind-list (cdr binds) sb.senv)))
      (make-senv+binds :senv sbs.senv :binds (cons sb.bind sbs.binds)))
    :measure (bind-list-count binds))

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
    "We check the expression
     using the initial static environment.
     We return its type, together with the expression, if successful;
     the returned expression is currently identical to the input,
     as in @(tsee check-exprs/atoms/binds)."))
  (check-expr expr (init-senv)))
