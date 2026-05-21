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
(include-book "abstract-syntax-structural-operations")
(include-book "abstract-syntax-matching-operations")
(include-book "abstract-syntax-variable-operations")
(include-book "type-equivalence")
(include-book "static-environments")
(include-book "nat-list-operations")

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
          type+shape-p-when-result-not-error
          type+shape-listp-when-result-not-error
          typelist+type-p-when-result-not-error
          ispacevarlist+type-p-when-result-not-error
          typevarlist+type-p-when-result-not-error
          stringdimmap+stringshapemap-p-when-result-not-error
          string-type-mapp-when-result-not-error
          string-type-map-pairp-when-result-not-error)))

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
     It is designed for simplicity.")
   (xdoc::p
    "Not all expressions are currently covered;
     uncovered expressions return a @(':todo') error."))
  :order-subtopics t
  :default-parent t)

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
  :returns (prefix shape-resultp)
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
     We check whether the second list is a suffix of the first list.
     If the prefix is a singleton list, we return its element."))
  (b* (((unless (and (shape-addp shape)
                     (shape-addp suffix)))
        (reserr nil)) ; not supported
       (shape (normalize-shape shape))
       (suffix (normalize-shape suffix))
       ((unless (shape-case shape :append))
        (raise "Internal error: normalized shape is ~x0." shape)
        (reserr nil))
       ((unless (shape-case suffix :append))
        (raise "Internal error: normalized shape is ~x0." suffix)
        (reserr nil))
       (shape-elements (shape-append->shapes shape))
       (suffix-elements (shape-append->shapes suffix))
       ((unless (<= (len suffix-elements) (len shape-elements))) (reserr nil))
       ((unless (equal suffix-elements
                       (nthcdr (- (len shape-elements)
                                  (len suffix-elements))
                               shape-elements)))
        (reserr nil))
       (prefix-elements (take (- (len shape-elements)
                                 (len suffix-elements))
                              shape-elements)))
    (if (and (consp prefix-elements)
             (endp (cdr prefix-elements)))
        (car prefix-elements)
      (shape-append prefix-elements)))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :prepwork
  ((defrulel returns-lemma1
     (implies (< 0 (- (len x) (len y)))
              (consp x)))
   (defrulel returns-lemma2
     (implies (<= 1 (len x))
              (consp x)))))

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
    "We go through the list in order,
     but the order of the list is irrelevant.
     If the list is empty, the result is the empty concatenation,
     which is the bottom of the partial order.
     If the list is a singleton, the result is its only element.
     If the list has two or more elements,
     we recursively calculate the join of the @(tsee cdr) of the list,
     then we normalize that and the @(tsee car) and compare them.
     If neither the @(tsee car) is a prefix of the join nor vice versa,
     it is an error, i.e. there is no join;
     otherwise the result is the longer concatenation."))
  (b* (((when (endp shapes)) (shape-append nil))
       ((when (endp (cdr shapes))) (shape-fix (car shapes)))
       ((ok cdr-shape) (join-shapes (cdr shapes)))
       ((unless (and (shape-addp cdr-shape)
                     (shape-addp (car shapes))))
        (reserr nil)) ; not supported
       (cdr-shape (normalize-shape cdr-shape))
       (car-shape (normalize-shape (car shapes)))
       ((unless (shape-case cdr-shape :append))
        (raise "Internal error: normalized shape is ~x0." cdr-shape)
        (reserr nil))
       ((unless (shape-case car-shape :append))
        (raise "Internal error: normalized shape is ~x0." car-shape)
        (reserr nil))
       (car-elements (shape-append->shapes car-shape))
       (cdr-elements (shape-append->shapes cdr-shape)))
    (cond ((prefixp car-elements cdr-elements) (shape-append cdr-elements))
          ((prefixp cdr-elements car-elements) (shape-append car-elements))
          (t (reserr nil))))
  :no-function nil
  :verify-guards :after-returns
  ///
  (fty::deffixequiv join-shapes
    :hints (("Goal" :induct t :in-theory (enable shape-list-fix)))))

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

(define ispace-vars-in-scope-p ((vars ispace-var-setp) (senv senvp))
  :returns (yes/no booleanp)
  :short "Check if the ispace variables in a set are all in scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when the variables are all in the static environment."))
  (set::subset (ispace-var-set-fix vars) (senv->ispace-vars senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-vars-in-scope-p ((vars type-var-setp) (senv senvp))
  :returns (yes/no booleanp)
  :short "Check if the type variables in a set are all in scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when the variables are all in the static environment."))
  (set::subset (type-var-set-fix vars) (senv->type-vars senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-exprs/atoms
  :short "Check expressions, atoms, and lists thereof."
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
     but we should formally prove all of this."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr ((expr exprp) (senv senvp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an expression, returning its type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the static environment.")
     (xdoc::p
      "An atom stands for an array of rank 0,
       i.e. with empty shape and the atom as the only element.")
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
       The type must have atom kind.
       We ensure that the ispace and type variables of the type are in scope.
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
      "For a term application,
       first we check the function expression,
       which must have an explicit array type of a function type,
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
       The argument expressions must all have array types,
       whose atom types must be equal to
       the input atom types of the function expression.
       The shapes of the argument expressions,
       for which our code uses @('arg-shapes'),
       are denoted @($(\\mathtt{++}\\ \\iota_a\\ \\iota)\\ldots$),
       which means that the shapes @($\\iota\\ldots$)
       of the corresponding inputs types must be suffixes,
       and that we need to extract the prefixes @($\\iota_a\\ldots$);
       we do that via a separate function (see its documentation).
       Then we take the join of all those prefixes and the function shape
       (see documentation of @(tsee join-shapes)):
       that is the principal shape (ispace), in Remora's terminology,
       denoted @($\\iota_p$) in [arxiv] and [thesis].
       Finally we return the type of the term application expression,
       which is the array type consisting of
       the function output atom type
       and the concatenation of the principal shape
       with the function output shape.")
     (xdoc::p
      "For a type application,
       first we check the function expression,
       which must have an array type of a universal type,
       whose body type is an explicit array type.
       In [arxiv] and [thesis],
       @($(x\\ k)\\ldots$) corresponds to @('vars') in our code,
       @($\\tau_u$) corresponds to @('body-atom-type'),
       @($\\iota_u$) corresponds to @('body-shape'),
       and @($\\iota_f$) corresponds to @('fun-shape').
       We check that
       all the free ispace and type variables of the type arguments
       are in scope.
       We check all the type arguments
       (@($\\tau\\ldots$) in [arxiv] and [thesis]),
       ensuring that their kinds match the ones of
       the variables in the universal type.
       We form a substitution from the bound variables to the argument types,
       and we apply it to the body atom type
       to obtain the atom type of the resulting array type,
       whose shape is obtained by concatenating
       the function shape to the body shape.
       We check that the substitution cannot result in variable capture:
       type checking fails if that check fails;
       we should instead rename the bound variables to avoid the capture.")
     (xdoc::p
      "For an ispace application,
       first we check the function expression,
       which must have an array type of a product type,
       whose body type is an explicit array type.
       In [arxiv] and [thesis],
       @($(x\\ \\gamma)\\ldots$) corresponds to @('vars') in our code,
       @($\\tau_p$) corresponds to @('body-atom-type'),
       @($\\iota_p$) corresponds to @('body-shape'),
       and @($\\iota_f$) corresponds to @('fun-shape').
       We check that
       all the free (ispace) variables in the ispace arguments are in scope.
       We check all the ispace arguments
       (@($\\iota\\ldots$) in [arxiv] and [thesis]),
       ensuring that their sorts match the ones of
       the bound variables in the product type.
       We obtain two ispace maps (for dimensions and shapes),
       which we substitute to the body atom type
       to obtain the atom type of the resulting array type,
       whose shape is obtained by concatenating
       the function shape to
       the result of applying the same substitution to the body shape.
       We check that the substitution cannot result in variable capture:
       type checking fails if that check fails;
       we should instead rename the bound variables to avoid the capture.")
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
       we rename the bound variables to the ispace variables:
       we associate the resulting type
       to the term variable of the unboxing expression,
       and we extend the static environment with that association.
       We check the body expression of the unboxing expression
       in the extended static environment;
       we must get an explicit array type.
       In [arxiv] and [thesis],
       the latter array has atom type @($\\tau_b$) and ispace @($\\iota_b$),
       which correspond to @('body-atom-type') and @('body-ispace') in our code.
       The type of the unboxing expression is the array type consisting of
       the @($\\tau_b$) type as atom
       and the concatenation of @($\\iota_s$) and @($\\iota_b$) as ispace."))
    (expr-case
     expr
     :var
     (b* ((name+type (omap::assoc expr.name (senv->expr-vars senv)))
          ((unless name+type) (reserr nil)))
       (cdr name+type))
     :atom
     (b* (((ok type) (check-atom expr.atom senv)))
       (make-type-array :elem type
                        :shape (shape-dims nil)))
     :array
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.atoms)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-atom-list expr.atoms senv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types)))
       (make-type-array :elem type
                        :shape (shape-dims (dim-const-list expr.dims))))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((unless (type-atomp expr.type)) (reserr nil))
          ((unless (and (ispace-vars-in-scope-p
                         (type-free-ispace-vars expr.type) senv)
                        (type-vars-in-scope-p
                         (type-free-type-vars expr.type) senv)))
           (reserr nil)))
       (make-type-array :elem expr.type
                        :shape (shape-dims (dim-const-list expr.dims))))
     :frame
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.exprs)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-expr-list expr.exprs senv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok (type+shape array)) (type-match-array type)))
       (make-type-array
        :elem array.type
        :shape (shape-append (list (shape-dims (dim-const-list expr.dims))
                                   array.shape))))
     :frame-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((unless (and (ispace-vars-in-scope-p
                         (type-free-ispace-vars expr.type) senv)
                        (type-vars-in-scope-p
                         (type-free-type-vars expr.type) senv)))
           (reserr nil))
          ((ok (type+shape array)) (type-match-array expr.type)))
       (make-type-array
        :elem array.type
        :shape (shape-append (list (shape-dims (dim-const-list expr.dims))
                                   array.shape))))
     :string (reserr :todo)
     :app
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (type-match-array fun-arr-type))
          (fun-type (type+shape->type fun-arr-type+shape))
          (fun-shape (type+shape->shape fun-arr-type+shape))
          ((ok fun-types+type) (type-match-fun fun-type))
          (in-types (typelist+type->types fun-types+type))
          (out-type (typelist+type->type fun-types+type))
          ((ok in-types+shapes) (type-list-match-array in-types))
          (in-atom-types (type+shape-list->type in-types+shapes))
          (in-shapes (type+shape-list->shape in-types+shapes))
          ((ok out-type+shape) (type-match-array out-type))
          (out-atom-type (type+shape->type out-type+shape))
          (out-shape (type+shape->shape out-type+shape))
          ((ok arg-types) (check-expr-list expr.args senv))
          ((ok arg-types+shapes) (type-list-match-array arg-types))
          (arg-atom-types (type+shape-list->type arg-types+shapes))
          (arg-shapes (type+shape-list->shape arg-types+shapes))
          ((unless (type-list-equivp arg-atom-types in-atom-types))
           (reserr nil))
          ((ok prefix-shapes) (check-shape-suffixes arg-shapes in-shapes))
          ((ok principal-shape) (join-shapes (cons fun-shape prefix-shapes))))
       (make-type-array
        :elem out-atom-type
        :shape (shape-append (list principal-shape out-shape))))
     :tapp
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (type-match-array fun-arr-type))
          (fun-type (type+shape->type fun-arr-type+shape))
          (fun-shape (type+shape->shape fun-arr-type+shape))
          ((ok fun-vars+type) (type-match-forall fun-type))
          (vars (typevarlist+type->vars fun-vars+type))
          (body-arr-type (typevarlist+type->type fun-vars+type))
          ((ok body-type+shape) (type-match-array body-arr-type))
          (body-atom-type (type+shape->type body-type+shape))
          (body-shape (type+shape->shape body-type+shape))
          ((unless (and (ispace-vars-in-scope-p
                         (type-list-free-ispace-vars expr.args) senv)
                        (type-vars-in-scope-p
                         (type-list-free-type-vars expr.args) senv)))
           (reserr nil))
          ((ok (string-type-map-pair type-maps))
           (check-type-params-and-args vars expr.args))
          ((unless (type-subst-type-vars-no-capture-p body-atom-type
                                                      type-maps.1st
                                                      type-maps.2nd))
           (reserr nil))
          (body-atom-type-subst
           (type-subst-type-vars body-atom-type
                                 type-maps.1st
                                 type-maps.2nd)))
       (make-type-array
        :elem body-atom-type-subst
        :shape (shape-append (list fun-shape body-shape))))
     :iapp
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (type-match-array fun-arr-type))
          (fun-type (type+shape->type fun-arr-type+shape))
          (fun-shape (type+shape->shape fun-arr-type+shape))
          ((ok fun-vars+type) (type-match-product fun-type))
          (vars (ispacevarlist+type->vars fun-vars+type))
          (body-arr-type (ispacevarlist+type->type fun-vars+type))
          ((ok body-type+shape) (type-match-array body-arr-type))
          (body-atom-type (type+shape->type body-type+shape))
          (body-shape (type+shape->shape body-type+shape))
          ((unless (ispace-vars-in-scope-p
                    (ispace-list-free-ispace-vars expr.args) senv))
           (reserr nil))
          ((ok (stringdimmap+stringshapemap ispace-maps))
           (check-ispace-params-and-args vars expr.args))
          ((unless (type-subst-ispace-vars-no-capture-p body-atom-type
                                                        ispace-maps.dim-map
                                                        ispace-maps.shape-map))
           (reserr nil))
          (body-atom-type-subst
           (type-subst-ispace-vars body-atom-type
                                   ispace-maps.dim-map
                                   ispace-maps.shape-map))
          (body-shape-subst (shape-subst-ispace-vars body-shape
                                                     ispace-maps.dim-map
                                                     ispace-maps.shape-map)))
       (make-type-array
        :elem body-atom-type-subst
        :shape (shape-append (list fun-shape body-shape-subst))))
     :capp (reserr :todo)
     :unbox
     (b* (((unless (no-duplicatesp-equal expr.ispaces))
           (reserr nil))
          ((ok target-arr-type) (check-expr expr.target senv))
          ((ok target-arr-type+shape) (type-match-array target-arr-type))
          (sum-type (type+shape->type target-arr-type+shape))
          (sum-shape (type+shape->shape target-arr-type+shape))
          ((ok sum-vars+type) (type-match-sum sum-type))
          (sum-vars (ispacevarlist+type->vars sum-vars+type))
          (sum-body-type (ispacevarlist+type->type sum-vars+type))
          ((unless (= (len expr.ispaces) (len sum-vars))) (reserr nil))
          ((ok (string-string-map-pair renaming))
           (check-ispace-var-renaming sum-vars expr.ispaces))
          ((unless (type-rename-ispace-vars-no-capture-p sum-body-type
                                                         renaming.1st
                                                         renaming.2nd))
           (reserr nil))
          (sum-body-type-renam
           (type-rename-ispace-vars sum-body-type
                                    renaming.1st
                                    renaming.2nd))
          (senv (senv-add-ispace-vars expr.ispaces senv))
          (senv (senv-add-var+type expr.var sum-body-type-renam senv))
          ((ok arr-type) (check-expr expr.body senv))
          ((ok arr-type+shape) (type-match-array arr-type))
          (body-atom-type (type+shape->type arr-type+shape))
          (body-shape (type+shape->shape arr-type+shape)))
       (make-type-array :elem body-atom-type
                        :shape (shape-append (list sum-shape body-shape))))
     :bracket (reserr :todo)
     :let (reserr :todo))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr-list ((exprs expr-listp) (senv senvp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of expressions,
            returning their array types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the expressions."))
    (b* (((when (endp exprs)) nil)
         ((ok type) (check-expr (car exprs) senv))
         ((ok types) (check-expr-list (cdr exprs) senv)))
      (cons type types))
    :measure (expr-list-count exprs)

    ///

    (more-returns
     (types true-listp
            :rule-classes (:rewrite :type-prescription)
            :hints (("Goal"
                     :induct (len exprs)
                     :in-theory (enable len fty::true-listp-when-reserrp)))))

    (defret len-of-check-expr-list
      (implies (not (reserrp types))
               (equal (len types) (len exprs)))
      :hints (("Goal" :induct (len exprs) :in-theory (enable len))))

    (defret check-expr-list-iff-not-zp-len-exprs
      (iff types (not (zp (len exprs))))
      :hints (("Goal" :induct (len exprs) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom ((atom atomp) (senv senvp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an atom, returning its atom type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value
       is independent from the static environment,
       and determined via separate functions.")
     (xdoc::p
      "For a term abstraction,
       first we check that there are no duplicate bound variable names.
       We check that
       all the ispace and type variables in the types of the parameters
       are in scope.
       We extend the static environment with the bound variables,
       and we check the body of the abstraction
       in the extended static environment.
       Its type is the output type of the function type of the abstraction,
       and its input types are the ones of the bound variables.")
     (xdoc::p
      "For a type abstraction,
       first we check that there are no duplicate bound variables;
       two variables with the same name but different kinds
       (one atom and one array) count as distinct.
       We check the body of the abstraction in the extended environment.
       The resulting type is the body of the universal type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For an ispace abstraction,
       first we check that there are no duplicate bound variables;
       two variables with the same name but different sorts
       (one dimension and one shape) count as distinct.
       We check the body of the abstraction.
       The resulting type is the body of the product type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For a boxing atom,
       the free (ispace) variables in the ispaces must be in scope,
       and the type that is part of its syntax must be a sum type.
       The free ispace and type variables of the type must be in scope.
       We check that the ispaces in the boxing atom have the same sorts
       as the bound variables of the sum type,
       obtaining a dimension substitution and a shape substitution.
       In the body type of the sum type,
       we apply those substitutions;
       the resulting type must be equivalent to
       the type of the body expression of the box.
       The type of the boxing atom is the sum type.
       We check that the substitution cannot result in variable capture:
       type checking fails if that check fails;
       we should instead rename the bound variables to avoid the capture."))
    (atom-case
     atom
     :base
     (type-base (base-type-of-base-lit atom.lit))
     :lambda
     (b* (((unless (no-duplicatesp-equal (var+type-list->var atom.params)))
           (reserr nil))
          (types (var+type-list->type atom.params))
          ((unless (and (ispace-vars-in-scope-p
                         (type-list-free-ispace-vars types) senv)
                        (type-vars-in-scope-p
                         (type-list-free-type-vars types) senv)))
           (reserr nil))
          (senv (senv-add-vars+types atom.params senv))
          ((ok type) (check-expr atom.body senv)))
       (make-type-fun :in types :out type))
     :tlambda
     (b* (((unless (no-duplicatesp-equal atom.params))
           (reserr nil))
          (senv (senv-add-type-vars atom.params senv))
          ((ok type) (check-expr atom.body senv)))
       (make-type-forall :params atom.params :body type))
     :ilambda
     (b* (((unless (no-duplicatesp-equal atom.params))
           (reserr nil))
          (senv (senv-add-ispace-vars atom.params senv))
          ((ok type) (check-expr atom.body senv)))
       (make-type-pi :params atom.params :body type))
     :box
     (b* (((unless (ispace-vars-in-scope-p
                    (ispace-list-free-ispace-vars atom.ispaces) senv))
           (reserr nil))
          ((unless (type-atomp atom.type)) (reserr nil))
          (box-type atom.type)
          ((unless (and (ispace-vars-in-scope-p
                         (type-free-ispace-vars box-type) senv)
                        (type-vars-in-scope-p
                         (type-free-type-vars box-type) senv)))
           (reserr nil))
          ((ok vars+type) (type-match-sum box-type))
          (vars (ispacevarlist+type->vars vars+type))
          (body-type (ispacevarlist+type->type vars+type))
          ((ok (stringdimmap+stringshapemap maps))
           (check-ispace-params-and-args vars atom.ispaces))
          ((unless (type-subst-ispace-vars-no-capture-p body-type
                                                        maps.dim-map
                                                        maps.shape-map))
           (reserr nil))
          (body-type-subst
           (type-subst-ispace-vars body-type
                                   maps.dim-map
                                   maps.shape-map))
          ((ok type) (check-expr atom.array senv))
          ((unless (type-equivp type body-type-subst)) (reserr nil)))
       box-type))
    :measure (atom-count atom))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom-list ((atoms atom-listp) (senv senvp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of atoms, returning their types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the atoms."))
    (b* (((when (endp atoms)) nil)
         ((ok type) (check-atom (car atoms) senv))
         ((ok types) (check-atom-list (cdr atoms) senv)))
      (cons type types))
    :measure (atom-list-count atoms)

    ///

    (more-returns
     (types true-listp
            :rule-classes (:rewrite :type-prescription)
            :hints (("Goal"
                     :induct (len atoms)
                     :in-theory (enable len fty::true-listp-when-reserrp)))))

    (defret len-of-check-atom-list
      (implies (not (reserrp types))
               (equal (len types) (len atoms)))
      :hints (("Goal" :induct (len atoms) :in-theory (enable len))))

    (defret check-atom-list-iff-not-zp-len-atoms
      (iff types (not (zp (len atoms))))
      :hints (("Goal" :induct (len atoms) :in-theory (enable len)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ///

  (defruledl len-lemma
    (implies (equal x y)
             (equal (len x) (len y))))

  (defrulel lemma
    (implies (and (not (reserrp (check-expr-list exprs senv)))
                  (not (reserrp
                        (type-list-match-array
                         (check-expr-list exprs senv))))
                  (not (reserrp (type-list-match-array x)))
                  (type-list-equivp
                   (type+shape-list->type
                    (type-list-match-array
                     (check-expr-list exprs senv)))
                   (type+shape-list->type
                    (type-list-match-array x))))
             (equal (len x)
                    (len exprs)))
    :use ((:instance same-len-when-type-list-equivp
                     (types1 (type+shape-list->type
                              (type-list-match-array
                               (check-expr-list exprs senv))))
                     (types2 (type+shape-list->type
                              (type-list-match-array x))))))

  (verify-guards check-expr)

  (fty::deffixequiv-mutual check-exprs/atoms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-program ((prog progp))
  :returns (type type-resultp)
  :short "Check a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check its expression,
     using the initial static environment.
     We return the type if successful."))
  (check-expr (prog->expr prog) (init-senv)))
