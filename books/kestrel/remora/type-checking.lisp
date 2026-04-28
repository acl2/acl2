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
          atom-typep-when-result-not-error
          atom-type-listp-when-result-not-error
          array-typep-when-result-not-error
          array-type-listp-when-result-not-error
          stringstringmap-pairp-when-result-not-error
          atomtype+shape-p-when-result-not-error
          atomtype+shape-listp-when-result-not-error
          arraytypelist+arraytype-p-when-result-not-error
          ispacevarlist+arraytype-p-when-result-not-error
          typevarlist+arraytype-p-when-result-not-error
          stringdimmap+stringshapemap-p-when-result-not-error
          stringatomtypemap+stringarraytypemap-p-when-result-not-error)))

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
     in [arxiv] and [thesis].")
   (xdoc::p
    "This type checker is not designed for efficiency
     or to provide informative error messages.
     It is designed for simplicity."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-type-of-base-value ((bval base-valuep))
  :returns (btype base-typep)
  :short "Base type of a base value."
  (base-value-case
   bval
   :bool (base-type-bool)
   :int (base-type-int)
   :float (base-type-float)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-list-product ((nats nat-listp))
  :returns (product natp)
  :short "Product of a list of zero or more natural numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to calculate the number of elements of an array or frame.")
   (xdoc::p
    "This is 1 if the list is empty."))
  (cond ((endp nats) 1)
        (t (* (lnfix (car nats)) (nat-list-product (cdr nats)))))

  ///

  (defret zp-of-nat-list-product-iff-member-0
    (iff (zp product)
         (member-equal 0 (nat-list-fix nats)))
    :hints (("Goal" :induct t)))

  (defret nat-list-product-0-iff-member-0
    (iff (equal product 0)
         (member-equal 0 (nat-list-fix nats)))
    :hints (("Goal" :induct t))))

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
  (b* ((shape (normalize-shape shape))
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
  :returns (maps stringatomtypemap+stringarraytypemap-resultp)
  :short "Check whether a list of type parameters
          and a list of type arguments match."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same number of elements,
     and each parameter must have the same kind as the corresponding argument.
     If the check succeeds, we return two maps,
     one from the names of the atom type parameters
     to the corresponding atom type arguments,
     and one from the names of the array type parameters
     to the corresponding array type arguments."))
  (b* (((when (endp params))
        (if (endp args)
            (make-stringatomtypemap+stringarraytypemap
             :atom-map nil
             :array-map nil)
          (reserr nil)))
       ((when (endp args)) (reserr nil))
       ((ok (stringatomtypemap+stringarraytypemap maps))
        (check-type-params-and-args (cdr params) (cdr args)))
       (param (car params))
       (arg (car args)))
    (type-var-case
     param
     :atom (type-case
            arg
            :atom (make-stringatomtypemap+stringarraytypemap
                   :atom-map (omap::update param.name
                                           arg.type
                                           maps.atom-map)
                   :array-map maps.array-map)
            :array (reserr nil))
     :array (type-case
             arg
             :atom (reserr nil)
             :array (make-stringatomtypemap+stringarraytypemap
                     :atom-map maps.atom-map
                     :array-map (omap::update param.name
                                              arg.type
                                              maps.array-map)))))
  :verify-guards :after-returns)

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
    :returns (type array-type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an expression, returning its array type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the static environment.")
     (xdoc::p
      "For a (non-empty) array, there must be no zero dimension,
       and the number of atoms must match the product of the dimensions.
       We type-check all the atoms,
       which must have all equivalent atom types.
       We pick the first type from the list of types (which must be non-empty)
       as the atom type for the array type.
       We form a shape with the dimensions,
       and we return the array type.")
     (xdoc::p
      "For an empty array, there must be a 0 dimension.
       We form a shape with the dimensions,
       and we return the array type.")
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
       @($(x\\ k)\\ldots$) corresponds to @'kvars') in our code,
       @($\\tau_u$) corresponds to @('body-atom-type'),
       @($\\iota_u$) corresponds to @('body-type'),
       and @($\\iota_f$) corresponds to @('fun-type').
       We check all the type arguments
       (@($\\tau\\ldots$) in [arxiv] and [thesis]),
       ensuring that their kinds match the ones of
       the variables in the universal type.
       We form a substitution from the bound variables to the argument types,
       and we apply it to the body atom type
       to obtain the atom type of the resulting array type,
       whose type is obtained by concatenating
       the function type to the body type.")
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
       We check all the shape arguments
       (@($\\iota\\ldots$) in [arxiv] and [thesis]),
       ensuring that their sorts match the ones of
       the bound variables in the product type.
       We obtain two ispace maps (for dimensions and shapes),
       which we substitute to the body atom type
       to obtain the atom type of the resulting array type,
       whose shape is obtained by concatenating
       the function shape to
       the result of applying the same substitution to the body shape.")
     (xdoc::p
      "For an unboxing expression,
       first we check that the ispace variables have no duplicate names.
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
     :array
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.atoms)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-atom-list expr.atoms senv))
          ((unless (atom-type-list-all-equivp types)) (reserr nil))
          (type (car types)))
       (make-array-type-array :type type
                              :shape (shape-dims (dim-const-list expr.dims))))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil)))
       (make-array-type-array :type expr.type
                              :shape (shape-dims (dim-const-list expr.dims))))
     :frame
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.exprs)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-expr-list expr.exprs senv))
          ((unless (array-type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok (atomtype+shape array)) (array-type-match-array type)))
       (make-array-type-array
        :type array.type
        :shape (shape-append (list (shape-dims (dim-const-list expr.dims))
                                   array.shape))))
     :frame-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((ok (atomtype+shape array)) (array-type-match-array expr.type)))
       (make-array-type-array
        :type array.type
        :shape (shape-append (list (shape-dims (dim-const-list expr.dims))
                                   array.shape))))
     :term-app
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (array-type-match-array fun-arr-type))
          (fun-type (atomtype+shape->type fun-arr-type+shape))
          (fun-shape (atomtype+shape->shape fun-arr-type+shape))
          ((ok fun-types+type) (atom-type-match-fun fun-type))
          (in-types (arraytypelist+arraytype->types fun-types+type))
          (out-type (arraytypelist+arraytype->type fun-types+type))
          ((ok in-types+shapes) (array-type-list-match-array in-types))
          (in-atom-types (atomtype+shape-list->type in-types+shapes))
          (in-shapes (atomtype+shape-list->shape in-types+shapes))
          ((ok out-type+shape) (array-type-match-array out-type))
          (out-atom-type (atomtype+shape->type out-type+shape))
          (out-shape (atomtype+shape->shape out-type+shape))
          ((ok arg-types) (check-expr-list expr.args senv))
          ((ok arg-types+shapes) (array-type-list-match-array arg-types))
          (arg-atom-types (atomtype+shape-list->type arg-types+shapes))
          (arg-shapes (atomtype+shape-list->shape arg-types+shapes))
          ((unless (atom-type-list-equivp arg-atom-types in-atom-types))
           (reserr nil))
          ((ok prefix-shapes) (check-shape-suffixes arg-shapes in-shapes))
          ((ok principal-shape) (join-shapes (cons fun-shape prefix-shapes))))
       (make-array-type-array
        :type out-atom-type
        :shape (shape-append (list principal-shape out-shape))))
     :type-app
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (array-type-match-array fun-arr-type))
          (fun-type (atomtype+shape->type fun-arr-type+shape))
          (fun-shape (atomtype+shape->shape fun-arr-type+shape))
          ((ok fun-vars+type) (atom-type-match-forall fun-type))
          (vars (typevarlist+arraytype->vars fun-vars+type))
          (body-arr-type (typevarlist+arraytype->type fun-vars+type))
          ((ok body-type+shape) (array-type-match-array body-arr-type))
          (body-atom-type (atomtype+shape->type body-type+shape))
          (body-shape (atomtype+shape->shape body-type+shape))
          ((ok (stringatomtypemap+stringarraytypemap type-maps))
           (check-type-params-and-args vars expr.args))
          (body-atom-type-subst
           (atom-type-subst-type-vars body-atom-type
                                      type-maps.atom-map
                                      type-maps.array-map)))
       (make-array-type-array
        :type body-atom-type-subst
        :shape (shape-append (list fun-shape body-shape))))
     :ispace-app
     (b* (((ok fun-arr-type) (check-expr expr.fun senv))
          ((ok fun-arr-type+shape) (array-type-match-array fun-arr-type))
          (fun-type (atomtype+shape->type fun-arr-type+shape))
          (fun-shape (atomtype+shape->shape fun-arr-type+shape))
          ((ok fun-vars+type) (atom-type-match-product fun-type))
          (vars (ispacevarlist+arraytype->vars fun-vars+type))
          (body-arr-type (ispacevarlist+arraytype->type fun-vars+type))
          ((ok body-type+shape) (array-type-match-array body-arr-type))
          (body-atom-type (atomtype+shape->type body-type+shape))
          (body-shape (atomtype+shape->shape body-type+shape))
          ((ok (stringdimmap+stringshapemap ispace-maps))
           (check-ispace-params-and-args vars expr.args))
          (body-atom-type-subst
           (atom-type-subst-ispace-vars body-atom-type
                                        ispace-maps.dim-map
                                        ispace-maps.shape-map))
          (body-shape-subst (shape-subst-ispace-vars body-shape
                                                     ispace-maps.dim-map
                                                     ispace-maps.shape-map)))
       (make-array-type-array
        :type body-atom-type-subst
        :shape (shape-append (list fun-shape body-shape-subst))))
     :unbox
     (b* (((unless (no-duplicatesp-equal (ispace-var-list->name expr.ispaces)))
           (reserr nil))
          ((ok target-arr-type) (check-expr expr.target senv))
          ((ok target-arr-type+shape) (array-type-match-array target-arr-type))
          (sum-type (atomtype+shape->type target-arr-type+shape))
          (sum-shape (atomtype+shape->shape target-arr-type+shape))
          ((ok sum-vars+type) (atom-type-match-sum sum-type))
          (sum-vars (ispacevarlist+arraytype->vars sum-vars+type))
          (sum-body-type (ispacevarlist+arraytype->type sum-vars+type))
          ((unless (= (len expr.ispaces) (len sum-vars))) (reserr nil))
          ((ok (stringstringmap-pair renaming))
           (check-ispace-var-renaming sum-vars expr.ispaces))
          (sum-body-type-renam
           (array-type-rename-ispace-vars sum-body-type
                                          renaming.1st
                                          renaming.2nd))
          (senv (senv-add-var+type expr.var sum-body-type-renam senv))
          ((ok arr-type) (check-expr expr.body senv))
          ((ok arr-type+shape) (array-type-match-array arr-type))
          (body-atom-type (atomtype+shape->type arr-type+shape))
          (body-shape (atomtype+shape->shape arr-type+shape)))
       (make-array-type-array :type body-atom-type
                              :shape (shape-append (list sum-shape body-shape)))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expr-list ((exprs expr-listp) (senv senvp))
    :returns (types array-type-list-resultp)
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
    :returns (type atom-type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an atom, returning its atom type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value
       is independent from the static environment(s),
       and determined via separate functions.")
     (xdoc::p
      "For a term abstraction,
       first we check that there are no duplicate bound variable names.
       We check all the types of the bound variables,
       which must all have the array kind.
       We extend the static environment with the bound variables,
       and we check the body of the abstraction
       in the extended static environment.
       Its type is the output type of the function type of the abstraction,
       and its input types are the ones of the bound variables.")
     (xdoc::p
      "For a type abstraction,
       first we check that there are no duplicate bound variable names.
       We check the body of the abstraction in the extended enviroment.
       The resulting type is the body of the universal type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For an ispace abstraction,
       first we check that there are no duplicate bound variable names.
       We check the body of the abstraction.
       The resulting type is the body of the product type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For a boxing atom,
       the type that is part of its syntax must be a sum type
       and must be successfully checked to have the atom kind.
       We check that the ispaces in the boxing atom have the same sorts
       as the bound variables of the sum type,
       obtaining a dimension substitution and a shape substitution.
       In the body type of the sum type,
       we apply those substitutions;
       the resulting type must be equivalent to
       the type of the body expression of the box.
       The type of the boxing atom is the sum type."))
    (atom-case
     atom
     :base
     (atom-type-base (base-type-of-base-value atom.value))
     :term-abs
     (b* (((unless (no-duplicatesp-equal (var+type-list->var atom.params)))
           (reserr nil))
          (types (var+type-list->type atom.params))
          (senv (senv-add-vars+types atom.params senv))
          ((ok type) (check-expr atom.body senv)))
       (make-atom-type-fun :in types :out type))
     :type-abs
     (b* (((unless (no-duplicatesp-equal (type-var-list->name atom.params)))
           (reserr nil))
          ((ok type) (check-expr atom.body senv)))
       (make-atom-type-forall :params atom.params :type type))
     :ispace-abs
     (b* (((unless (no-duplicatesp-equal (ispace-var-list->name atom.params)))
           (reserr nil))
          ((ok type) (check-expr atom.body senv)))
       (make-atom-type-pi :params atom.params :type type))
     :box
     (b* (((unless (type-case atom.type :atom)) (reserr nil))
          (box-type (type-atom->type atom.type))
          ((ok vars+type) (atom-type-match-sum box-type))
          (vars (ispacevarlist+arraytype->vars vars+type))
          (body-type (ispacevarlist+arraytype->type vars+type))
          ((ok (stringdimmap+stringshapemap maps))
           (check-ispace-params-and-args vars atom.ispaces))
          (body-type-subst
           (array-type-subst-ispace-vars body-type
                                         maps.dim-map
                                         maps.shape-map))
          ((ok type) (check-expr atom.array senv))
          ((unless (array-type-equivp type body-type-subst)) (reserr nil)))
       box-type))
    :measure (atom-count atom))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-atom-list ((atoms atom-listp) (senv senvp))
    :returns (types atom-type-list-resultp)
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
                        (array-type-list-match-array
                         (check-expr-list exprs senv))))
                  (not (reserrp (array-type-list-match-array x)))
                  (atom-type-list-equivp
                   (atomtype+shape-list->type
                    (array-type-list-match-array
                     (check-expr-list exprs senv)))
                   (atomtype+shape-list->type
                    (array-type-list-match-array x))))
             (equal (len x)
                    (len exprs)))
    :use ((:instance same-len-when-atom-type-list-equivp
                     (types1 (atomtype+shape-list->type
                              (array-type-list-match-array
                               (check-expr-list exprs senv))))
                     (types2 (atomtype+shape-list->type
                              (array-type-list-match-array x))))))

  (verify-guards check-expr)

  (fty::deffixequiv-mutual check-exprs/atoms))
