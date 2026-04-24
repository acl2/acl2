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

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/fix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory
  (enable
   kindp-when-kind-resultp-and-not-reserrp
   kind-listp-when-kind-list-resultp-and-not-reserrp
   typep-when-type-resultp-and-not-reserrp
   type-listp-when-type-list-resultp-and-not-reserrp
   type+shape-p-when-type+shape-resultp-and-not-reserrp
   type+shape-listp-when-type+shape-list-resultp-and-not-reserrp
   typelist+type-p-when-typelist+type-resultp-and-not-reserrp
   kindedvarlist+type-p-when-kindedvarlist+type-resultp-and-not-reserrp
   shapep-when-shape-resultp-and-not-reserrp
   shape-listp-when-shape-list-resultp-and-not-reserrp
   stringdimmap+stringshapemap-p-when-stringdimmap+stringshapemap-resultp-and-not-reserrp
   indexparamlist+type-p-when-indexparamlist+type-resultp-and-not-reserrp
   stringstringmap-pairp-when-stringstringmap-pair-resultp-and-not-reserrp)))

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
     It is designed for simplicity.")
   (xdoc::p
    "[arxiv], [thesis], and [esop] denote
     sort environments with @($\\Theta$),
     kind environments with @($\\Delta$), and
     type environments with @($\\Gamma$).
     Our code does not use sort environments;
     it uses @('kindenv') for kind environments,
     and @('typeenv') for type environments,
     which are maps from strings (for variable names)
     to the associated kinds and types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kinded-var-list-to-map ((kvars kinded-var-listp))
  :returns (map string-kind-mapp)
  :short "Turn a list of kinded variables into a map."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the map, with the associated kinds.
     If there are duplicate variables, the leftmost ones prevail.
     We should always call this function on
     lists of sorte varaibles without duplilcate names;
     perhaps we could have and verify a guard for that."))
  (b* (((when (endp kvars)) nil)
       ((kinded-var kvar) (car kvars))
       (map (kinded-var-list-to-map (cdr kvars))))
    (omap::update kvar.var kvar.kind map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typed-var-list-to-map ((tvars typed-var-listp))
  :returns (map string-type-mapp)
  :short "Turn a list of typed variables into a map."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the map, with the associated types.
     If there are duplicate variables, the leftmost ones prevail.
     We should always call this function on
     lists of sorte varaibles without duplilcate names;
     perhaps we could have and verify a guard for that."))
  (b* (((when (endp tvars)) nil)
       ((typed-var tvar) (car tvars))
       (map (typed-var-list-to-map (cdr tvars))))
    (omap::update tvar.var tvar.type map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  (define check-type ((type typep) (kindenv string-kind-mapp))
    :returns (kind kind-resultp)
    :parents (type-checking check-types)
    :short "Check a type, returning its kind if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the (type) environment.")
     (xdoc::p
      "A base type has the atom kind.")
     (xdoc::p
      "An array type has the array kind,
       provided that its inner type has the atom kind.")
     (xdoc::p
      "A function type has the atom kind,
       provided that its input and output types all have the array kind.")
     (xdoc::p
      "For a universal type,
       we ensure that there are no duplicate variables,
       we turn the kinded variables into an environment,
       and we use it to update the current kind environment;
       this may override existing mappings, which should be intended.
       Then we check the body of the universal type,
       ensuring that it has the array kind.
       The universal type has the atom kind.")
     (xdoc::p
      "For a product or sum type,
       we ensure that there are no duplicate variables.
       Then we check the body of the product or sum type,
       ensuring that it has the array kind.
       The product or sum type has the atom kind."))
    (b* ((kindenv (string-kind-map-fix kindenv)))
      (type-case
       type
       :var (b* ((name+kind (omap::assoc type.name kindenv))
                 ((unless name+kind) (reserr nil)))
              (cdr name+kind))
       :base (kind-atom)
       :array (b* (((ok kind) (check-type type.type kindenv))
                   ((unless (kind-case kind :atom)) (reserr nil)))
                (kind-array))
       :fun (b* (((ok kinds) (check-type-list type.in kindenv))
                 ((unless (kind-list-arrayp kinds)) (reserr nil))
                 ((ok kind) (check-type type.out kindenv))
                 ((unless (kind-case kind :array)) (reserr nil)))
              (kind-atom))
       :forall (b* ((vars (kinded-var-list->var type.vars))
                    ((unless (no-duplicatesp-equal vars)) (reserr nil))
                    (kindenv-addition (kinded-var-list-to-map type.vars))
                    (kindenv (omap::update* kindenv-addition kindenv))
                    ((ok kind) (check-type type.type kindenv))
                    ((unless (kind-case kind :array)) (reserr nil)))
                 (kind-atom))
       :pi (b* ((vars (index-param-list->name type.params))
                ((unless (no-duplicatesp-equal vars)) (reserr nil))
                ((ok kind) (check-type type.type kindenv))
                ((unless (kind-case kind :array)) (reserr nil)))
             (kind-atom))
       :sigma (b* ((vars (index-param-list->name type.params))
                   ((unless (no-duplicatesp-equal vars)) (reserr nil))
                   ((ok kind) (check-type type.type kindenv))
                   ((unless (kind-case kind :array)) (reserr nil)))
                (kind-atom))))
    :measure (type-count type))

  (define check-type-list ((types type-listp) (kindenv string-kind-mapp))
    :returns (kinds kind-list-resultp)
    :parents (type-checking check-types)
    :short "Check a list of types, returning their kinds if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The kinds are in the same order as the types."))
    (b* (((when (endp types)) nil)
         ((ok kind) (check-type (car types) kindenv))
         ((ok kinds) (check-type-list (cdr types) kindenv)))
      (cons kind kinds))
    :measure (type-list-count types)

    ///

    (defret len-of-check-type-list
      (implies (not (reserrp kinds))
               (equal (len kinds)
                      (len types)))
      :hints (("Goal" :induct (len types) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-type-of-base-value ((bval base-valuep))
  :returns (btype base-typep)
  :short "Base type of a base value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be extended and tweaked
     as we extend and tweak the base values and types,
     which the Remora publications do not pin down."))
  (base-value-case
   bval
   :bool (base-type-bool)
   :char (base-type-char)
   :int (base-type-int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-prim-op ((op prim-opp))
  :returns (type typep)
  :short "Type of a primitive operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the signature described in [arxiv] and [thesis].
     This can be extended and tweaked
     as we extend and tweak the primitive operations
     and the base values and types,
     which the Remora publications do not pin down.")
   (xdoc::p
    "[arxiv] and [thesis] exemplify the signature
     by giving the input and output types of @('+'),
     which we represent as @(':add').
     Those publications mention a @('Num') (i.e. numeric type).
     Given our current base types, we pick the integer type,
     for this and the other three arithmetic operations;
     they all have scalar ranks for inputs and outputs.")
   (xdoc::p
    "The types of @('append'), @('reduce'), and @('iota') are shown
     in Figure 2 of [arxiv] and in Figure 4.3 of [thesis].
     The figures elide the universal and product quantifiers,
     but we need to include them in our definition.")
   (xdoc::p
    "We use the readable constructors for Remora types
     defined in @(see abstract-syntax-constructors)."))
  (b* ((add/sub/mul/div-type (t-> ((tarray :int (shape))
                                   (tarray :int (shape)))
                                  (tarray :int (shape))))
       (append-type
        (tforall ("t" :atom)
                 (tpi ("$n" "$m" "@s")
                      (t-> ((tarray "t" (shape++ (shape "$m") "@s"))
                            (tarray "t" (shape++ (shape "$n") "@s")))
                           (tarray "t" (shape++ (shape (dim+ "$m" "$n"))
                                                "@s"))))))
       (reduce-type
        (tforall ("t" :atom)
                 (tpi ("@s" "$d")
                      (t-> ((tarray (t-> ((tarray "t" "@s")
                                          (tarray "t" "@s"))
                                         (tarray "t" "@s"))
                                    (shape))
                            (tarray "t" (shape++ (shape (dim+ 1 "$d")) "@s")))
                           (tarray "t" "@s")))))
       (iota-type
        (tpi ("$d")
             (t-> ((tarray :int (shape "$d")))
                  (tarray (tsigma ("@s") (tarray :int "@s")) (shape))))))
    (prim-op-case
     op
     :add add/sub/mul/div-type
     :sub add/sub/mul/div-type
     :mul add/sub/mul/div-type
     :div add/sub/mul/div-type
     :append append-type
     :reduce reduce-type
     :iota iota-type)))

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
     they use indices in general,
     but the indices are shapes,
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

(define check-index-params-and-args ((params index-param-listp)
                                     (args index-listp))
  :returns (maps stringdimmap+stringshapemap-resultp)
  :short "Check whether a list of index parameters and index arguments match."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same number of elements,
     and each parameter must have the same sort as the argument.
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
        (check-index-params-and-args (cdr params) (cdr args)))
       (param (car params))
       (arg (car args)))
    (index-param-case
     param
     :dim (index-case
           arg
           :dim (make-stringdimmap+stringshapemap
                 :dim-map (omap::update param.name
                                        arg.dim
                                        maps.dim-map)
                 :shape-map maps.shape-map)
           :shape (reserr nil))
     :shape (index-case
             arg
             :dim (reserr nil)
             :shape (make-stringdimmap+stringshapemap
                     :dim-map maps.dim-map
                     :shape-map (omap::update param.name
                                              arg.shape
                                              maps.shape-map)))))
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

  (define check-expr ((expr exprp)
                      (kindenv string-kind-mapp)
                      (typeenv string-type-mapp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an expression, returning its type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the type environment.")
     (xdoc::p
      "For a (non-empty) array, there must be no zero dimension,
       and the number of atoms must match the product of the dimensions.
       We type-check all the atoms,
       which must have all equivalent types, of the atom kind.
       We pick the first type from the list of types (which must be non-empty)
       as the atom type for the array type.
       We form a shape with the dimensions,
       and we return the array type.")
     (xdoc::p
      "For an empty array, there must be a 0 dimension.
       The type must have atom kind.
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
       but the type must be an array type,
       whose shape is concatenated after the frame's dimensions.")
     (xdoc::p
      "For a term application,
       first we check the function expression,
       which must have an array type of a function type,
       whose input and output types are all array types.
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
       that is the principal shape (index), in Remora's terminology,
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
       whose body type is an array type.
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
      "For an index application,
       first we check the function expression,
       which must have an array type of a product type,
       whose body type is an array type.
       In [arxiv] and [thesis],
       @($(x\\ \\gamma)\\ldots$) corresponds to @('params') in our code,
       @($\\tau_p$) corresponds to @('body-atom-type'),
       @($\\iota_p$) corresponds to @('body-shape'),
       and @($\\iota_f$) corresponds to @('fun-shape').
       We check all the shape arguments
       (@($\\iota\\ldots$) in [arxiv] and [thesis]),
       ensuring that their sorts match the ones of
       the bound variables in the product type.
       We obtain two index maps (for dimensions and shapes),
       which we substitute to the body atom type
       to obtain the atom type of the resulting array type,
       whose shape is obtained by concatenating
       the function shape to
       the result of applying the same substitution to the body shape.")
     (xdoc::p
      "For an unboxing expression,
       first we check that the index parameters have no duplicate names.
       We check the target expression,
       which must be an array type of a sum type.
       In [arxiv] and [thesis],
       @($\\iota_s$) corresponds to @('sum-shape') in our code,
       @($(x'\\ \\gamma)\\ldots$) corresponds to @('sum-params'),
       and @($\\tau_s$) corresponds to @('sum-body-type').
       The number of bound variables in the sum type must be the same as
       the number of the index variables in the unboxing expression.
       In the sum type body,
       we rename the bound variables to the index variables:
       we associate the resulting type
       to the term variable of the unboxing expression,
       and we extend the type environment with that association.
       We check the body expression of the unboxing expression
       in the extended environment;
       we must get an array type,
       which must have the array kind.
       In [arxiv] and [thesis],
       the latter array has atom type @($\\tau_b$) and index @($\\iota_b$),
       which correspond to @('body-atom-type') and @('body-index') in our code.
       The type of the unboxing expression is the array type consisting of
       the @($\\tau_b$) type as atom
       and the concatenation of @($\\iota_s$) and @($\\iota_b$) as index."))
    (expr-case
     expr
     :var
     (b* ((name+type (omap::assoc expr.name (string-type-map-fix typeenv)))
          ((unless name+type) (reserr nil)))
       (cdr name+type))
     :array
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.atoms)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-atom-list expr.atoms kindenv typeenv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok kind) (check-type type kindenv))
          ((unless (kind-case kind :atom)) (reserr nil)))
       (make-type-array :type type
                        :shape (shape-dims (dim-const-list expr.dims))))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((ok kind) (check-type expr.type kindenv))
          ((unless (kind-case kind :atom)) (reserr nil)))
       (make-type-array :type expr.type
                        :shape (shape-dims (dim-const-list expr.dims))))
     :frame
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.exprs)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-expr-list expr.exprs kindenv typeenv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok kind) (check-type type kindenv))
          ((unless (kind-case kind :array)) (reserr nil))
          ((ok (type+shape array)) (type-match-array type)))
       (make-type-array :type array.type
                        :shape (shape-append
                                (list (shape-dims (dim-const-list expr.dims))
                                      array.shape))))
     :frame-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((ok (type+shape array)) (type-match-array expr.type))
          ((ok kind) (check-type array.type kindenv))
          ((unless (kind-case kind :atom)) (reserr nil)))
       (make-type-array :type array.type
                        :shape (shape-append
                                (list (shape-dims (dim-const-list expr.dims))
                                      array.shape))))
     :term-app
     (b* (((ok fun-arr-type) (check-expr expr.fun kindenv typeenv))
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
          ((ok arg-types) (check-expr-list expr.args kindenv typeenv))
          ((ok arg-types+shapes) (type-list-match-array arg-types))
          (arg-atom-types (type+shape-list->type arg-types+shapes))
          (arg-shapes (type+shape-list->shape arg-types+shapes))
          ((unless (type-list-equivp arg-atom-types in-atom-types))
           (reserr nil))
          ((ok prefix-shapes) (check-shape-suffixes arg-shapes in-shapes))
          ((ok principal-shape) (join-shapes (cons fun-shape prefix-shapes))))
       (make-type-array :type out-atom-type
                        :shape (shape-append (list principal-shape out-shape))))
     :type-app
     (b* (((ok fun-arr-type) (check-expr expr.fun kindenv typeenv))
          ((ok fun-arr-type+shape) (type-match-array fun-arr-type))
          (fun-type (type+shape->type fun-arr-type+shape))
          (fun-shape (type+shape->shape fun-arr-type+shape))
          ((ok fun-vars+type) (type-match-forall fun-type))
          (kvars (kindedvarlist+type->vars fun-vars+type))
          (body-arr-type (kindedvarlist+type->type fun-vars+type))
          ((ok body-type+shape) (type-match-array body-arr-type))
          (body-atom-type (type+shape->type body-type+shape))
          (body-shape (type+shape->shape body-type+shape))
          ((ok kinds) (check-type-list expr.args kindenv))
          ((unless (equal kinds (kinded-var-list->kind kvars))) (reserr nil))
          (bound-vars (kinded-var-list->var kvars))
          (subst (omap::from-lists bound-vars expr.args)))
       (make-type-array
        :type (subst-free-type-vars-in-type body-atom-type subst)
        :shape (shape-append (list fun-shape body-shape))))
     :index-app
     (b* (((ok fun-arr-type) (check-expr expr.fun kindenv typeenv))
          ((ok fun-arr-type+shape) (type-match-array fun-arr-type))
          (fun-type (type+shape->type fun-arr-type+shape))
          (fun-shape (type+shape->shape fun-arr-type+shape))
          ((ok fun-params+type) (type-match-product fun-type))
          (params (indexparamlist+type->params fun-params+type))
          (body-arr-type (indexparamlist+type->type fun-params+type))
          ((ok body-type+shape) (type-match-array body-arr-type))
          (body-atom-type (type+shape->type body-type+shape))
          (body-shape (type+shape->shape body-type+shape))
          ((ok (stringdimmap+stringshapemap index-maps))
           (check-index-params-and-args params expr.args))
          (body-shape-subst (subst-vars-in-shape body-shape
                                                 index-maps.dim-map
                                                 index-maps.shape-map)))
       (make-type-array
        :type (subst-free-index-vars-in-type body-atom-type
                                             index-maps.dim-map
                                             index-maps.shape-map)
        :shape (shape-append (list fun-shape body-shape-subst))))
     :unbox
     (b* (((unless (no-duplicatesp-equal (index-param-list->name expr.indices)))
           (reserr nil))
          ((ok target-arr-type) (check-expr expr.target kindenv typeenv))
          ((ok target-arr-type+shape) (type-match-array target-arr-type))
          (sum-type (type+shape->type target-arr-type+shape))
          (sum-shape (type+shape->shape target-arr-type+shape))
          ((ok sum-params+type) (type-match-sum sum-type))
          (sum-params (indexparamlist+type->params sum-params+type))
          (sum-body-type (indexparamlist+type->type sum-params+type))
          ((unless (= (len expr.indices) (len sum-params))) (reserr nil))
          ((ok (stringstringmap-pair renaming))
           (check-index-param-renaming sum-params expr.indices))
          (sum-body-type-renam
           (rename-free-index-vars-in-type sum-body-type
                                           renaming.1st
                                           renaming.2nd))
          (typeenv (omap::update expr.var
                                 sum-body-type-renam
                                 (string-type-map-fix typeenv)))
          ((ok arr-type) (check-expr expr.body kindenv typeenv))
          ((ok arr-type+shape) (type-match-array arr-type))
          (body-atom-type (type+shape->type arr-type+shape))
          (body-shape (type+shape->shape arr-type+shape))
          ((ok kind) (check-type arr-type kindenv))
          ((unless (kind-case kind :array)) (reserr nil)))
       (make-type-array :type body-atom-type
                        :shape (shape-append (list sum-shape body-shape)))))
    :measure (expr-count expr))

  (define check-expr-list ((exprs expr-listp)
                           (kindenv string-kind-mapp)
                           (typeenv string-type-mapp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of expressions, returning their types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the expressions."))
    (b* (((when (endp exprs)) nil)
         ((ok type) (check-expr (car exprs) kindenv typeenv))
         ((ok types) (check-expr-list (cdr exprs) kindenv typeenv)))
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

  (define check-atom ((atom atomp)
                      (kindenv string-kind-mapp)
                      (typeenv string-type-mapp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an atom, returning its type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value or a primitive operator
       is independent from the environment(s),
       and determined via separate functions.")
     (xdoc::p
      "For a term abstraction,
       first we check that there are no duplicate bound variable names.
       We check all the types of the bound variables,
       which must all have the array kind.
       We extend the type environment with the bound variables,
       and we check the body of the abstraction in the extended environment.
       Its type is the output type of the function type of the abstraction,
       and its input types are the ones of the bound variables.")
     (xdoc::p
      "For a type abstraction,
       first we check that there are no duplicate bound variable names.
       We extend the kind environment with the bound variables,
       and we check the body of the abstraction in the extended enviroment.
       The resulting type is the body of the universal type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For an index abstraction,
       first we check that there are no duplicate bound variable names.
       We check the body of the abstraction.
       The resulting type is the body of the product type
       that is the type of the abstraction,
       whose bound variables are the same as the abstraction.")
     (xdoc::p
      "For a boxing atom,
       the type that is part of its syntax must be a sum type
       and must be successfully checked to have the atom kind.
       We check that the indices in the boxing atom have the same sorts
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
     (type-base (base-type-of-base-value atom.value))
     :op
     (type-of-prim-op atom.op)
     :term-abs
     (b* (((unless (no-duplicatesp-equal (typed-var-list->var atom.vars)))
           (reserr nil))
          (types (typed-var-list->type atom.vars))
          ((ok kinds) (check-type-list types kindenv))
          ((unless (kind-list-arrayp kinds)) (reserr nil))
          (typeenv-addition (typed-var-list-to-map atom.vars))
          (typeenv (omap::update* typeenv-addition
                                  (string-type-map-fix typeenv)))
          ((ok type) (check-expr atom.body kindenv typeenv)))
       (make-type-fun :in types :out type))
     :type-abs
     (b* (((unless (no-duplicatesp-equal (kinded-var-list->var atom.vars)))
           (reserr nil))
          (kindenv-addition (kinded-var-list-to-map atom.vars))
          (kindenv (omap::update* kindenv-addition
                                  (string-kind-map-fix kindenv)))
          ((ok type) (check-expr atom.body kindenv typeenv)))
       (make-type-forall :vars atom.vars :type type))
     :index-abs
     (b* (((unless (no-duplicatesp-equal (index-param-list->name atom.params)))
           (reserr nil))
          ((ok type) (check-expr atom.body kindenv typeenv)))
       (make-type-pi :params atom.params :type type))
     :box
     (b* (((ok params+type) (type-match-sum atom.type))
          (params (indexparamlist+type->params params+type))
          (body-type (indexparamlist+type->type params+type))
          ((ok kind) (check-type atom.type kindenv))
          ((unless (kind-case kind :atom)) (reserr nil))
          ((ok (stringdimmap+stringshapemap maps))
           (check-index-params-and-args params atom.indices))
          (body-type-subst
           (subst-free-index-vars-in-type body-type
                                          maps.dim-map
                                          maps.shape-map))
          ((ok type) (check-expr atom.array kindenv typeenv))
          ((unless (type-equivp type body-type-subst)) (reserr nil)))
       atom.type))
    :measure (atom-count atom))

  (define check-atom-list ((atoms atom-listp)
                           (kindenv string-kind-mapp)
                           (typeenv string-type-mapp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of atoms, returning their types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the atoms."))
    (b* (((when (endp atoms)) nil)
         ((ok type) (check-atom (car atoms) kindenv typeenv))
         ((ok types) (check-atom-list (cdr atoms) kindenv typeenv)))
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

  :verify-guards nil ; done below

  ///

  (defruledl len-lemma
    (implies (equal x y)
             (equal (len x) (len y))))

  (defrulel lemma1
    (implies (and (not (reserrp (check-type-list types kindenv)))
                  (equal (check-type-list types kindenv)
                         (kinded-var-list->kind x)))
             (equal (len x)
                    (len types)))
    :use ((:instance len-lemma
                     (x (check-type-list types kindenv))
                     (y (kinded-var-list->kind x)))
          len-of-check-type-list)
    :disable len-of-check-type-list)

  (defrulel lemma2
    (implies (and (not (reserrp
                        (check-expr-list exprs kindenv typeenv)))
                  (not (reserrp
                        (type-list-match-array
                         (check-expr-list exprs kindenv typeenv))))
                  (not (reserrp (type-list-match-array x)))
                  (type-list-equivp
                   (type+shape-list->type
                    (type-list-match-array
                     (check-expr-list exprs kindenv typeenv)))
                   (type+shape-list->type
                    (type-list-match-array x))))
             (equal (len x)
                    (len exprs)))
    :use ((:instance same-len-when-type-list-equivp
                     (types1 (type+shape-list->type
                              (type-list-match-array
                               (check-expr-list
                                exprs kindenv typeenv))))
                     (types2 (type+shape-list->type
                              (type-list-match-array x))))))

  (verify-guards check-expr)

  (fty::deffixequiv-mutual check-exprs/atoms))
