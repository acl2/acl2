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
(include-book "abstract-syntax-substitution-operations")
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
   sortp-when-sort-resultp-and-not-reserrp
   sort-listp-when-sort-list-resultp-and-not-reserrp
   kindp-when-kind-resultp-and-not-reserrp
   kind-listp-when-kind-list-resultp-and-not-reserrp
   indexp-when-index-resultp-and-not-reserrp
   index-listp-when-index-list-resultp-and-not-reserrp
   typep-when-type-resultp-and-not-reserrp
   type-listp-when-type-list-resultp-and-not-reserrp
   type+index-p-when-type+index-resultp-and-not-reserrp
   type+index-listp-when-type+index-list-resultp-and-not-reserrp
   typelist+type-p-when-typelist+type-resultp-and-not-reserrp
   sortedvarlist+type-p-when-sortedvarlist+type-resultp-and-not-reserrp
   kindedvarlist+type-p-when-kindedvarlist+type-resultp-and-not-reserrp)))

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
     in the arXiv paper and in the dissertation.")
   (xdoc::p
    "This type checker is not designed for efficiency
     or to provide informative error messages.
     It is designed for simplicity.")
   (xdoc::p
    "The papers and dissertation denote
     sort environments with @($\\Theta$),
     kind environments with @($\\Delta$), and
     type environments with @($\\Gamma$).
     Our code uses @('sortenv'), @('kindenv'), and @('typeenv'),
     which are maps from strings (for variable names)
     to the associated sorts, kinds, and types.")
   (xdoc::p
    "This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sorted-var-list-to-map ((svars sorted-var-listp))
  :returns (sortenv string-sort-mapp)
  :short "Turn a list of sorted variables into a map."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the map, with the associated sorts.
     If there are duplicate variables, the leftmost ones prevail.
     We should always call this function on
     lists of sorte varaibles without duplilcate names;
     perhaps we could have and verify a guard for that."))
  (b* (((when (endp svars)) nil)
       ((sorted-var svar) (car svars))
       (map (sorted-var-list-to-map (cdr svars))))
    (omap::update svar.var svar.sort map))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defines check-indices
  :short "Check indices and lists of indices."

  (define check-index ((index indexp) (sortenv string-sort-mapp))
    :returns (sort sort-resultp)
    :parents (type-checking check-indices)
    :short "Check an index, returning its sort if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the environment.")
     (xdoc::p
      "A constant is always a dimension.")
     (xdoc::p
      "A shape is a shape (i.e. has the shape sort),
       provided that its indices are all dimensions.")
     (xdoc::p
      "An addition is a dimension,
       provided that its indices are all dimensions.")
     (xdoc::p
      "A concatenation is a shape,
       provided that its indices are all shapes."))
    (b* ((sortenv (string-sort-map-fix sortenv)))
      (index-case
       index
       :var (b* ((name+sort (omap::assoc index.name sortenv))
                 ((unless name+sort) (reserr nil)))
              (cdr name+sort))
       :const (sort-dim)
       :shape (b* (((ok sorts) (check-index-list index.indices sortenv))
                   ((unless (sort-list-dimp sorts)) (reserr nil)))
                (sort-shape))
       :add (b* (((ok sorts) (check-index-list index.indices sortenv))
                 ((unless (sort-list-dimp sorts)) (reserr nil)))
              (sort-dim))
       :append (b* (((ok sorts) (check-index-list index.indices sortenv))
                    ((unless (sort-list-shapep sorts)) (reserr nil)))
                 (sort-shape))))
    :measure (index-count index))

  (define check-index-list ((indices index-listp) (sortenv string-sort-mapp))
    :returns (sorts sort-list-resultp)
    :parents (type-checking check-indices)
    :short "Check a list of indices, returning their sorts if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The sorts are in the same order as the indices."))
    (b* (((when (endp indices)) nil)
         ((ok sort) (check-index (car indices) sortenv))
         ((ok sorts) (check-index-list (cdr indices) sortenv)))
      (cons sort sorts))
    :measure (index-list-count indices)

    ///

    (defret len-of-check-index-list
      (implies (not (reserrp sorts))
               (equal (len sorts)
                      (len indices)))
      :hints (("Goal" :induct (len indices) :in-theory (enable len)))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  (define check-type ((type typep)
                      (sortenv string-sort-mapp)
                      (kindenv string-kind-mapp))
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
       provided that its inner type has the atom kind
       and its index has the shape sort.")
     (xdoc::p
      "A function type has the atom kind,
       provided that its input and output types all have the array kind.")
     (xdoc::p
      "For a universal type,
       we ensure that there are no duplicate variables,
       we turn the kinded variables into an environment,
       and we use it to update the current type environment;
       this may override existing mappings, which should be intended.
       Then we check the body of the universal type,
       ensuring that it has the array kind.
       The universal type has the atom kind.")
     (xdoc::p
      "For a product or sum type,
       we ensure that there are no duplicate variables,
       we turn the sorted variables into an environment,
       and we use it to update the current index environment;
       this may override existing mappings, which should be intended.
       Then we check the body of the product or sum type,
       ensuring that it has the array kind.
       The product or sum type has the atom kind."))
    (b* ((sortenv (string-sort-map-fix sortenv))
         (kindenv (string-kind-map-fix kindenv)))
      (type-case
       type
       :var (b* ((name+kind (omap::assoc type.name kindenv))
                 ((unless name+kind) (reserr nil)))
              (cdr name+kind))
       :base (kind-atom)
       :array (b* (((ok kind) (check-type type.type sortenv kindenv))
                   ((unless (kind-case kind :atom)) (reserr nil))
                   ((ok sort) (check-index type.index sortenv))
                   ((unless (sort-case sort :shape)) (reserr nil)))
                (kind-array))
       :fun (b* (((ok kinds) (check-type-list type.in sortenv kindenv))
                 ((unless (kind-list-arrayp kinds)) (reserr nil))
                 ((ok kind) (check-type type.out sortenv kindenv))
                 ((unless (kind-case kind :array)) (reserr nil)))
              (kind-atom))
       :forall (b* ((vars (kinded-var-list->var type.vars))
                    ((unless (no-duplicatesp-equal vars)) (reserr nil))
                    (kindenv-addition (kinded-var-list-to-map type.vars))
                    (kindenv (omap::update* kindenv-addition kindenv))
                    ((ok kind) (check-type type.type sortenv kindenv))
                    ((unless (kind-case kind :array)) (reserr nil)))
                 (kind-atom))
       :pi (b* ((vars (sorted-var-list->var type.vars))
                ((unless (no-duplicatesp-equal vars)) (reserr nil))
                (sortenv-addition (sorted-var-list-to-map type.vars))
                (sortenv (omap::update* sortenv-addition sortenv))
                ((ok kind) (check-type type.type sortenv kindenv))
                ((unless (kind-case kind :array)) (reserr nil)))
             (kind-atom))
       :sigma (b* ((vars (sorted-var-list->var type.vars))
                   ((unless (no-duplicatesp-equal vars)) (reserr nil))
                   (sortenv-addition (sorted-var-list-to-map type.vars))
                   (sortenv (omap::update* sortenv-addition sortenv))
                   ((ok kind) (check-type type.type sortenv kindenv))
                   ((unless (kind-case kind :array)) (reserr nil)))
                (kind-atom))))
    :measure (type-count type))

  (define check-type-list ((types type-listp)
                           (sortenv string-sort-mapp)
                           (kindenv string-kind-mapp))
    :returns (kinds kind-list-resultp)
    :parents (type-checking check-types)
    :short "Check a list of types, returning their kinds if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The kinds are in the same order as the types."))
    (b* (((when (endp types)) nil)
         ((ok kind) (check-type (car types) sortenv kindenv))
         ((ok kinds) (check-type-list (cdr types) sortenv kindenv)))
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
    "This corresponds to the signature described
     in the arXiv paper and in the dissertation.
     This can be extended and tweaked
     as we extend and tweak the primitive operations
     and the base values and types,
     which the Remora publications do not pin down.")
   (xdoc::p
    "The arXiv paper and the dissertation exemplify the signature
     by giving the input and output types of @('+'),
     which we represent as @(':add').
     Those publications mention a @('Num') (i.e. numeric type).
     Given our current base types, we pick the integer type,
     for this and the other three arithmetic operations;
     they all have scalar ranks for inputs and outputs.")
   (xdoc::p
    "The types of @('append'), @('reduce'), and @('iota') are shown
     in Figure 2 of the arXiv paper
     and in Figure 4.3 of the dissertation.
     The figures elide the universal and product quantifiers,
     but we need to include them in our definition.")
   (xdoc::p
    "We use the readable constructors for Remora types
     defined in @(see abstract-syntax-constructors)."))
  (b* ((add/sub/mul/div-type (t-> ((tarray :int (ishape))
                                   (tarray :int (ishape)))
                                  (tarray :int (ishape))))
       (append-type
        (tforall ("t" :atom)
                 (tpi ("n" :dim
                       "m" :dim
                       "s" :shape)
                      (t-> ((tarray "t" (i++ (ishape "m") "s"))
                            (tarray "t" (i++ (ishape "n") "s")))
                           (tarray "t" (i++ (ishape (i+ "m" "n")) "s"))))))
       (reduce-type
        (tforall ("t" :atom)
                 (tpi ("s" :shape
                       "d" :dim)
                      (t-> ((tarray (t-> ((tarray "t" "s")
                                          (tarray "t" "s"))
                                         (tarray "t" "s"))
                                    (ishape))
                            (tarray "t" (i++ (ishape (i+ 1 "d")) "s")))
                           (tarray "t" "s")))))
       (iota-type
        (tpi ("d" :dim)
             (t-> ((tarray :int (ishape "d")))
                  (tarray (tsigma ("s" :shape) (tarray :int "s")) (ishape))))))
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

(define check-index-suffix ((index indexp) (suffix indexp))
  :returns (prefix index-resultp)
  :short "Check if an index has another index as suffix,
          returning the prefix index if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for a term application: see @(tsee check-expr).
     Each of the indices of the input types of the function expression
     must be a suffix of the index of the type of
     the argument expression corresponding to the function input.
     In the arXiv paper and dissertation,
     the index of the argument is denoted
     @($(\\mathtt{++}\\ \\iota_a\\ \\iota)\\ldots$),
     and the index of the input is denoted @($\\iota$).
     This function takes the argument index as the formal @('index'),
     and the input type index as the formal @('suffix'),
     and returns @($\\iota_a$) if successful,
     which is the prefix.")
   (xdoc::p
    "To perform this check, we need to normalize both indices.
     Since these are indices of array types,
     they can only be variables,
     or shapes (of dimensions),
     or concatenations of the above;
     the concatenation is either empty or has two or more elements,
     because singleton concatenations are normalized to their element.")
   (xdoc::p
    "To facilitate comparison,
     we turn non-concatenations (i.e. variables and shapes)
     into singleton concatenations.
     In other words, we end up with two lists of indices,
     all of which are variables and (singleton) shapes,
     to compare for the second one being a suffix of the first one.
     If the prefix is a singleton list,
     we return the element, so that we keep the resulting prefix normalized.")
   (xdoc::p
    "This function works on all categories of indices,
     including those of the dimension sort,
     even though it is always called with indices of the shape sort.
     We may be able to explicate invariants
     that will rule out these dimension sorts;
     we will investigate that later."))
  (b* ((index (normalize-index index))
       (suffix (normalize-index suffix))
       (index-elements (index-case index
                                   :append index.indices
                                   :otherwise (list index)))
       (suffix-elements (index-case suffix
                                    :append suffix.indices
                                    :otherwise (list suffix)))
       ((unless (<= (len suffix-elements) (len index-elements))) (reserr nil))
       ((unless (equal suffix-elements
                       (nthcdr (- (len index-elements)
                                  (len suffix-elements))
                               index-elements)))
        (reserr nil))
       (prefix-elements (take (- (len index-elements)
                                 (len suffix-elements))
                              index-elements)))
    (if (and (consp prefix-elements)
             (endp (cdr prefix-elements)))
        (car prefix-elements)
      (index-append prefix-elements)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :prepwork
  ((defrule returns-lemma1
     (implies (< 0 (- (len x) (len y)))
              (consp x)))
   (defrule returns-lemma2
     (implies (<= 1 (len x))
              (consp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-index-suffixes ((indices index-listp) (suffixes index-listp))
  :guard (equal (len suffixes) (len indices))
  :returns (prefixes index-list-resultp)
  :short "Check if each index in a list has
          the corresponding index in a list as suffix,
          returning each prefix if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee check-index-suffix) to lists,
     which all have the same lengths (if successful)."))
  (b* (((when (endp indices)) nil)
       ((unless (mbt (consp suffixes))) (reserr nil))
       ((ok prefix) (check-index-suffix (car indices) (car suffixes)))
       ((ok prefixes) (check-index-suffixes (cdr indices) (cdr suffixes))))
    (cons prefix prefixes))

  ///

  (defret len-of-check-index-suffixes
    (implies (not (reserrp prefixes))
             (equal (len prefixes)
                    (len indices)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-indices ((indices index-listp))
  :returns (index index-resultp)
  :short "Calculate the least upper bound of a list of indices,
          with respect to prefix as partial order."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for a term application; see @(tsee check-expr).
     After having calculated all the prefixes @($\\iota_a\\ldots$),
     we need to calculate the join (i.e. least upper bound)
     of those indices and of the index @($\\iota_f$) of the function expression.
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
     To facilitate comparisons,
     we turn non-concatenations into singleton concatenations,
     so we just need to compare the elements of the concatenations.
     If neither the @(tsee car) is a prefix of the join nor vice versa,
     it is an error, i.e. there is no join;
     otherwise the result is the longer concatenation."))
  (b* (((when (endp indices)) (index-append nil))
       ((when (endp (cdr indices))) (index-fix (car indices)))
       ((ok cdr-index) (join-indices (cdr indices)))
       (cdr-index (normalize-index cdr-index))
       (car-index (normalize-index (car indices)))
       (car-elements (index-case car-index
                                 :append car-index.indices
                                 :otherwise (list car-index)))
       (cdr-elements (index-case cdr-index
                                 :append cdr-index.indices
                                 :otherwise (list cdr-index))))
    (cond ((prefixp car-elements cdr-elements) (index-append cdr-elements))
          ((prefixp cdr-elements car-elements) (index-append car-elements))
          (t (reserr nil))))
  :verify-guards :after-returns
  ///
  (fty::deffixequiv join-indices
    :hints (("Goal" :induct t :in-theory (enable index-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-exprs/atoms
  :short "Check expressions, atoms, and lists thereof."
  :long
  (xdoc::topstring
   (xdoc::p
    "Because of type equivalence,
     an expression or atom may not have a unique type,
     but rather a set of possible equivalent types.
     Our checking functions return a ``canonical'' type,
     based on the syntactic specifics of the expression or atom.
     Type equivalence is used to compare types,
     e.g. the type of an argument against the type of a parameter.
     This approach should be equivalent to the typing rules,
     which may assign multiple equivalent types to an expression or an atom;
     but we should formally prove all of this."))

  (define check-expr ((expr exprp)
                      (sortenv string-sort-mapp)
                      (kindenv string-kind-mapp)
                      (typeenv string-type-mapp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an expression, returning its type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "A variable is looked up in the (term) environment.")
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
       and the index of the resulting array type is
       the concatenation of the dimensions with
       the index of the array type of the expressions
       (we pick the first one).")
     (xdoc::p
      "An empty frame is similar to an empty array,
       but the type must be an array type
       with an atom type and with a shape index.
       The latter is concatenated after the frame's dimensions.")
     (xdoc::p
      "For a term application,
       first we check the function expression,
       which must have an array type of a function type,
       whose input and output types are all array types.
       The atom input and output types
       are denoted @($\\tau\\ldots$) and @($\\tau'$),
       and their indices are denoted @($\\iota\\ldots$) and @($\\iota'$),
       in the arXiv paper and dissertation;
       our code uses
       @('in-atom-types'), @('out-atom-type'),
       @('in-index'), and @('out-index').
       The index of the array type of the function expression
       is denoted @($\\iota_f$) in the paper and dissertation;
       our code uses @('fun-index').
       The argument expressions must all have array types,
       whose atom types must be equal to
       the input atom types of the function expression.
       The indices of the argument expressions,
       for which our code uses @('arg-indices'),
       are denoted @($(\\mathtt{++}\\ \\iota_a\\ \\iota)\\ldots$),
       which means that the indices @($\\iota\\ldots$)
       of the corresponding inputs types must be suffixes,
       and that we need to extract the prefixes @($\\iota_a\\ldots$);
       we do that via a separate function (see its documentation).
       Then we take the join of all those prefixes and the function index
       (see documentation of @(tsee join-indices):
       that is the principal index, in Remora's terminology,
       denoted @($\\iota_p$) in the paper and dissertation.
       Finally we return the type of the term application expression,
       which is the array type consisting of
       the function output atom type
       and the concatenation of the principal index
       with the function output index.")
     (xdoc::p
      "For a type application,
       first we check the function expression,
       which must have an array type of a universal type,
       whose body type is an array type.
       In the arXiv paper and dissertation,
       @($(x\\ k)\\ldots$) corresponds to @'kvars') in our code,
       @($\\tau_u$) corresponds to @('body-atom-type'),
       @($\\iota_u$) corresponds to @('body-index'),
       and @($\\iota_f$) corresponds to @('fun-index').
       We check all the type arguments
       (@($\\tau\\ldots$) in the paper and dissertation),
       ensuring that their kinds match the ones of
       the variables in the universal type.
       We form a substitution from the bound variables to the argument types,
       and we apply it to the body atom type
       to obtain the atom type of the resulting array type,
       whose index is obtained by concatenating
       the function index to the body index.")
     (xdoc::p
      "For an index application,
       first we check the function expression,
       which must have an array type of a product type,
       whose body type is an array type.
       In the arXiv paper and dissertation,
       @($(x\\ \\gamma)\\ldots$) corresponds to @'svars') in our code,
       @($\\tau_p$) corresponds to @('body-atom-type'),
       @($\\iota_p$) corresponds to @('body-index'),
       and @($\\iota_f$) corresponds to @('fun-index').
       We check all the index arguments
       (@($\\iota\\ldots$) in the paper and dissertation),
       ensuring that their sorts match the ones of
       the variables in the product type.
       We form a substitution from the bound variables to the argument indices,
       and we apply it to the body atom type
       to obtain the atom type of the resulting array type,
       whose index is obtained by concatenating
       the function index to
       the result of applying the same substitution to the body index.")
     (xdoc::p
      "For an unboxing expression,
       first we check the target expression,
       which must be an array type of a sum type.
       In the arXiv paper and dissertation,
       @($\\iota_s$) corresponds to @('sum-index') in our code,
       @($(x'\\ \\gamma)\\ldots$) corresponds to @('svars'),
       and @($\\tau_s$) corresponds to @('body-type').
       The number of bound variables must be the same as
       the number of the index variables in the unboxing expression.
       We extend the sort environment with the index variables
       associated to the sorts of the corresponding bound variables.
       In the sum type body,
       we rename the bound variables to the index variables:
       we associate the resulting type
       to the term variable of the unboxing expression,
       and we extend the type environment with that association.
       We check the body expression of the unboxing expression
       in the extended environment;
       we must get an array type,
       which must have the array kind.
       In the arXiv paper and dissertation,
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
          ((ok types) (check-atom-list expr.atoms sortenv kindenv typeenv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok kind) (check-type type sortenv kindenv))
          ((unless (kind-case kind :atom)) (reserr nil)))
       (make-type-array :type type
                        :index (index-shape (index-const-list expr.dims))))
     :array-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((ok kind) (check-type expr.type sortenv kindenv))
          ((unless (kind-case kind :atom)) (reserr nil)))
       (make-type-array :type expr.type
                        :index (index-shape (index-const-list expr.dims))))
     :frame
     (b* (((when (member-equal 0 expr.dims)) (reserr nil))
          ((unless (= (len expr.exprs)
                      (nat-list-product expr.dims)))
           (reserr nil))
          ((ok types) (check-expr-list expr.exprs sortenv kindenv typeenv))
          ((unless (type-list-all-equivp types)) (reserr nil))
          (type (car types))
          ((ok kind) (check-type type sortenv kindenv))
          ((unless (kind-case kind :array)) (reserr nil))
          ((ok (type+index array)) (type-match-array type)))
       (make-type-array :type array.type
                        :index (index-append
                                (list (index-shape (index-const-list expr.dims))
                                      array.index))))
     :frame-empty
     (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
          ((ok (type+index array)) (type-match-array expr.type))
          ((ok kind) (check-type array.type
                                 sortenv
                                 kindenv))
          ((unless (kind-case kind :atom)) (reserr nil))
          ((ok sort) (check-index array.index
                                  sortenv))
          ((unless (sort-case sort :shape)) (reserr nil)))
       (make-type-array :type array.type
                        :index (index-append
                                (list (index-shape
                                       (index-const-list expr.dims))
                                      array.index))))
     :term-app
     (b* (((ok fun-arr-type) (check-expr expr.fun sortenv kindenv typeenv))
          ((ok fun-arr-type+index) (type-match-array fun-arr-type))
          (fun-type (type+index->type fun-arr-type+index))
          (fun-index (type+index->index fun-arr-type+index))
          ((ok fun-types+type) (type-match-fun fun-type))
          (in-types (typelist+type->types fun-types+type))
          (out-type (typelist+type->type fun-types+type))
          ((ok in-types+indices) (type-list-match-array in-types))
          (in-atom-types (type+index-list->type in-types+indices))
          (in-indices (type+index-list->index in-types+indices))
          ((ok out-type+index) (type-match-array out-type))
          (out-atom-type (type+index->type out-type+index))
          (out-index (type+index->index out-type+index))
          ((ok arg-types) (check-expr-list expr.args sortenv kindenv typeenv))
          ((ok arg-types+indices) (type-list-match-array arg-types))
          (arg-atom-types (type+index-list->type arg-types+indices))
          (arg-indices (type+index-list->index arg-types+indices))
          ((unless (equal arg-atom-types in-atom-types)) (reserr nil))
          ((ok prefix-indices) (check-index-suffixes arg-indices in-indices))
          ((ok principal-index) (join-indices (cons fun-index prefix-indices))))
       (make-type-array :type out-atom-type
                        :index (index-append (list principal-index out-index))))
     :type-app
     (b* (((ok fun-arr-type) (check-expr expr.fun sortenv kindenv typeenv))
          ((ok fun-arr-type+index) (type-match-array fun-arr-type))
          (fun-type (type+index->type fun-arr-type+index))
          (fun-index (type+index->index fun-arr-type+index))
          ((ok fun-vars+type) (type-match-forall fun-type))
          (kvars (kindedvarlist+type->vars fun-vars+type))
          (body-arr-type (kindedvarlist+type->type fun-vars+type))
          ((ok body-type+index) (type-match-array body-arr-type))
          (body-atom-type (type+index->type body-type+index))
          (body-index (type+index->index body-type+index))
          ((ok kinds) (check-type-list expr.args sortenv kindenv))
          ((unless (equal kinds (kinded-var-list->kind kvars))) (reserr nil))
          (bound-vars (kinded-var-list->var kvars))
          (subst (omap::from-lists bound-vars expr.args)))
       (make-type-array
        :type (subst-free-type-vars-in-type body-atom-type subst)
        :index (index-append (list fun-index body-index))))
     :index-app
     (b* (((ok fun-arr-type) (check-expr expr.fun sortenv kindenv typeenv))
          ((ok fun-arr-type+index) (type-match-array fun-arr-type))
          (fun-type (type+index->type fun-arr-type+index))
          (fun-index (type+index->index fun-arr-type+index))
          ((ok fun-vars+type) (type-match-product fun-type))
          (svars (sortedvarlist+type->vars fun-vars+type))
          (body-arr-type (sortedvarlist+type->type fun-vars+type))
          ((ok body-type+index) (type-match-array body-arr-type))
          (body-atom-type (type+index->type body-type+index))
          (body-index (type+index->index body-type+index))
          ((ok sorts) (check-index-list expr.args sortenv))
          ((unless (equal sorts (sorted-var-list->sort svars))) (reserr nil))
          (bound-vars (sorted-var-list->var svars))
          (subst (omap::from-lists bound-vars expr.args))
          (body-index-subst (subst-vars-in-index body-index subst)))
       (make-type-array
        :type (subst-free-index-vars-in-type body-atom-type subst)
        :index (index-append (list fun-index body-index-subst))))
     :unbox
     (b* (((ok target-arr-type)
           (check-expr expr.target sortenv kindenv typeenv))
          ((ok target-arr-type+index) (type-match-array target-arr-type))
          (sum-type (type+index->type target-arr-type+index))
          (sum-index (type+index->index target-arr-type+index))
          ((ok sum-vars+type) (type-match-sum sum-type))
          (svars (sortedvarlist+type->vars sum-vars+type))
          (body-type (sortedvarlist+type->type sum-vars+type))
          ((unless (= (len expr.index-vars) (len svars))) (reserr nil))
          (bound-vars (sorted-var-list->var svars))
          (sorts (sorted-var-list->sort svars))
          (sortenv-addition (omap::from-lists expr.index-vars sorts))
          (sortenv (omap::update* sortenv-addition
                                  (string-sort-map-fix sortenv)))
          (renaming (omap::from-lists bound-vars expr.index-vars))
          (body-type-renam (rename-free-index-vars-in-type body-type renaming))
          (typeenv (omap::update expr.term-var
                                 body-type-renam
                                 (string-type-map-fix typeenv)))
          ((ok arr-type) (check-expr expr.body sortenv kindenv typeenv))
          ((ok arr-type+index) (type-match-array arr-type))
          (body-atom-type (type+index->type arr-type+index))
          (body-index (type+index->index arr-type+index))
          ((ok kind) (check-type arr-type sortenv kindenv))
          ((unless (kind-case kind :array)) (reserr nil)))
       (make-type-array :type body-atom-type
                        :index (index-append (list sum-index body-index)))))
    :measure (expr-count expr))

  (define check-expr-list ((exprs expr-listp)
                           (sortenv string-sort-mapp)
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
         ((ok type) (check-expr (car exprs) sortenv kindenv typeenv))
         ((ok types) (check-expr-list (cdr exprs) sortenv kindenv typeenv)))
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
                      (sortenv string-sort-mapp)
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
       and determined via separate functions."))
    (declare (ignore sortenv kindenv typeenv))
    (atom-case
     atom
     :base (type-base (base-type-of-base-value atom.value))
     :op (type-of-prim-op atom.op)
     :term-abs (reserr :todo)
     :type-abs (reserr :todo)
     :index-abs (reserr :todo)
     :box (reserr :todo))
    :measure (atom-count atom))

  (define check-atom-list ((atoms atom-listp)
                           (sortenv string-sort-mapp)
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
         ((ok type) (check-atom (car atoms) sortenv kindenv typeenv))
         ((ok types) (check-atom-list (cdr atoms) sortenv kindenv typeenv)))
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

  :prepwork ((set-bogus-mutual-recursion-ok t)) ; TODO: remove

  :verify-guards nil ; done below

  ///

  (defruled guards-lemma
    (implies (equal x y)
             (equal (len x) (len y))))

  (verify-guards check-expr
    :hints (("Goal"
             :use ((:instance guards-lemma
                              (x (type+index-list->type
                                  (type-list-match-array
                                   (check-expr-list
                                    (expr-term-app->args expr)
                                    sortenv kindenv typeenv))))
                              (y (type+index-list->type
                                  (type-list-match-array
                                   (typelist+type->types
                                    (type-match-fun
                                     (type+index->type
                                      (type-match-array
                                       (check-expr
                                        (expr-term-app->fun expr)
                                        sortenv kindenv typeenv)))))))))
                   (:instance guards-lemma
                              (x (check-type-list
                                  (expr-type-app->args expr)
                                  sortenv kindenv))
                              (y (kinded-var-list->kind
                                  (kindedvarlist+type->vars
                                   (type-match-forall
                                    (type+index->type
                                     (type-match-array
                                      (check-expr
                                       (expr-type-app->fun expr)
                                       sortenv kindenv typeenv))))))))
                   (:instance guards-lemma
                              (x (check-index-list
                                  (expr-index-app->args expr)
                                  sortenv))
                              (y (sorted-var-list->sort
                                  (sortedvarlist+type->vars
                                   (type-match-product
                                    (type+index->type
                                     (type-match-array
                                      (check-expr
                                       (expr-index-app->fun expr)
                                       sortenv kindenv typeenv))))))))))))

  (fty::deffixequiv-mutual check-exprs/atoms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle the 'todo's above
