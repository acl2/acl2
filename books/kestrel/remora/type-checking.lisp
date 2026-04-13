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
(include-book "type-equivalence")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable kindp-when-kind-resultp-and-not-reserrp
                    kind-listp-when-kind-list-resultp-and-not-reserrp
                    sortp-when-sort-resultp-and-not-reserrp
                    sort-listp-when-sort-list-resultp-and-not-reserrp
                    typep-when-type-resultp-and-not-reserrp
                    type-listp-when-type-list-resultp-and-not-reserrp
                    type+index-p-when-type+index-resultp-and-not-reserrp)))

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
    "This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap index-senv
  :short "Fixtype of static environments for indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "These associate sorts to (index) variables.")
   (xdoc::p
    "They are denoted as @($\\Theta$) in the papers and dissertation."))
  :key-type string
  :val-type sort
  :pred index-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap type-senv
  :short "Fixtype of static environments for types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These associate kinds to (type) variables.")
   (xdoc::p
    "They are denoted as @($\\Delta$) in the papers and dissertation."))
  :key-type string
  :val-type kind
  :pred type-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap term-senv
  :short "Fixtype of static environments for terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These associate types to (term) variables.")
   (xdoc::p
    "They are denoted as @($\\Gamma$) in the papers and dissertation."))
  :key-type string
  :val-type type
  :pred term-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sorted-var-list-to-index-senv ((svars sorted-var-listp))
  :returns (indenv index-senvp)
  :short "Turn a list of sorted variables into a static index environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the environment, with the associated sorts.
     If there are duplicate variables, the leftmost ones prevail.
     When we call this function on the formals of a lambda abstraction,
     we check that there are no duplicates."))
  (b* (((when (endp svars)) nil)
       ((sorted-var svar) (car svars))
       (indenv (sorted-var-list-to-index-senv (cdr svars))))
    (omap::update svar.var svar.sort indenv))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define kinded-var-list-to-type-senv ((kvars kinded-var-listp))
  :returns (typenv type-senvp)
  :short "Turn a list of kinded variables into a static type environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the environment, with the associated kinds.
     If there are duplicate variables, the leftmost ones prevail.
     When we call this function on the formals of a lambda abstraction,
     we check that there are no duplicates."))
  (b* (((when (endp kvars)) nil)
       ((kinded-var kvar) (car kvars))
       (typenv (kinded-var-list-to-type-senv (cdr kvars))))
    (omap::update kvar.var kvar.kind typenv))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typed-var-list-to-term-senv ((tvars typed-var-listp))
  :returns (termenv term-senvp)
  :short "Turn a list of typed variables into a static term environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the variables,
     and put them into the environment, with the associated types.
     If there are duplicate variables, the leftmost ones prevail.
     When we call this function on the formals of a lambda abstraction,
     we check that there are no duplicates."))
  (b* (((when (endp tvars)) nil)
       ((typed-var tvar) (car tvars))
       (termenv (typed-var-list-to-term-senv (cdr tvars))))
    (omap::update tvar.var tvar.type termenv))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-indices
  :short "Check indices and lists of indices."

  (define check-index ((index indexp) (indenv index-senvp))
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
    (b* ((indenv (index-senv-fix indenv)))
      (index-case
       index
       :var (b* ((name+sort (omap::assoc index.name indenv))
                 ((unless name+sort) (reserr nil)))
              (cdr name+sort))
       :const (sort-dim)
       :shape (b* (((ok sorts) (check-index-list index.indices indenv))
                   ((unless (sort-list-dimp sorts)) (reserr nil)))
                (sort-shape))
       :add (b* (((ok sorts) (check-index-list index.indices indenv))
                 ((unless (sort-list-dimp sorts)) (reserr nil)))
              (sort-dim))
       :append (b* (((ok sorts) (check-index-list index.indices indenv))
                    ((unless (sort-list-shapep sorts)) (reserr nil)))
                 (sort-shape))))
    :measure (index-count index))

  (define check-index-list ((indices index-listp) (indenv index-senvp))
    :returns (sorts sort-list-resultp)
    :parents (type-checking check-indices)
    :short "Check a list of indices, returning their sorts if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The sorts are in the same order as the indices."))
    (b* (((when (endp indices)) nil)
         ((ok sort) (check-index (car indices) indenv))
         ((ok sorts) (check-index-list (cdr indices) indenv)))
      (cons sort sorts))
    :measure (index-list-count indices))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual check-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-types
  :short "Check types and lists of types."

  (define check-type ((type typep) (indenv index-senvp) (typenv type-senvp))
    :returns (kind kind-resultp)
    :parents (type-checking check-indices)
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
    (b* ((indenv (index-senv-fix indenv))
         (typenv (type-senv-fix typenv)))
      (type-case
       type
       :var (b* ((name+kind (omap::assoc type.name typenv))
                 ((unless name+kind) (reserr nil)))
              (cdr name+kind))
       :base (kind-atom)
       :array (b* (((ok kind) (check-type type.type indenv typenv))
                   ((unless (kind-case kind :atom)) (reserr nil))
                   ((ok sort) (check-index type.index indenv))
                   ((unless (sort-case sort :shape)) (reserr nil)))
                (kind-array))
       :fun (b* (((ok kinds) (check-type-list type.in indenv typenv))
                 ((unless (kind-list-arrayp kinds)) (reserr nil))
                 ((ok kind) (check-type type.out indenv typenv))
                 ((unless (kind-case kind :array)) (reserr nil)))
              (kind-atom))
       :forall (b* ((vars (kinded-var-list->var type.vars))
                    ((unless (no-duplicatesp-equal vars)) (reserr nil))
                    (typenv-addition (kinded-var-list-to-type-senv type.vars))
                    (typenv (omap::update* typenv-addition typenv))
                    ((ok kind) (check-type type.type indenv typenv))
                    ((unless (kind-case kind :array)) (reserr nil)))
                 (kind-atom))
       :pi (b* ((vars (sorted-var-list->var type.vars))
                ((unless (no-duplicatesp-equal vars)) (reserr nil))
                (indenv-addition (sorted-var-list-to-index-senv type.vars))
                (indenv (omap::update* indenv-addition indenv))
                ((ok kind) (check-type type.type indenv typenv))
                ((unless (kind-case kind :array)) (reserr nil)))
             (kind-atom))
       :sigma (b* ((vars (sorted-var-list->var type.vars))
                   ((unless (no-duplicatesp-equal vars)) (reserr nil))
                   (indenv-addition (sorted-var-list-to-index-senv type.vars))
                   (indenv (omap::update* indenv-addition indenv))
                   ((ok kind) (check-type type.type indenv typenv))
                   ((unless (kind-case kind :array)) (reserr nil)))
                (kind-atom))))
    :measure (type-count type))

  (define check-type-list ((types type-listp)
                           (indenv index-senvp)
                           (typenv type-senvp))
    :returns (kinds kind-list-resultp)
    :parents (type-checking check-types)
    :short "Check a list of types, returning their kinds if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The kinds are in the same order as the types."))
    (b* (((when (endp types)) nil)
         ((ok kind) (check-type (car types) indenv typenv))
         ((ok kinds) (check-type-list (cdr types) indenv typenv)))
      (cons kind kinds))
    :measure (type-list-count types))

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
        (tpi ("d" :dim
              "s" :shape)
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
                      (indenv index-senvp)
                      (typenv type-senvp)
                      (termenv term-senvp))
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
       The latter is concatenated after the frame's dimensions."))
    (expr-case
     expr
     :var (b* ((name+type (omap::assoc expr.name (term-senv-fix termenv)))
               ((unless name+type) (reserr nil)))
            (cdr name+type))
     :array (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                 ((unless (= (len expr.atoms)
                             (nat-list-product expr.dims)))
                  (reserr nil))
                 ((ok types) (check-atom-list expr.atoms indenv typenv termenv))
                 ((unless (type-list-all-equivp types)) (reserr nil))
                 (type (car types))
                 ((ok kind) (check-type type indenv typenv))
                 ((unless (kind-case kind :atom)) (reserr nil)))
              (make-type-array :type type
                               :index (index-shape
                                       (index-const-list expr.dims))))
     :array-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                       ((ok kind) (check-type expr.type indenv typenv))
                       ((unless (kind-case kind :atom)) (reserr nil)))
                    (make-type-array :type expr.type
                                     :index (index-shape
                                             (index-const-list expr.dims))))
     :frame (b* (((when (member-equal 0 expr.dims)) (reserr nil))
                 ((unless (= (len expr.exprs)
                             (nat-list-product expr.dims)))
                  (reserr nil))
                 ((ok types) (check-expr-list expr.exprs indenv typenv termenv))
                 ((unless (type-list-all-equivp types)) (reserr nil))
                 (type (car types))
                 ((ok kind) (check-type type indenv typenv))
                 ((unless (kind-case kind :array)) (reserr nil))
                 ((ok (type+index array)) (type-match-array type)))
              (make-type-array :type array.type
                               :index (index-append
                                       (list (index-shape
                                              (index-const-list expr.dims))
                                             array.index))))
     :frame-empty (b* (((unless (member-equal 0 expr.dims)) (reserr nil))
                       ((ok (type+index array)) (type-match-array expr.type))
                       ((ok kind) (check-type array.type
                                              indenv
                                              typenv))
                       ((unless (kind-case kind :atom)) (reserr nil))
                       ((ok sort) (check-index array.index
                                               indenv))
                       ((unless (sort-case sort :shape)) (reserr nil)))
                    (make-type-array :type array.type
                                     :index (index-append
                                             (list (index-shape
                                                    (index-const-list expr.dims))
                                                   array.index))))
     :term-app (reserr :todo)
     :type-app (reserr :todo)
     :index-app (reserr :todo)
     :unbox (reserr :todo))
    :measure (expr-count expr))

  (define check-expr-list ((exprs expr-listp)
                           (indenv index-senvp)
                           (typenv type-senvp)
                           (termenv term-senvp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of expressions, returning their types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the expressions."))
    (b* (((when (endp exprs)) nil)
         ((ok type) (check-expr (car exprs) indenv typenv termenv))
         ((ok types) (check-expr-list (cdr exprs) indenv typenv termenv)))
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
      :hints (("Goal" :induct (len exprs):in-theory (enable len)))))

  (define check-atom ((atom atomp)
                      (indenv index-senvp)
                      (typenv type-senvp)
                      (termenv term-senvp))
    :returns (type type-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check an atom, returning its type if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type of a base value or a primitive operator
       is independent from the environment(s),
       and determined via separate functions."))
    (declare (ignore indenv typenv termenv))
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
                           (indenv index-senvp)
                           (typenv type-senvp)
                           (termenv term-senvp))
    :returns (types type-list-resultp)
    :parents (type-checking check-exprs/atoms)
    :short "Check a list of atoms, returning their types if successful."
    :long
    (xdoc::topstring
     (xdoc::p
      "The types are in the same order as the atoms."))
    (b* (((when (endp atoms)) nil)
         ((ok type) (check-atom (car atoms) indenv typenv termenv))
         ((ok types) (check-atom-list (cdr atoms) indenv typenv termenv)))
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
      :hints (("Goal" :induct (len atoms):in-theory (enable len)))))

  :prepwork ((set-bogus-mutual-recursion-ok t)) ; TODO: remove

  :verify-guards nil ; done below

  ///

  (verify-guards check-expr)

  (fty::deffixequiv-mutual check-exprs/atoms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: handle the 'todo's above
