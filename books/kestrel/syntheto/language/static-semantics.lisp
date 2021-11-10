; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "static-semantics-types")

(local (include-book "std/lists/append" :dir :system))


;(local (include-book "kestrel/lists-light/remove-equal" :dir :system))

;; Add to "kestrel/lists-light/remove-equal" ?
(defthm alistp-remove-equal
  (implies (alistp l)
           (alistp (remove-equal x l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (language)
  :short "Static semantics of Syntheto."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the constraints that Syntheto code must satisfy
     in order to be well-formed and have a formal semantics.")
   (xdoc::p
    "The constraints include type requirements,
     according to Syntheto's strong typing.
     Since the Syntheto type system includes
     predicate subtypes and product/sum type invariants,
     the static semantics is undecidable,
     because it may involve general theorem proving.
     We handle this situation by splitting the static semantics
     into a decidable and an undecidable part,
     similar to systems like PVS and Specware.
     The decidable part handles most of the constraints,
     generating proof obligations for the undecidable parts.
     Proof obligations are Syntheto boolean expressions
     universally quantified over its explicitly typed free variables.")
   (xdoc::p
    "The constraints of the static semantics are checked
     in the context of variables, types, and other entities
     that are in scope and can be referenced.
     We represent the context as an explicit data structure,
     which is passed to the ACL2 functions that check the constraints
     and which is updated by some of these functions
     as more entities come into scope.
     In addition to the entities mentioned above,
     since we need to generate proof obligations,
     the context also includes conditions (boolean expressions)
     collected as expressions are traversed."))
  :order-subtopics t
  :default-parent t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *builtin-function-names*
  :short "List of identifiers of the Syntheto built-in functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial selection, which may change in the future."))
  (list (identifier "empty")
        (identifier "add")
        (identifier "append")
        (identifier "length")
        (identifier "is_empty")
        (identifier "first")
        (identifier "last")
        (identifier "rest")
        (identifier "member")
        (identifier "remove_first"))
  ///
  (assert-event (identifier-listp *builtin-function-names*))
  (assert-event (no-duplicatesp-equal *builtin-function-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-result
  :short "Fixtype of type results."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible results of checking that
     an expression satisfies the constraints of the static semantics.
     If the check fails, we return an error,
     which may contain information,
     which we do not constraint to be a fixtype for more flexibility.
     If the checking succeeds,
     it returns the calculated type(s) of the expression,
     along with a list of zero or more proof obligations.")
   (xdoc::p
    "The type(s) of the expression consists of one or more types;
     it is never the empty list.
     The list is a singleton when the expression returns a single value,
     while it is longer when the expression returns a multiple value,
     where `multiple' is in the same sense as ACL2's @(tsee mv);
     recall that Syntheto is a front-end language for ACL2,
     and so Syntheto's multiple values correspond to ACL2's multiple values.")
   (xdoc::p
    "The proof obligations are organized as a list, instead of a set,
     just so that the ordering matches the order in which they arise,
     as the user visually scans the expression.
     The ordering has no real logical meaning;
     however, as it should be provable,
     the ordering is such that each obligation is well-formed
     in the context of the preceding ones.")
   (xdoc::p
    "The values of this fixtype are also used as result of
     checking lists of expressions instead of single expressions.
     In that case, the list of types has a different meaning:
     each expression is single-valued,
     and each type in the list corresponds to an expression.
     When we check the static well-formedness of a list of expressions,
     they are always required to be single-values,
     so it is adequate to use a list of types, and not a list of lists of types.
     In Syntheto, as in ACL2,
     there are restrictions on the use of multi-valued expressions,
     e.g. they cannot be passed as arguments to functions;
     they have to be bound to (multiple) variables first.")
   (xdoc::p
    "See @(tsee check-expression) and mutually recursive companions
     for details on how the values of this fixtype are used."))
  (:ok ((types type-listp)
        (obligations proof-obligation-list)))
  (:err ((info any)))
  :pred type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ensure-single-type ((types type-listp))
  :returns (type? maybe-typep)
  :short "Ensure that a list of types is a singleton."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, return the type.
     Otherwise, we return @('nil').")
   (xdoc::p
    "This is used to ensure that an expression is single-valued.
     We call this function on the type list in the @(tsee type-result)
     resulting from checking the static well-formedness of the expression."))
  (and (consp types)
       (not (consp (cdr types)))
       (type-fix (car types)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subtypep ((sub typep) (sup typep) (tops toplevel-listp))
  :returns (yes/no booleanp)
  :short "Check if a type is a subtype of another type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The subtype definitions in a list of Syntheto top-level constructs
     induce a subtype relation over types.
     In Syntheto, subtype means true inclusion of values,
     not an embedding as in other languages;
     thus, certain values belong to multiple types,
     e.g. the integer 4 belongs to the type of integers,
     but also to a possible subtype of natural numbers,
     and to a possible subtype of even numbers.")
   (xdoc::p
    "A primitive, collection, or options type
     is only (reflexively) a subtype of itself.
     Currently Syntheto's subtypes do not lift
     from element types to collection types.
     A defined type is only a subtype of itself
     if it is a sum or product type;
     otherwise, it is a subtype not only of itself,
     but also of its direct supertype
     (i.e. the one referenced in its subtype definition),
     and of all the direct supertype's supertypes.")
   (xdoc::p
    "Thus, to check whether @('sub') is a subtype of @('sup'),
     we first check if they are the same type.
     Otherwise, the subtype relation cannot hold
     unless @('sub') has a direct supertype.
     If the latter is the same as @('sup'), the subtype relation holds.
     Otherwise, we recursively check whether
     the direct supertype is a subtype of @('sup').")
   (xdoc::p
    "In well-formed Syntheto there are no subtype circularities
     and so the recursion terminates.
     However, this ACL2 function has
     no assumption of well-formedness.
     The latter notion needs the notion of maximal supertype to be expressed:
     it may be possible to set up a large mutual recursion
     to define all these concepts,
     but that may increase the complexity of the static semantics.
     Thus, we prefer to totalize this function here
     to work on non-well-formed lists of Syntheto top-level constructs.
     We extract the list of all defined type names
     from the list of top-level constructs,
     and use that list to look up the type definitions,
     removing each used up definition from the list.
     This way, circularities are detected when attempting to look up
     the same definition twice, which will not be in the list the second time;
     we return @('nil') (i.e. no subtype relation) if we detect a circularity.
     The length of the list is the measure for termination."))
  (subtypep-aux sub sup (get-defined-type-names tops) tops)
  :hooks (:fix)

  :prepwork
  ((define subtypep-aux ((sub typep)
                         (sup typep)
                         (defined-names identifier-listp)
                         (tops toplevel-listp))
     :returns (yes/no booleanp)
     :parents nil
     (b* ((defined-names (identifier-list-fix defined-names)))
       (or (type-equiv sub sup)
           (b* ((direct (direct-supertype sub tops)))
             (and direct
                  (b* ((name (type-defined->name sub)))
                    (and (member-equal name defined-names)
                         (subtypep-aux direct
                                       sup
                                       (remove1-equal name defined-names)
                                       tops)))))))
     :measure (len defined-names)
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define max-supertype ((type typep) (tops toplevel-listp))
  :returns (super? maybe-typep)
  :short "Maximal supertype of a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We follow the chain of direct subtypes,
     returning the last one in the chain,
     which may be the starting type when it is not a subtype.")
   (xdoc::p
    "The discussion in @(tsee subtypep)
     about well-formedness and circularities
     applies here.
     We use the same approach to ensure termination.
     We return @('nil') if we detect a circularity.
     The result is never @('nil') in
     well-formed lists of top-level constructs."))
  (max-supertype-aux type (get-defined-type-names tops) tops)
  :hooks (:fix)

  :prepwork
  ((define max-supertype-aux ((type typep)
                              (defined-names identifier-listp)
                              (tops toplevel-listp))
     :returns (super? maybe-typep)
     :parents nil
     (b* ((defined-names (identifier-list-fix defined-names))
          (direct (direct-supertype type tops)))
       (if direct
           (b* ((name (type-defined->name type)))
             (and (member-equal name defined-names)
                  (max-supertype-aux direct
                                     (remove1-equal name defined-names)
                                     tops)))
         (type-fix type)))
     :measure (len defined-names)
     :hooks (:fix))))

(define max-supertypes ((types type-listp) (tops toplevel-listp))
  :returns (super? type-listp)
  (if (endp types)
      ()
    (cons (or (max-supertype (car types) tops)
              (type-fix (car types)))
          (max-supertypes (cdr types) tops)))
   :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define supremum-type ((type1 typep) (type2 typep) (tops toplevel-listp))
  :returns (supremum? maybe-typep)
  :short "Supremum (i.e. least upper bound) of two Syntheto types."
  :long
  (xdoc::topstring
   (xdoc::p
    "If one type is a subtype of the other, the latter is the supremum.
     Otherwise, we move up one step from either type if possible
     (i.e. if the chosen type has a direct one),
     and continue like that.
     It does not matter which type we choose.
     If the two types have a supremum, all paths converge to it.
     Here we always choose the first type, @('type1').")
   (xdoc::p
    "The discussion in @(tsee subtypep)
     about well-formedness and circularities
     applies here.
     We use the same approach to ensure termination.
     We return @('nil') if we detect a circularity."))
  (supremum-type-aux type1 type2 (get-defined-type-names tops) tops)
  :hooks (:fix)

  :prepwork
  ((define supremum-type-aux ((type1 typep)
                              (type2 typep)
                              (defined-names identifier-listp)
                              (tops toplevel-listp))
     :returns (supremum? maybe-typep)
     :parents nil
     (b* ((defined-names (identifier-list-fix defined-names))
          ((when (subtypep type1 type2 tops)) (type-fix type2))
          ((when (subtypep type2 type1 tops)) (type-fix type1))
          (direct (direct-supertype type1 tops)))
       (and direct
            (b* ((name (type-defined->name type1)))
              (and (member-equal name defined-names)
                   (supremum-type-aux direct
                                      type2
                                      (remove1-equal name defined-names)
                                      tops)))))
     :measure (len defined-names)
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define supremum-type-list ((types1 type-listp)
                            (types2 type-listp)
                            (tops toplevel-listp))
  :returns (mv (okp booleanp)
               (supremum type-listp))
  :short "Lift @(tsee supremum-type) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two input lists must have the same length for the supremum to exist.
     Given that @('nil') is a valid result when both lists are empty,
     we return an additional explicit boolean result for success or failure."))
  (b* (((when (endp types1)) (mv (endp types2) nil))
       ((when (endp types2)) (mv nil nil))
       (type (supremum-type (car types1) (car types2) tops))
       ((when (not type)) (mv nil nil))
       ((mv okp types) (supremum-type-list (cdr types1) (cdr types2) tops))
       ((when (not okp)) (mv nil nil)))
    (mv t (cons type types)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define non-trivial-proof-obligation ((variables typed-variable-listp)
                                      (hypotheses obligation-hyp-listp)
                                      (restriction expressionp)
                                      (expr expressionp))
  :returns (oblig? proof-obligation-listp) ; Actually singleton list or nil
  (if (member-equal (obligation-hyp-condition restriction) (obligation-hyp-list-fix hypotheses))
      nil
    (b* ((oblig (make-proof-obligation :variables variables
                                       :hypotheses hypotheses
                                       :conclusion restriction
                                       :source-expression expr))
         ;; (- (cw "Obligation for ~x0~%~x1~%" (d-->a-expr expr) (proof-obligation-to-acl2-theorem oblig ())))
         )
      (list oblig)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-subproof-obligations ((variables typed-variable-listp)
                                   (hypotheses obligation-hyp-listp)
                                   (restrictions expression-listp)
                                   (expr expressionp))
  :returns (obligs proof-obligation-listp)
  :short "Create the obligations for a chain of subtypes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee match-type):
     see the documentation of that function for background.")
   (xdoc::p
    "This function takes as inputs
     (i) the typed variables in context,
     (ii) the hypotheses in context, and
     (iii) the sequence of expressions that define
     the restrictions of each subtype in the chain,
     from the supremum of @(tsee match-type)'s source and destination types
     down to the destination type,
     in the same order.
     This function returns as output a list of proof obligations,
     one for each of the expression in (iii) above:
     the obligation has that expression as conclusion,
     and as hypotheses has the ones in (ii) above,
     augmented by all the preceding type restriction expressions."))
  (cond ((endp restrictions) nil)
        (t (let ((oblig? (non-trivial-proof-obligation variables hypotheses (car restrictions)
                                                     expr))
                 (r-obligs (make-subproof-obligations
                            variables
                            (append (obligation-hyp-list-fix hypotheses)
                                    (list (obligation-hyp-condition (car restrictions))))
                            (cdr restrictions)
                            expr)))
             (append oblig? r-obligs))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define match-type ((expr expressionp)
                    (source typep)
                    (target typep)
                    (ctxt contextp))
  :returns (mv (yes/no booleanp)
               (obligs proof-obligation-listp))
  :short "Match a source type to a target type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when an expression with a statically calculated type
     (this is the source type)
     is passed as argument to a function with a certain argument type
     (this is the target type),
     or when a similar situation occurs
     (see the static semantic functions that call this function).
     We need to make sure that the expression,
     besides its inferred source type,
     also has the target type.
     The expression is passed to this ACL2 function,
     for the purpose of generating the proof obligations (see below).")
   (xdoc::p
    "This is trivial when source and target types are the same.
     When the source type is a subtype of the target type, it is also easy.
     In other cases, a necessary condition for
     the expression to have also the target type is that
     the source and target type have a supremum type:
     if they do not, they are disjoint types,
     and we have a ``typical'' type error.")
   (xdoc::p
    "If source and destination types have a supremum,
     there are three possible situations.
     One is that the target type is the supremum:
     in this case the source type is a subtype,
     and this case has already been described above as easy.
     Another case is that the source type is the supremum,
     in which case the target type is a subtype:
     in this case, we generate proof obligations
     saying that the expression satisfies all the predicates
     that define the subtypes down to the target type.
     The third case is that the supremum differs from both source and target:
     in this case, we know that the expression readily has
     also the supremum as type (going up the hierarchy from the source type),
     but to reach the target type,
     we need to generate proof obligations with all the predicates
     encountered from the supremum to the target.")
   (xdoc::p
    "The three cases above can be unified into
     (i) calculating the supremum and
     (ii) collecting the proof obligations from supremum down to target.
     If the supremum is the same as the target,
     then there is no obligation.
     Otherwise, there is some obligation.")
   (xdoc::p
    "We collect the subtype restriction expressions
     at the same time as we calculate the supremum:
     we do so by climbing up from the target type,
     and otherwise doing the same as in @(tsee supremum-type)
     (which climbs up from its first type argument).
     We use the same approach to ensuring termination.
     Note that the restriction expressions are collected in reverse:
     we put in the correct order, from higher to lower,
     and we call @(tsee make-subproof-obligations) to produce the obligations."))
  (b* (((mv yes/no restrs)
        (match-type-aux expr
                        source
                        target
                        (get-defined-type-names (context->tops ctxt))
                        (context->tops ctxt)))
       ((unless yes/no) (mv nil nil))
       (obligs (make-subproof-obligations (context->obligation-vars ctxt)
                                          (context->obligation-hyps ctxt)
                                          (rev restrs)
                                          expr)))
    (mv t obligs))
  :hooks (:fix)

  :prepwork
  ((define match-type-aux ((expr expressionp)
                           (source typep)
                           (target typep)
                           (defined-names identifier-listp)
                           (tops toplevel-listp))
     :returns (mv (yes/no booleanp)
                  (restrs expression-listp))
     :parents nil
     (b* ((defined-names (identifier-list-fix defined-names))
          ((when (subtypep source target tops)) (mv t nil))
          (tsub (get-type-subset target tops))
          ((when (not tsub)) (mv nil nil))
          (subst (omap::update (type-subset->variable tsub)
                               (expression-fix expr)
                               nil))
          (restr (subst-expression subst (type-subset->restriction tsub)))
          (name (type-defined->name target))
          ((unless (member-equal name defined-names)) (mv nil nil))
          ((mv yes/no restrs) (match-type-aux expr
                                              source
                                              (type-subset->supertype tsub)
                                              (remove1-equal name defined-names)
                                              tops))
          ((unless yes/no) (mv nil nil)))
       (mv t (cons restr restrs)))
     :measure (len defined-names)
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define match-type-list ((exprs expression-listp)
                         (sources type-listp)
                         (targets type-listp)
                         (ctxt contextp))
  :guard (= (len exprs) (len sources))
  :returns (mv (yes/no booleanp)
               (obligs proof-obligation-listp))
  :short "Match a list of source types to a list of target types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee match-type) to lists.
     The number of expressions and source types are the same,
     because the source types are the ones of the expressions.
     The number of target types must also be the same
     for this function to succeed.
     We accumulate the proof obligations and return all of them."))
  (b* (((when (endp exprs)) (mv (endp targets) nil))
       ((when (endp targets)) (mv nil nil))
       ((mv okp obligs)
        (match-type (car exprs) (car sources) (car targets) ctxt))
       ((unless okp) (mv nil nil))
       ((mv okp more-obligs)
        (match-type-list (cdr exprs) (cdr sources) (cdr targets) ctxt))
       ((unless okp) (mv nil nil)))
    (mv t (append obligs more-obligs)))
  :hooks (:fix)
  ///

  (defrule same-len-target-exprs-when-match-type-list
    (implies (mv-nth 0 (match-type-list exprs sources targets ctxt))
             (equal (len targets) (len exprs)))
    :enable match-type-list
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decompose-expression ((expr expressionp) (n posp))
  :returns (exprs expression-listp)
  :short "Decompose an expression into a list of expressions of given length."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('n') is 1, we return a singleton list containing the expression.
     Otherwise, we return a list of @('n') expressions,
     each of which is a component expression consisting of
     the initial expression as target and the list position as index.")
   (xdoc::p
    "The idea is that @('n') is 1 if the expression is single-valued,
     greater than 1 if the expression is multi-valued.
     In the latter case, @('n') should be equal to the
     number of components of the multiple value.
     Thus, the expression is decomposed into its one or more components."))
  (b* ((n (pos-fix n)))
    (if (= n 1)
        (list (expression-fix expr))
      (decompose-expression-aux 0 n expr)))
  :hooks (:fix)

  :prepwork
  ((define decompose-expression-aux ((i natp) (n natp) (expr expressionp))
     :returns (exprs expression-listp)
     (b* ((i (nfix i))
          (n (nfix n)))
       (if (>= i n)
           nil
         (cons (make-expression-component :multi expr :index i)
               (decompose-expression-aux (1+ i) n expr))))
     :measure (nfix (- (nfix n) (nfix i)))
     :hooks (:fix)
     ///
     (defret len-of-decompose-expression-aux
       (equal (len exprs)
              (nfix (- (nfix n) (nfix i)))))))

  ///

  (defret len-of-decompose-expression
    (equal (len exprs) (pos-fix n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define match-to-target ((expr expressionp)
                         (source type-listp)
                         (target type-listp)
                         (ctxt contextp))
 ; :guard (consp source)
  :returns (result type-resultp)
  :short "Match the type(s) of an expression to some optional target type(s)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we check the static semantics constraints for an expression,
     we normally calculate a (list of) type(s) for the expression
     (one if the expression is single-valued, more if multi-valued),
     and then we may or may not have a (list of) target type(s)
     that the expression must match.
     This ACL2 function performs this matching.")
   (xdoc::p
    "The @('target') input is @('nil') if there are no required target types.
     In this case, the matching succeeds
     and we return the type(s) of the expression.")
   (xdoc::p
    "Otherwise, we ensure that source and target types are
     the same in number and match element-wise.
     This may generate some proof obligations.
     If these checks succeed, we return the target type(s)."))
  (if (atom target)
      (make-type-result-ok :types source :obligations nil)
    (if (/= (len target) (len source))
        (type-result-err (list :type-mismatch-in-number
                           (type-list-fix source)
                           (type-list-fix target)))
      (b* ((exprs (decompose-expression expr (len target)))
           ((mv okp obligs) (match-type-list exprs source target ctxt)))
        (if okp
            (make-type-result-ok :types target :obligations obligs)
          (type-result-err (list :type-mismatch
                             (type-list-fix source)
                             (type-list-fix target)))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type ((type typep) (ctxt contextp))
  :returns (yes/no booleanp)
  :short "Check if a type is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The primitive types are always well-formed.
     The collection types and the option type are well-formed
     iff their argument types are.
     A defined type is well-formed iff
     it references a defined type in the existing top-level constructs,
     or one of the types being currently defined."))
  (type-case type
             :boolean t
             :character t
             :string t
             :integer t
             :set (check-type type.element ctxt)
             :sequence (check-type type.element ctxt)
             :map (and (check-type type.domain ctxt)
                       (check-type type.range ctxt))
             :option (check-type type.base ctxt)
             :defined (bool-fix (or (get-type-definition type.name
                                                         (context->tops ctxt))
                                    (member-equal type.name
                                                  (context->types ctxt)))))
  :measure (type-count type)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-list ((types type-listp) (ctxt contextp))
  :returns (yes/no booleanp)
  (or (endp types)
      (and (check-type (car types) ctxt)
           (check-type-list (cdr types) ctxt)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define literal-type ((lit literalp))
  :returns (type typep)
  :short "Type of a literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Syntheto, each literal has an obvious primitive type."))
  (literal-case lit
                :boolean (type-boolean)
                :character (type-character)
                :string (type-string)
                :integer (type-integer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-literal ((lit literalp))
  :returns (result type-resultp)
  :short "Check if a literal is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A literal is always well-formed,
     but we have this function so that we can return a type result,
     uniformly with other kinds of expressions.
     A literal never engenders any proof obligation.
     A literal is always single-valued."))
  (make-type-result-ok :types (list (literal-type lit)) :obligations nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-variable ((var identifierp) (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a variable is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable must be in the (variable) context.
     We return its contextual type.
     A variable never engenders any proof obligation.
     A variable is always single-valued."))
  (b* ((var-ctxt (context->variables ctxt))
       (var (identifier-fix var))
       (pair? (omap::in var var-ctxt))
       ((when (not pair?)) (type-result-err
                            (list :variable-not-in-context
                              var
                              var-ctxt)))
       (type (cdr pair?)))
    (make-type-result-ok :types (list type) :obligations nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-not-expression ((arg expressionp)
                              (arg-type typep)
                              (arg-obligs proof-obligation-listp)
                              (expr expressionp) ; might be useful for error reporting
                              (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a boolean negation expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operand must be a boolean, and the result is a boolean."))
  (declare (ignorable expr))
  (b* (((mv okp obligs) (match-type arg arg-type (type-boolean) ctxt))
       ((unless okp) (type-result-err
                      (list :type-mismatch-not
                        (expression-fix arg)
                        (type-fix arg-type)
                        (type-boolean))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the boolean type." obligs)))
    (make-type-result-ok :types (list (type-boolean))
                         :obligations (append arg-obligs obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-minus-expression ((arg expressionp)
                                (arg-type typep)
                                (arg-obligs proof-obligation-listp)
                                (expr expressionp) ; might be useful for error reporting
                                (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an integer negation expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operand must be an integer, and the result is an integer."))
  (declare (ignorable expr))
  (b* (((mv okp obligs) (match-type arg arg-type (type-integer) ctxt))
       ((unless okp) (type-result-err
                      (list :type-mismatch-minus
                        (expression-fix arg)
                        (type-fix arg-type)
                        (type-boolean))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the integer type."
               obligs)))
    (make-type-result-ok :types (list (type-integer))
                         :obligations (append arg-obligs obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-unary-expression ((op unary-opp)
                                (arg expressionp)
                                (arg-result type-resultp)
                                (expr expressionp)
                                (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a unary expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('arg-result') parameter of this function is
     the result of checking the operand expression.
     If it is an error, we propagate it.
     Otherwise, we dispatch based on the unary operator:
     each operator's function returns a result,
     which may add proof obligations to the ones from the operand."))
  (type-result-case
   arg-result
   :err (type-result-err arg-result.info)
   :ok (b* ((type (ensure-single-type arg-result.types)))
         (if (not type)
             (type-result-err (list :type-mismatch-multi
                                (expression-fix arg)
                                arg-result.types))
           (unary-op-case
            op
            :not (check-not-expression arg
                                       type
                                       arg-result.obligations
                                       expr
                                       ctxt)
            :minus (check-minus-expression arg
                                           type
                                           arg-result.obligations
                                           expr
                                           ctxt)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-eq/ne-expression ((arg1 expressionp)
                                (arg2 expressionp)
                                (arg1-type typep)
                                (arg2-type typep)
                                (arg1-obligs proof-obligation-listp)
                                (arg2-obligs proof-obligation-listp)
                                (err-keyword keywordp)
                                (expr expressionp)
                                (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an equality or inequality expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two types must have a supremum type,
     which is the one where the (in)equality is checked.
     Otherwise, the expression is not type-correct.
     The expression returns a boolean."))
  (declare (ignorable expr))
  (b* ((supremum (supremum-type arg1-type arg2-type (context->tops ctxt))))
    (if supremum
        (make-type-result-ok :types (list (type-boolean))
                             :obligations (append arg1-obligs
                                                  arg2-obligs))
      (type-result-err (list err-keyword
                             (expression-fix arg1)
                             (expression-fix arg2)
                             (type-fix arg1-type)
                             (type-fix arg2-type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-eq-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
                             (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an equality expression is well-formed."
  (check-eq/ne-expression arg1 arg2
                          arg1-type arg2-type
                          arg1-obligs arg2-obligs
                          :type-mismatch-eq expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ne-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
                             (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an inequality expression is well-formed."
  (check-eq/ne-expression arg1 arg2
                          arg1-type arg2-type
                          arg1-obligs arg2-obligs
                          :type-mismatch-ne expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-lt/le/gt/ge-expression ((arg1 expressionp)
                                      (arg2 expressionp)
                                      (arg1-type typep)
                                      (arg2-type typep)
                                      (arg1-obligs proof-obligation-listp)
                                      (arg2-obligs proof-obligation-listp)
                                      (err-keyword keywordp)
                                      (expr expressionp)
                                      (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an ordering expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two types must be
     both (subtypes of) integers,
     both (subtypes of) characters, or
     both (subtypes of) strings.
     We calculate the supremum type,
     and check whether it is (a subtype of) any of these three types.
     The expression returns a boolean."))
  (declare (ignorable expr))
  (b* ((supremum (supremum-type arg1-type arg2-type (context->tops ctxt))))
    (if (and supremum
             (subtypep supremum (type-integer) (context->tops ctxt)))
        (make-type-result-ok :types (list (type-boolean))
                             :obligations (append arg1-obligs
                                                  arg2-obligs))
      (type-result-err (list err-keyword
                             (expression-fix arg1)
                             (expression-fix arg2)
                             (type-fix arg1-type)
                             (type-fix arg2-type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-lt-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
                             (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a less-than expression is well-formed."
  (check-lt/le/gt/ge-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-lt expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-le-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
                             (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a less-than-or-equal-to expression is well-formed."
  (check-lt/le/gt/ge-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-le expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-gt-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
(ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a greater-than expression is well-formed."
  (check-lt/le/gt/ge-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-gt expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ge-expression ((arg1 expressionp)
                             (arg2 expressionp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-obligs proof-obligation-listp)
                             (arg2-obligs proof-obligation-listp)
                             (expr expressionp)
                             (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a greater-than-or-equal-to expression is well-formed."
  (check-lt/le/gt/ge-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-ge expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-iff-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
                              (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a coimplication expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operands must be booleans, and the result is a boolean."))
  (declare (ignorable expr))
  (b* (((mv okp obligs) (match-type arg1 arg1-type (type-boolean) ctxt))
       ((unless okp) (type-result-err
                      (list :type-mismatch-iff
                        (expression-fix arg1)
                        (expression-fix arg2)
                        (type-fix arg1-type)
                        (type-fix arg2-type)
                        (type-boolean))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the boolean type." obligs))
       ((mv okp obligs) (match-type arg2 arg2-type (type-boolean) ctxt))
       ((unless okp) (type-result-err
                      (list :type-mismatch-iff
                        (expression-fix arg1)
                        (expression-fix arg2)
                        (type-fix arg1-type)
                        (type-fix arg2-type)
                        (type-boolean))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the boolean type." obligs)))
    (make-type-result-ok :types (list (type-boolean))
                         :obligations (append arg1-obligs
                                              arg2-obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-add/sub/mul-expression ((arg1 expressionp)
                                      (arg2 expressionp)
                                      (arg1-type typep)
                                      (arg2-type typep)
                                      (arg1-obligs proof-obligation-listp)
                                      (arg2-obligs proof-obligation-listp)
                                      (err-keyword keywordp)
                                      (expr expressionp)
                                      (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an addition, substraction, or multiplication expression
          is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operands must be integers, and the result is an integer."))
  (declare (ignorable expr))
  (b* (((mv okp obligs) (match-type arg1 arg1-type (type-integer) ctxt))
       ((unless okp) (type-result-err
                      (list err-keyword
                            (expression-fix arg1)
                            (expression-fix arg2)
                            (type-fix arg1-type)
                            (type-fix arg2-type)
                            (type-integer))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the integer type." obligs))
       ((mv okp obligs) (match-type arg2 arg2-type (type-integer) ctxt))
       ((unless okp) (type-result-err
                      (list err-keyword
                            (expression-fix arg1)
                            (expression-fix arg2)
                            (type-fix arg1-type)
                            (type-fix arg2-type)
                            (type-integer))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the integer type." obligs)))
    (make-type-result-ok :types (list (type-integer))
                         :obligations (append arg1-obligs
                                              arg2-obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-add-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
                              (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if an addition expression is well-formed."
  (check-add/sub/mul-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-add expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sub-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
                              (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a subtraction expression is well-formed."
  (check-add/sub/mul-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-sub expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-mul-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
                              (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a multiplication expression is well-formed."
  (check-add/sub/mul-expression arg1 arg2
                                arg1-type arg2-type
                                arg1-obligs arg2-obligs
                                :type-mismatch-mul expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-div/rem-expression ((arg1 expressionp)
                                  (arg2 expressionp)
                                  (arg1-type typep)
                                  (arg2-type typep)
                                  (arg1-obligs proof-obligation-listp)
                                  (arg2-obligs proof-obligation-listp)
                                  (err-keyword keywordp)
                                  (expr expressionp)
                                  (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a division or remainder expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The operands must be integers, and the result is an integer.
     Furthermore, the divisor must be non-zero:
     we generate a proof obligation for that."))
  (b* (((mv okp obligs) (match-type arg1 arg1-type (type-integer) ctxt))
       ((unless okp) (type-result-err
                      (list err-keyword
                            (expression-fix arg1)
                            (expression-fix arg2)
                            (type-fix arg1-type)
                            (type-fix arg2-type)
                            (type-integer))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the integer type." obligs))
       ((mv okp obligs) (match-type arg2 arg2-type (type-integer) ctxt))
       ((unless okp) (type-result-err
                      (list err-keyword
                            (expression-fix arg1)
                            (expression-fix arg2)
                            (type-fix arg1-type)
                            (type-fix arg2-type)
                            (type-integer))))
       ((acl2::run-when (consp obligs))
        (raise "Internal error: obligations ~x0 for the integer type." obligs))
       (oblig? (non-trivial-proof-obligation
                (context->obligation-vars ctxt)
                (context->obligation-hyps ctxt)
                (make-expression-binary :operator (binary-op-ne)
                                        :left-operand arg2
                                        :right-operand
                                        (make-expression-literal
                                         :get (make-literal-integer :value 0)))
                expr)))
    (make-type-result-ok :types (list (type-integer))
                         :obligations (append arg1-obligs
                                              arg2-obligs
                                              oblig?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-div-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
(ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a division expression is well-formed."
  (check-div/rem-expression arg1 arg2
                            arg1-type arg2-type
                            arg1-obligs arg2-obligs
                            :type-mismatch-div expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-rem-expression ((arg1 expressionp)
                              (arg2 expressionp)
                              (arg1-type typep)
                              (arg2-type typep)
                              (arg1-obligs proof-obligation-listp)
                              (arg2-obligs proof-obligation-listp)
                              (expr expressionp)
(ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a multiplication expression is well-formed."
  (check-div/rem-expression arg1 arg2
                            arg1-type arg2-type
                            arg1-obligs arg2-obligs
                            :type-mismatch-rem expr ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-strict-binary-expression ((op binary-opp)
                                        (arg1 expressionp)
                                        (arg2 expressionp)
                                        (arg1-result type-resultp)
                                        (arg2-result type-resultp)
                                        (expr expressionp)
                                        (ctxt contextp))
  :guard (binary-op-strictp op)
  :returns (result type-resultp)
  :short "Check if a strict binary expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('arg1-result') and @('arg2-result') parameters of this function are
     the results of checking the operand expressions.
     If any is an error, we propagate it, left first.
     Otherwise, we dispatch based on the binary operator:
     each operator's function returns a result,
     which may add proof obligations to the ones from the operand."))
  (type-result-case
   arg1-result
   :err (type-result-err arg1-result.info)
   :ok (b* ((arg1-type (ensure-single-type arg1-result.types)))
         (if (not arg1-type)
             (type-result-err (list :type-mismatch-multi
                                (expression-fix arg1)
                                arg1-result.types))
           (type-result-case
            arg2-result
            :err (type-result-err arg2-result.info)
            :ok (b* ((arg2-type (ensure-single-type arg2-result.types)))
                  (if (not arg2-type)
                      (type-result-err (list :type-mismatch-multi
                                         (expression-fix arg2)
                                         arg2-result.types))
                    (case (binary-op-kind op)
                      (:eq (check-eq-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:ne (check-ne-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:lt (check-lt-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:le (check-le-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:gt (check-gt-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:ge (check-ge-expression arg1
                                                arg2
                                                arg1-type
                                                arg2-type
                                                arg1-result.obligations
                                                arg2-result.obligations
                                                expr ctxt))
                      (:iff (check-iff-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (:add (check-add-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (:sub (check-sub-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (:mul (check-mul-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (:div (check-div-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (:rem (check-rem-expression arg1
                                                  arg2
                                                  arg1-type
                                                  arg2-type
                                                  arg1-result.obligations
                                                  arg2-result.obligations
                                                  expr ctxt))
                      (t (prog2$ (impossible)
                                 (type-result-err :impossible))))))))))
  :guard-hints (("Goal" :in-theory (enable binary-op-strictp
                                           binary-op-nonstrictp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-call-expression ((function identifierp)
                               (types type-listp)
                               (args expression-listp)
                               (args-result type-resultp)
                               (expr expressionp)
                               (ctxt contextp))
  :guard (type-result-case args-result
                           :err t
                           :ok (= (len args-result.types) (len args)))
  :returns (result type-resultp)
  :short "Check if a function call is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the argument types match the function's input types.
     If the function has a precondition, we also generate a proof obligation
     saying that the arguments satisfy it.
     The call has the output types of the function."))
  (type-result-case
   args-result
   :err (type-result-err args-result.info)
   :ok (b* (((mv err? inputs outputs precond &)
             (get-function-in/out/pre/post function types ctxt))
            ((when err?) (type-result-err err?))
            (input-types (typed-variable-list->type-list inputs))
            (output-types (typed-variable-list->type-list outputs))
            ((mv okp obligs) (match-type-list args
                                              args-result.types
                                              input-types
                                              ctxt))
            ((when (not okp))
             (type-result-err (list :type-mismatch-call
                                (identifier-fix function)
                                (expression-list-fix args)
                                args-result.types
                                input-types)))
            (oblig?
             (if precond
                 (b* ((input-names (typed-variable-list->name-list inputs))
                      (subst (omap::from-lists input-names
                                               (expression-list-fix args)))
                      (formula (subst-expression subst precond)))
                   (non-trivial-proof-obligation
                    (context->obligation-vars ctxt)
                    (context->obligation-hyps ctxt)
                    formula expr))
               nil)))
         (make-type-result-ok :types output-types
                              :obligations (append args-result.obligations
                                                   obligs
                                                   oblig?))))
  :guard-hints (("Goal"
                 ;; somehow the forward chaining rule does not work:
                 :use (:instance same-len-target-exprs-when-match-type-list
                       (exprs args)
                       (sources (type-result-ok->types args-result))
                       (targets (typed-variable-list->type-list
                                 (mv-nth 1
                                         (get-function-in/out/pre/post
                                          function types ctxt)))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-multi-expression ((args expression-listp)
                                (args-result type-resultp))
  :guard (type-result-case args-result
                           :err t
                           :ok (= (len args-result.types) (len args)))
  :returns (result type-resultp)
  :short "Check if a multi-valued expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be two or more expressions.
     We return the same type result, unchanged."))
  (type-result-case
   args-result
   :err (type-result-err args-result.info)
   :ok (if (< (len args-result.types) 2)
           (type-result-err (list :multi-expression-non-multi
                              (expression-list-fix args)))
         (type-result-fix args-result)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-component-expression ((multi expressionp)
                                    (multi-result type-resultp)
                                    (index natp))
  :returns (result type-resultp)
  :short "Check if a multi-valued component expression is
          statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression must be a multi-valued one,
     i.e. have at least two types.
     The index must be below the number of types.
     The type corresponding to the index is the type of the expression."))
  (type-result-case
   multi-result
   :err (type-result-err multi-result.info)
   :ok (cond ((< (len multi-result.types) 2)
              (type-result-err
               (list :non-multi-component-expression (expression-fix multi))))
             ((>= (nfix index) (len multi-result.types))
              (type-result-err
               (list :multi-component-out-of-range
                 (expression-fix multi) (nfix index))))
             (t (make-type-result-ok
                 :types (list (nth (nfix index) multi-result.types))
                 :obligations multi-result.obligations))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define align-let-vars-values ((vars typed-variable-listp) (value expressionp))
  :returns (mv (okp booleanp)
               (var-names identifier-listp)
               (var-types type-listp)
               (values expression-listp))
  :short "Align bound variables to their expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Syntheto binding expression binds
     a single expression to a list of variables.
     There must be at least one variable, otherwise it is an error.
     If there is exactly one variable,
     the (value of the) expression is bound to it.
     If there are two or more variables,
     the expression must return multiple values,
     whose number must match the number of variables,
     and these values are bound to the variables, in order.")
   (xdoc::p
    "Statically, we can ``align'' the expression with the variable as follows.
     When there is an empty list of variables, it is an error.
     When there is exactly one variable, it aligns with the whole expression.
     Where there are two or more variables,
     each aligns with a component of the expression,
     i.e. with a component expression whose subexpression is
     the original expression bound to the variable list.")
   (xdoc::p
    "This ACL2 function carries out this ``alignment''.
     It returns a list of expressions, as many as the variables,
     each of which corresponds to a variable.
     It also decomposes the typed variables into names and types.
     Furthermore, it ensures that there is at least one variable,
     returning an error indication if that is not the case.
     This function is called by @(tsee check-bind-expression);
     see that function for further details."))
  (cond ((endp vars) (mv nil nil nil nil))
        ((endp (cdr vars)) (mv t
                               (typed-variable-list->name-list vars)
                               (typed-variable-list->type-list vars)
                               (list (expression-fix value))))
        (t (b* (((mv names types values)
                 (align-let-vars-values-aux vars 0 value)))
             (mv t names types values))))
  :hooks (:fix)

  :prepwork
  ((define align-let-vars-values-aux ((vars typed-variable-listp)
                                      (index natp)
                                      (value expressionp))
     :returns (mv (var-names identifier-listp)
                  (var-types type-listp)
                  (values expression-listp))
     (b* (((when (endp vars)) (mv nil nil nil))
          (var (car vars))
          (name (typed-variable->name var))
          (type (typed-variable->type var))
          (val (make-expression-component :multi value :index index))
          ((mv names types vals)
           (align-let-vars-values-aux (cdr vars) (1+ (nfix index)) value)))
       (mv (cons name names) (cons type types) (cons val vals)))
     :hooks (:fix)
     ///
     (defret len-of-align-let-vars-values-aux.names
       (equal (len var-names) (len vars)))
     (defret len-of-align-let-vars-values-aux.types
       (equal (len var-types) (len vars)))
     (defret len-of-align-let-vars-values-aux.values
       (equal (len values) (len vars)))))

  ///

  (defret len-of-align-let-vars-values.names
    (equal (len var-names) (len vars)))
  (defret len-of-align-let-vars-values.types
    (equal (len var-types) (len vars)))
  (defret len-of-align-let-vars-values.values
    (equal (len values) (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define match-field ((init initializerp)
                     (source typep)
                     (targets field-listp)
                     (ctxt contextp))
  :returns (mv (yes/no booleanp)
               (obligs proof-obligation-listp)
               (rest-targets field-listp))
  :short "Match a source field to some target field."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when checking the static semantics of
     initializers in product/sum constructions and updates:
     each initializer in such expressions (the @('init') input)
     with its own calculated type (the @('type') input),
     must correspond to a field in the product or sum type
     (one in the @('targets') input).
     Thus, we look for a field, with the same name as the initializer,
     in the target fields;
     if it is not found, it is an error;
     if it is found, we match the types
     and remove the target field from further consideration,
     by returning a list of the remaining fields.
     This function is called repeatedly by @(tsee match-field-list)."))
  (b* (((when (endp targets)) (mv nil nil nil))
       (target (field-fix (car targets)))
       ((when (not (equal (field->name target)
                          (initializer->field init))))
        (b* (((mv okp obligs rest-targets)
              (match-field init source (cdr targets) ctxt))
             ((when (not okp)) (mv nil nil nil)))
          (mv t obligs (cons target rest-targets))))
       ((mv okp obligs) (match-type (initializer->value init)
                                    source
                                    (field->type target)
                                    ctxt))
       ((when (not okp)) (mv nil nil nil)))
    (mv t obligs (field-list-fix (cdr targets))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define match-field-list ((inits initializer-listp)
                          (sources type-listp)
                          (targets field-listp)
                          (ctxt contextp))
  :guard (= (len inits) (len sources))
  :returns (mv (yes/no booleanp)
               (obligs proof-obligation-listp)
               (rest-targets field-listp))
  :short "Match a list of source fields to some target fields."
  (b* (((when (endp inits)) (mv t nil (field-list-fix targets)))
       (init (car inits))
       (source (car sources))
       ((mv okp first-obligs targets) (match-field init source targets ctxt))
       ((when (not okp)) (mv nil nil nil))
       ((mv okp rest-obligs targets) (match-field-list (cdr inits)
                                                       (cdr sources)
                                                       targets
                                                       ctxt))
       ((when (not okp)) (mv nil nil nil)))
    (mv t (append first-obligs rest-obligs) targets))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initializers-to-variable-substitution ((inits initializer-listp))
  :returns (subst variable-substitutionp)
  :short "Turn a list of initializers into a variable substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each field name is regarded as a variable
     and the corresponding expression is associated to the variable,
     and will replace the variable when the substitution is applied."))
  (cond ((endp inits) nil)
        (t (omap::update (initializer->field (car inits))
                         (initializer->value (car inits))
                         (initializers-to-variable-substitution (cdr inits)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-product-construct-expression ((type identifierp)
                                            (inits initializer-listp)
                                            (inits-result type-resultp)
                                            (expr expressionp)
                                            (ctxt contextp))
  :guard (type-result-case inits-result
                           :err t
                           :ok (= (len inits-result.types) (len inits)))
  :returns (result type-resultp)
  :short "Check if a product construction expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The identifier must be the name of a product type in the context.
     We match the field types calculated for the initializers
     with the field types of the product type.
     If the product type has an invariant,
     we also generate a proof obligation saying that
     the initializers satisfy the invariant.
     The type of the expression is the product type."))
  (type-result-case
   inits-result
   :err (type-result-err inits-result.info)
   :ok (b* ((product (get-type-product (type-defined type)
                                       (context->tops ctxt)))
            ((when (not product))
             (type-result-err (list :product-construct-type-mismatch
                                (identifier-fix type))))
            (fields (type-product->fields product))
            ((mv okp obligs unmatched-fields)
             (match-field-list inits inits-result.types fields ctxt))
            ((when (not okp)) (type-result-err (list :field-type-mismatch
                                                 (identifier-fix type)
                                                 (initializer-list-fix inits)
                                                 fields)))
            ((when (consp unmatched-fields)) (type-result-err
                                              (list :unmatched-fields
                                                (identifier-fix type)
                                                (initializer-list-fix inits)
                                                fields)))
            (inv (type-product->invariant product))
            (inv-oblig?
             (if inv
                 (b* ((subst (initializers-to-variable-substitution inits)))
                   (non-trivial-proof-obligation
                    (context->obligation-vars ctxt)
                    (context->obligation-hyps ctxt)
                    (subst-expression subst inv)
                    expr))
               nil)))
         (make-type-result-ok :types (list (type-defined type))
                              :obligations (append inits-result.obligations
                                                   obligs
                                                   inv-oblig?))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-product-field-expression ((target expressionp)
                                        (target-result type-resultp)
                                        (field identifierp)
                                        (expr expressionp)
                                        (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a product field expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the expression must be a defined product type,
     or a subtype of a defined product type:
     we calculate the maximal supertype of the expression's type,
     and ensure that it is a defined product type;
     since product types are not subtypes,
     calculating the maximal supertype cannot ``skip'' a product type.")
   (xdoc::p
    "We find the type of the field in the product type:
     this is the type of the whole expression.
     No additional proof obligations are generated for this expression."))
  (declare (ignorable expr))
  (type-result-case
   target-result
   :err (type-result-err target-result.info)
   :ok (b* ((type (ensure-single-type target-result.types))
            ((when (not type))
             (type-result-err (list :multi-valued-field-target
                                (expression-fix target)
                                target-result.types)))
            (type (max-supertype type (context->tops ctxt)))
            ((when (not type)) (type-result-err (list :no-max-supertype type)))
            (tprod (get-type-product type (context->tops ctxt)))
            ((when (not tprod))
             (type-result-err (list :product-field-type-mismatch type)))
            (ftype (get-field-type field (type-product->fields tprod)))
            ((when (not ftype))
             (type-result-err (list :no-field-in-product
                                (identifier-fix field)
                                tprod))))
         (make-type-result-ok :types (list ftype)
                              :obligations target-result.obligations)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-product-update-expression ((tname identifierp)
                                         (target expressionp)
                                         (target-result type-resultp)
                                         (fields initializer-listp)
                                         (fields-result type-resultp)
                                         (expr expressionp)
                                         (ctxt contextp))
  :guard (type-result-case fields-result
                           :err t
                           :ok (= (len fields-result.types) (len fields)))
  :returns (result type-resultp)
  :short "Check if a product update expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the target expression must be a deined product type,
     or a subtype of a defined product type:
     we calculate the maximal supertype of the expression's type,
     and ensure that it is a defined product type;
     since product types are not subtypes,
     calculating the maximal supertype cannot ``skip'' a product type.")
   (xdoc::p
    "We match the initializers to the fields of the product type,
     returning an error if there is any mismatch.
     Unlike a product construction expression, there may be unmatched fields:
     in general, a product update expression changes only some of the fields.")
   (xdoc::p
    "If the product type has an invariant, we generate a proof obligation
     saying that the new product type value satisfies the invariant.
     This formula is obtained by substituting, in the invariant,
     the updated field names with the updating expressions,
     and the non-updated field names with
     corresponding product field expressions."))
  (type-result-case
   target-result
   :err (type-result-err target-result.info)
   :ok (type-result-case
        fields-result
        :err (type-result-err fields-result.info)
        :ok (b* ((type (ensure-single-type target-result.types))
                 ((when (not type))
                  (type-result-err (list :multi-valued-field-target
                                     (expression-fix target)
                                     target-result.types)))
                 (type (max-supertype type (context->tops ctxt)))
                 ((when (not type)) (type-result-err (list :no-max-supertype
                                                       type)))
                 (tprod (get-type-product type (context->tops ctxt)))
                 ((when (not tprod))
                  (type-result-err (list :product-update-type-mismatch type)))
                 (target-fields (type-product->fields tprod))
                 ((mv okp obligs unmatched-fields)
                  (match-field-list fields
                                    fields-result.types
                                    target-fields
                                    ctxt))
                 ((when (not okp))
                  (type-result-err (list :field-type-mismatch
                                     type
                                     (initializer-list-fix fields)
                                     unmatched-fields)))
                 (inv (type-product->invariant tprod))
                 (inv-oblig?
                  (if inv
                      (b* ((subst-new
                            (initializers-to-variable-substitution fields))
                           (names (field-list->name-list unmatched-fields))
                           (subst-old
                            (omap::from-lists
                             names
                             (expression-product-field-list tname target names)))
                           (subst (omap::update* subst-new subst-old)))
                        (non-trivial-proof-obligation (context->obligation-vars ctxt)
                                                      (context->obligation-hyps ctxt)
                                                      (subst-expression subst inv)
                                                      expr))
                    nil)))
              (make-type-result-ok :types (list type)
                                   :obligations (append
                                                 fields-result.obligations
                                                 obligs
                                                 inv-oblig?)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sum-construct-expression ((type identifierp)
                                        (alternative identifierp)
                                        (inits initializer-listp)
                                        (inits-result type-resultp)
                                        (expr expressionp)
                                        (ctxt contextp))
  :guard (type-result-case inits-result
                           :err t
                           :ok (= (len inits-result.types) (len inits)))
  :returns (result type-resultp)
  :short "Check if a sum construction expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first identifier must be the name of a sum type in the context.
     The second identifier must be the name of one of the alternatives.
     We retrieve the associated product type
     and we proceed similarly to @(tsee check-product-construct-expression)."))
  (type-result-case
   inits-result
   :err (type-result-err inits-result.info)
   :ok (b* ((sum (get-type-sum (type-defined type) (context->tops ctxt)))
            ((when (not sum))
             (type-result-err (list :sum-construct-type-mismatch
                                (identifier-fix type))))
            (product (get-alternative-product alternative
                                              (type-sum->alternatives sum)))
            ((when (not product))
             (type-result-err (list :sum-construct-no-alternative
                                (identifier-fix type)
                                (identifier-fix alternative))))
            (fields (type-product->fields product))
            ((mv okp obligs unmatched-fields)
             (match-field-list inits inits-result.types fields ctxt))
            ((when (not okp)) (type-result-err (list :field-type-mismatch
                                                 (identifier-fix type)
                                                 (initializer-list-fix inits)
                                                 fields)))
            ((when (consp unmatched-fields)) (type-result-err
                                              (list :unmatched-fields
                                                (identifier-fix type)
                                                (initializer-list-fix inits)
                                                fields)))
            (inv (type-product->invariant product))
            (inv-oblig?
             (if inv
                 (b* ((subst (initializers-to-variable-substitution inits)))
                   (non-trivial-proof-obligation (context->obligation-vars ctxt)
                                                 (context->obligation-hyps ctxt)
                                                 (subst-expression subst inv)
                                                 expr))
               nil)))
         (make-type-result-ok :types (list (type-defined type))
                              :obligations (append inits-result.obligations
                                                   obligs
                                                   inv-oblig?))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sum-field-expression ((tname identifierp)
                                    (target expressionp)
                                    (target-result type-resultp)
                                    (alternative identifierp)
                                    (field identifierp)
                                    (expr expressionp)
(ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a sum field expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the expression must be a defined sum type,
     or a subtype of a defined sum type:
     we calculate the maximal supertype of the expression's type,
     and ensure that it is a defined sum type;
     since sum types are not subtypes,
     calculating the maximal supertype cannot ``skip'' a sum type.")
   (xdoc::p
    "We generate a proof obligation saying that
     the target expression has the specified alternative.")
   (xdoc::p
    "We find the type of the field in the alternative of the sum type:
     this is the type of the whole expression."))
  (type-result-case
   target-result
   :err (type-result-err target-result.info)
   :ok (b* ((type (ensure-single-type target-result.types))
            ((when (not type))
             (type-result-err (list :multi-valued-field-target
                                (expression-fix target)
                                target-result.types)))
            (type (max-supertype type (context->tops ctxt)))
            ((when (not type)) (type-result-err (list :no-max-supertype type)))
            (tsum (get-type-sum type (context->tops ctxt)))
            ((when (not tsum))
             (type-result-err (list :sum-field-type-mismatch type)))
            (oblig? (non-trivial-proof-obligation
                     (context->obligation-vars ctxt)
                     (context->obligation-hyps ctxt)
                     (make-expression-sum-test :type tname
                                               :target target
                                               :alternative alternative)
                     expr))
            (product (get-alternative-product alternative
                                              (type-sum->alternatives tsum)))
            ((when (not product))
             (type-result-err (list :sum-field-no-alternative
                                tsum
                                (identifier-fix alternative))))
            (ftype (get-field-type field (type-product->fields product)))
            ((when (not ftype))
             (type-result-err (list :no-field-in-product
                                (identifier-fix field)
                                product))))
         (make-type-result-ok :types (list ftype)
                              :obligations (append target-result.obligations
                                                   oblig?))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sum-update-expression ((tname identifierp)
                                     (target expressionp)
                                     (target-result type-resultp)
                                     (alternative identifierp)
                                     (inits initializer-listp)
                                     (inits-result type-resultp)
                                     (expr expressionp)
                                     (ctxt contextp))
  :guard (type-result-case inits-result
                           :err t
                           :ok (= (len inits-result.types) (len inits)))
  :returns (result type-resultp)
  :short "Check if a sum update expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee check-product-update-expression),
     but the target expression must be (a subtype of) a sum type,
     and the product type is the one associated to the alternative.
     We also generate a proof obligation saying that
     the sum type value is of the specified alternative."))
  (type-result-case
   target-result
   :err (type-result-err target-result.info)
   :ok (type-result-case
        inits-result
        :err (type-result-err inits-result.info)
        :ok (b* ((type (ensure-single-type target-result.types))
                 ((when (not type))
                  (type-result-err (list :multi-valued-field-target
                                     (expression-fix target)
                                     target-result.types)))
                 (type (max-supertype type (context->tops ctxt)))
                 ((when (not type)) (type-result-err (list :no-max-supertype
                                                       type)))
                 (tsum (get-type-sum type (context->tops ctxt)))
                 ((when (not tsum))
                  (type-result-err (list :sum-update-type-mismatch type)))
                 (oblig? (non-trivial-proof-obligation
                          (context->obligation-vars ctxt)
                          (context->obligation-hyps ctxt)
                          (make-expression-sum-test :type tname
                                                    :target target
                                                    :alternative alternative)
                          expr))
                 (product (get-alternative-product
                           alternative
                           (type-sum->alternatives tsum)))
                 ((when (not product))
                  (type-result-err (list :sum-update-no-alternative
                                     tsum
                                     (identifier-fix alternative))))
                 (fields (type-product->fields product))
                 ((mv okp obligs unmatched-fields)
                  (match-field-list inits
                                    inits-result.types
                                    fields
                                    ctxt))
                 ((when (not okp))
                  (type-result-err (list :field-type-mismatch
                                     type
                                     (initializer-list-fix inits)
                                     unmatched-fields)))
                 (inv (type-product->invariant product))
                 (inv-oblig?
                  (if inv
                      (b* ((subst-new
                            (initializers-to-variable-substitution inits))
                           (names (field-list->name-list unmatched-fields))
                           (subst-old
                            (omap::from-lists
                             names
                             (expression-sum-field-list tname
                                                        target
                                                        alternative
                                                        names)))
                           (subst (omap::update* subst-new subst-old)))
                        (non-trivial-proof-obligation (context->obligation-vars ctxt)
                                                      (context->obligation-hyps ctxt)
                                                      (subst-expression subst inv)
                                                      expr))
                    nil)))
              (make-type-result-ok :types (list type)
                                   :obligations (append
                                                 inits-result.obligations
                                                 oblig?
                                                 obligs
                                                 inv-oblig?)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sum-test-expression ((target expressionp)
                                   (target-result type-resultp)
                                   (alternative identifierp)
                                   (expr expressionp)
                                   (ctxt contextp))
  :returns (result type-resultp)
  :short "Check if a sum test expression is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the target expression must be (a subtype of) a sum type.
     The alternative must be one of that sum type.
     The type of the whole expression is boolean."))
  (declare (ignorable expr))
  (type-result-case
   target-result
   :err (type-result-err target-result.info)
   :ok (b* ((type (ensure-single-type target-result.types))
            ((when (not type))
             (type-result-err (list :multi-valued-sum-test-target
                                (expression-fix target)
                                target-result.types)))
            (type (max-supertype type (context->tops ctxt)))
            ((when (not type)) (type-result-err (list :no-max-supertype type)))
            (tsum (get-type-sum type (context->tops ctxt)))
            ((when (not tsum))
             (type-result-err (list :sum-test-type-mismatch type)))
            (product (get-alternative-product
                      alternative
                      (type-sum->alternatives tsum)))
            ((when (not product))
             (type-result-err (list :sum-test-no-alternative
                                tsum
                                (identifier-fix alternative)))))
         (make-type-result-ok :types (list (type-boolean))
                              :obligations target-result.obligations)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-expression-fns
  :short "Mutually recursive functions for expression checking."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expression ((expr expressionp) (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if an expression is statically well-formed."
    (expression-case
     expr
     :literal (check-literal expr.get)
     :variable (check-variable expr.name ctxt)
     :unary (check-unary-expression expr.operator
                                    expr.operand
                                    (check-expression expr.operand ctxt)
                                    expr ctxt)
     :binary (if (binary-op-strictp expr.operator)
                 (check-strict-binary-expression
                  expr.operator
                  expr.left-operand
                  expr.right-operand
                  (check-expression expr.left-operand ctxt)
                  (check-expression expr.right-operand ctxt)
                  expr
                  ctxt)
               (check-nonstrict-binary-expression expr.operator
                                                  expr.left-operand
                                                  expr.right-operand
                                                  expr
                                                  ctxt))
     :if (check-if/when/unless-expression expr.test nil
                                          expr.then expr.else
                                          expr ctxt)
     :when (check-if/when/unless-expression expr.test nil
                                            expr.then expr.else
                                            expr ctxt)
     :unless (check-if/when/unless-expression expr.test t
                                              expr.then expr.else
                                              expr ctxt)
     :cond (check-cond-expression expr.branches expr ctxt)
     :call (check-call-expression expr.function
                                  expr.types
                                  expr.arguments
                                  (check-expression-list expr.arguments ctxt)
                                  expr ctxt)
     :multi (check-multi-expression expr.arguments
                                    (check-expression-list expr.arguments ctxt))
     :component (check-component-expression expr.multi
                                            (check-expression expr.multi ctxt)
                                            expr.index)
     :bind (check-bind-expression expr.variables expr.value expr.body expr ctxt)
     :product-construct (check-product-construct-expression
                         expr.type
                         expr.fields
                         (check-expression-list
                          (initializer-list->value-list expr.fields)
                          ctxt)
                         expr ctxt)
     :product-field (check-product-field-expression
                     expr.target
                     (check-expression expr.target ctxt)
                     expr.field
                     expr ctxt)
     :product-update (check-product-update-expression
                      expr.type
                      expr.target
                      (check-expression expr.target ctxt)
                      expr.fields
                      (check-expression-list
                       (initializer-list->value-list expr.fields)
                       ctxt)
                      expr ctxt)
     :sum-construct (check-sum-construct-expression
                     expr.type
                     expr.alternative
                     expr.fields
                     (check-expression-list
                      (initializer-list->value-list expr.fields)
                      ctxt)
                     expr ctxt)
     :sum-field (check-sum-field-expression
                 expr.type
                 expr.target
                 (check-expression expr.target ctxt)
                 expr.alternative
                 expr.field
                 expr ctxt)
     :sum-update (check-sum-update-expression
                  expr.type
                  expr.target
                  (check-expression expr.target ctxt)
                  expr.alternative
                  expr.fields
                  (check-expression-list
                   (initializer-list->value-list expr.fields)
                   ctxt)
                  expr ctxt)
     :sum-test (check-sum-test-expression
                expr.target
                (check-expression expr.target ctxt)
                expr.alternative
                expr ctxt)
     :bad-expression (type-result-err (list :explicit-bad-expression
                                            expr.info)))
    :measure (two-nats-measure (expression-count expr) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-nonstrict-binary-expression ((op binary-opp)
                                             (arg1 expressionp)
                                             (arg2 expressionp)
                                             (expr expressionp)
                                             (ctxt contextp))
    :guard (binary-op-nonstrictp op)
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a non-strict binary expression is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "For a conjunction, we first check that the left conjunct is boolean.
       Then we check that the right conjunct is boolean,
       in the context augmented by the left conjucnt.
       That is, in the second conjunct
       we can assume that the first conjunct holds:
       otherwise, the conjunction is already false (non-strictness).")
     (xdoc::p
      "A disjunction is treated similarly to a conjunction,
       except that the context for the second disjunct
       is augmented with the negation of the first disjunct.
       That is, in the second disjunct
       we can assume that the first disjunct does not hold:
       otherwise, the conjunction is already true (non-strictness).")
     (xdoc::p
      "A forward implication is treated the same as a conjunction:
       in the consequent we can assume that the antecedent holds,
       otherwise the implication is already true (non-strictness).")
     (xdoc::p
      "A backward implication is treated the same as a forward implication,
       with the roles of the operands swapped."))
    (declare (ignorable expr))
    (case (binary-op-kind op)
      ((:and :implies)
       (b* ((err-keyword (if (binary-op-case op :and)
                             :type-mismatch-and
                           :type-mismatch-implies))
            (left-result (check-expression arg1 ctxt)))
         (type-result-case
          left-result
          :err (type-result-err left-result.info)
          :ok (b* ((left-type (ensure-single-type left-result.types))
                   ((when (not left-type)) (type-result-err
                                            (list :type-mismatch-multi
                                              (expression-fix arg1)
                                              left-result.types)))
                   ((unless (subtypep left-type
                                      (type-boolean)
                                      (context->tops ctxt)))
                    (type-result-err (list err-keyword
                                           (expression-fix arg1)
                                           left-type
                                           (type-boolean))))
                   (ctxt2 (context-add-condition arg1 ctxt))
                   (right-result (check-expression arg2 ctxt2)))
                (type-result-case
                 right-result
                 :err (type-result-err right-result.info)
                 :ok (b* ((right-type (ensure-single-type right-result.types))
                          ((when (not right-type)) (type-result-err
                                                    (list :type-mismatch-multi
                                                      (expression-fix arg2)
                                                      right-result.types)))
                          ((unless (subtypep right-type
                                             (type-boolean)
                                             (context->tops ctxt)))
                           (type-result-err (list err-keyword
                                                  (expression-fix arg2)
                                                  right-type
                                                  (type-boolean)))))
                       (make-type-result-ok
                        :types (list (type-boolean))
                        :obligations (append left-result.obligations
                                             right-result.obligations))))))))
      (:or
       (b* ((left-result (check-expression arg1 ctxt)))
         (type-result-case
          left-result
          :err (type-result-err left-result.info)
          :ok (b* ((left-type (ensure-single-type left-result.types))
                   ((when (not left-type)) (type-result-err
                                            (list :type-mismatch-multi
                                              (expression-fix arg1)
                                              left-result.types)))
                   ((unless (subtypep left-type
                                      (type-boolean)
                                      (context->tops ctxt)))
                    (type-result-err (list :type-mismatch-or
                                       (expression-fix arg1)
                                       left-type
                                       (type-boolean))))
                   (ctxt2 (context-add-condition (negate-expression arg1) ctxt))
                   (right-result (check-expression arg2 ctxt2)))
                (type-result-case
                 right-result
                 :err (type-result-err right-result.info)
                 :ok (b* ((right-type (ensure-single-type right-result.types))
                          ((when (not right-type)) (type-result-err
                                                    (list :type-mismatch-multi
                                                      (expression-fix arg2)
                                                      right-result.types)))
                          ((unless (subtypep right-type
                                             (type-boolean)
                                             (context->tops ctxt)))
                           (type-result-err (list :type-mismatch-or
                                              (expression-fix arg2)
                                              right-type
                                              (type-boolean)))))
                       (make-type-result-ok
                        :types (list (type-boolean))
                        :obligations (append left-result.obligations
                                             right-result.obligations))))))))
      (:implied
       (b* ((left-result (check-expression arg1 ctxt)))
         (type-result-case
          left-result
          :err (type-result-err left-result.info)
          :ok (b* ((left-type (ensure-single-type left-result.types))
                   ((when (not left-type)) (type-result-err
                                            (list :type-mismatch-multi
                                              (expression-fix arg1)
                                              left-result.types)))
                   ((unless (subtypep left-type
                                      (type-boolean)
                                      (context->tops ctxt)))
                    (type-result-err (list :type-mismatch-implied
                                       (expression-fix arg1)
                                       left-type
                                       (type-boolean))))
                   (ctxt2 (context-add-condition arg1 ctxt))
                   (right-result (check-expression arg2 ctxt2)))
                (type-result-case
                 right-result
                 :err (type-result-err right-result.info)
                 :ok (b* ((right-type (ensure-single-type right-result.types))
                          ((when (not right-type)) (type-result-err
                                                    (list :type-mismatch-multi
                                                      (expression-fix arg2)
                                                      right-result.types)))
                          ((unless (subtypep right-type
                                             (type-boolean)
                                             (context->tops ctxt)))
                           (type-result-err
                            (list :type-mismatch-implied
                              (expression-fix arg2)
                              right-type
                              (type-boolean)))))
                       (make-type-result-ok
                        :types (list (type-boolean))
                        :obligations (append left-result.obligations
                                             right-result.obligations))))))))
      (t (prog2$ (impossible)
                 (type-result-err :impossible))))
    :measure (two-nats-measure (+ (expression-count arg1)
                                  (expression-count arg2))
                               0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-if/when/unless-expression ((test expressionp)
                                           (test-negp booleanp)
                                           (then expressionp)
                                           (else expressionp)
                                           (expr expressionp)
                                           (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if an if/when/unless-then-else expression
            is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We first check the test expression, which must be boolean.
       Then we check the two branch expressions, in contexts augmented with
       (i) the test and its negation when @('test-negp') is @('nil') or
       (ii) the negation of the test and the test otherwise:
       this parameter is @('nil') for an if/when-then-else expression,
       @('t') for an unless-then-else expression;
       that is, the parameter says whether the test should be negated.
       We also ensure that the two branches' types are compatible,
       namely that they have a supremum type (list),
       which is the type (list) of the if-then-else expression."))
    (declare (ignorable expr))
    (b* ((test-result (check-expression test ctxt)))
      (type-result-case
       test-result
       :err (type-result-err test-result.info)
       :ok (b* ((test-type (ensure-single-type test-result.types))
                ((when (not test-type)) (type-result-err
                                         (list :type-mismatch-multi
                                           (expression-fix test)
                                           test-result.types)))
                ((unless (subtypep test-type
                                   (type-boolean)
                                   (context->tops ctxt)))
                 (type-result-err (list :type-mismatch-if-test
                                    (expression-fix test)
                                    test-type
                                    (type-boolean))))
                (ctxt2 (context-add-condition (if test-negp
                                                  (negate-expression test)
                                                test)
                                              ctxt))
                (then-result (check-expression then ctxt2)))
             (type-result-case
              then-result
              :err (type-result-err then-result.info)
              :ok (b* ((ctxt2 (context-add-condition (if test-negp
                                                         test
                                                       (negate-expression test))
                                                     ctxt))
                       (else-result (check-expression else ctxt2)))
                    (type-result-case
                     else-result
                     :err (type-result-err else-result.info)
                     :ok (b* (((mv okp sup) (supremum-type-list
                                             then-result.types
                                             else-result.types
                                             (context->tops ctxt))))
                           (if okp
                               (make-type-result-ok
                                :types sup
                                :obligations (append test-result.obligations
                                                     then-result.obligations
                                                     else-result.obligations))
                             (type-result-err
                              (list :no-type-supremum-in-if
                                (expression-fix then)
                                (expression-fix else)
                                then-result.types
                                else-result.types))))))))))
    :measure (two-nats-measure (+ (expression-count test)
                                  (expression-count then)
                                  (expression-count else))
                               0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-cond-expression ((branches branch-listp) (expr expressionp) (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a conditional expression is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check every branch; see @(tsee check-branch-list).
       In addition, we generate a proof obligation saying that
       the conditions are exhaustive."))
    (b* ((result (check-branch-list branches nil ctxt)))
      (type-result-case
       result
       :err (type-result-err result.info)
       :ok (b* ((oblig? (non-trivial-proof-obligation
                         (context->obligation-vars ctxt)
                         (context->obligation-hyps ctxt)
                         (disjoin-expressions
                          (branch-list->condition-list branches))
                         expr)))
             (make-type-result-ok
              :types result.types
              :obligations (append result.obligations oblig?)))))
    :measure (two-nats-measure (branch-list-count branches) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-bind-expression ((vars typed-variable-listp)
                                 (value expressionp)
                                 (body expressionp)
                                 (expr expressionp)
                                 (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a binding expression is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "First we align the variables and the expressions,
       which also ensures that there is at least one variable.
       We also ensure that there are no duplicate variable names.
       We check the static semantics of the expression bound to the variables,
       and we check whether its types match the variable types,
       which may generate proof obligations.
       We augment the context with the binding,
       and we check the body in this augmented context."))
    (declare (ignorable expr))
    (b* (((mv okp var-names var-types values)
          (align-let-vars-values vars value))
         ((when (not okp)) (type-result-err (list :no-let-variables
                                              (expression-fix value)
                                              (expression-fix body))))
         ((unless (no-duplicatesp-equal var-names))
          (type-result-err (list :duplicate-variable-names var-names)))
         (value-result (check-expression value ctxt)))
      (type-result-case
       value-result
       :err (type-result-err value-result.info)
       :ok (b* (((unless (= (len values) (len value-result.types)))
                 (type-result-err (list :mismatched-let-types
                                    (typed-variable-list-fix vars)
                                    value-result.types)))
                ((mv okp obligs) (match-type-list values
                                                  value-result.types
                                                  var-types
                                                  ctxt))
                ((when (not okp)) (type-result-err (list :let-type-mismatch
                                                     values
                                                     value-result.types
                                                     var-types)))
                (binding (make-binding :variables vars :value value))
                (ctxt (context-add-variables
                       (typed-variables-to-variable-context vars)
                       ctxt))
                (ctxt (context-add-binding binding ctxt))
                (body-result (check-expression body ctxt)))
             (type-result-case
              body-result
              :err (type-result-err body-result.info)
              :ok (make-type-result-ok
                   :types body-result.types
                   :obligations (append value-result.obligations
                                        obligs
                                        body-result.obligations))))))
    :measure (two-nats-measure (+ (expression-count value)
                                  (expression-count body))
                               0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-expression-list ((exprs expression-listp) (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a list of expressions is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We require each expression to be single-valued.
       So the list of types in the type result
       consists of the types of the expressions, in order."))
    (b* (((when (endp exprs))
          (make-type-result-ok :types nil :obligations nil))
         (result (check-expression (car exprs) ctxt)))
      (type-result-case
       result
       :err (type-result-err result.info)
       :ok (b* ((type (ensure-single-type result.types))
                ((when (not type)) (type-result-err
                                    (list :type-mismatch-multi
                                      (expression-fix (car exprs))
                                      result.types)))
                (obligs result.obligations)
                (result (check-expression-list (cdr exprs) ctxt)))
             (type-result-case
              result
              :err (type-result-err result.info)
              :ok (b* ((types result.types)
                       (more-obligs result.obligations))
                    (make-type-result-ok
                     :types (cons type types)
                     :obligations (append obligs more-obligs)))))))
    :measure (two-nats-measure (expression-list-count exprs) 0)
    ///
    (defret len-of-result-types
      (implies (type-result-case result :ok)
               (equal (len (type-result-ok->types result))
                      (len exprs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-branch ((branch branchp) (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a branch is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that the condition is a boolean.
       Then we augment the context with the condition and we check the action,
       whose type is the type of branch."))
    (b* (((branch branch) branch)
         (cond-result (check-expression branch.condition ctxt)))
      (type-result-case
       cond-result
       :err (type-result-err cond-result.info)
       :ok (b* ((cond-type (ensure-single-type cond-result.types))
                ((when (not cond-type)) (type-result-err
                                         (list :type-mismatch-multi
                                           branch.condition
                                           cond-result.types)))
                ((unless (subtypep cond-type
                                   (type-boolean)
                                   (context->tops ctxt)))
                 (type-result-err (list :type-mismatch-condition
                                    branch.condition
                                    cond-type
                                    (type-boolean))))
                (ctxt2 (context-add-condition branch.condition ctxt))
                (act-result (check-expression branch.action ctxt2)))
             (type-result-case
              act-result
              :err (type-result-err act-result.info)
              :ok (make-type-result-ok
                   :types act-result.types
                   :obligations (append cond-result.obligations
                                        act-result.obligations))))))
    :measure (two-nats-measure (branch-count branch) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define check-branch-list ((branches branch-listp)
                             (current-sup type-listp)
                             (ctxt contextp))
    :returns (result type-resultp)
    :parents (static-semantics check-expression-fns)
    :short "Check if a list of branches is statically well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are the branches that form a conditional expression,
       in which the order of the branches is significant.
       This means that each branch is checked in a context
       where the conditions of the preceding branches are negated
       (otherwise one of the preceding branches would be taken).
       Thus, as we process each branch,
       we augment the context with the negation of the branch condition
       just before processing the subsequent branches.")
     (xdoc::p
      "The type of a conditional is the supremum of
       the types of the branches.
       We calculate it by carrying and updating the type supremum
       as we go through the branches:
       this is the @('current-sup') argument of this ACL2 function,
       which is initially @('nil')
       (which cannot be the type list of an expression,
       which must always have one or more types).
       If we reach the end of the branches without a supremum,
       we fail because it means that there are no branches
       (unlike ACL2's @(tsee cond), there is no implicit value returned
       by a Syntheto conditional expression without branches;
       in particular, there is no @('nil') as such in Syntheto).
       When we process the first branch, use it as the supremum.
       When we cannot calculate a supremum (i.e. it does not exist),
       type checking fails."))
    (b* ((current-sup (type-list-fix current-sup))
         ((when (endp branches))
          (if current-sup
              (make-type-result-ok :types current-sup
                                   :obligations nil)
            (type-result-err :empty-conditional)))
         (branch (car branches))
         (result (check-branch branch ctxt)))
      (type-result-case
       result
       :err (type-result-err result.info)
       :ok (b* (((mv okp new-sup) (if current-sup
                                      (supremum-type-list
                                       current-sup
                                       result.types
                                       (context->tops ctxt))
                                    (mv t result.types)))
                ((unless okp)
                 (type-result-err (list :incompatible-branches
                                    current-sup
                                    result.types)))
                (ctxt2 (context-add-condition
                        (negate-expression (branch->condition branch))
                        ctxt))
                (more-result (check-branch-list (cdr branches) new-sup ctxt2)))
             (type-result-case
              more-result
              :err (type-result-err more-result.info)
              :ok (make-type-result-ok
                   :types more-result.types
                   :obligations (append result.obligations
                                        more-result.obligations))))))
    :measure (two-nats-measure (branch-list-count branches) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable binary-op-strictp
                                     binary-op-nonstrictp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork

  ((defrulel termination-lemma-1
     (implies (expression-case expr :binary)
              (< (+ (expression-count (expression-binary->left-operand expr))
                    (expression-count (expression-binary->right-operand expr)))
                 (expression-count expr)))
     :expand ((expression-count expr))
     :rule-classes :linear)

   (defrulel termination-lemma-2
     (implies (expression-case expr :if)
              (< (+ (expression-count (expression-if->test expr))
                    (expression-count (expression-if->then expr))
                    (expression-count (expression-if->else expr)))
                 (expression-count expr)))
     :expand ((expression-count expr))
     :rule-classes :linear)

   (defrulel termination-lemma-3
     (implies (expression-case expr :when)
              (< (+ (expression-count (expression-when->test expr))
                    (expression-count (expression-when->then expr))
                    (expression-count (expression-when->else expr)))
                 (expression-count expr)))
     :expand ((expression-count expr))
     :rule-classes :linear)

   (defrulel termination-lemma-4
     (implies (expression-case expr :unless)
              (< (+ (expression-count (expression-unless->test expr))
                    (expression-count (expression-unless->then expr))
                    (expression-count (expression-unless->else expr)))
                 (expression-count expr)))
     :expand ((expression-count expr))
     :rule-classes :linear)

   (defrulel termination-lemma-5
     (implies (expression-case expr :bind)
              (< (+ (expression-count (expression-bind->value expr))
                    (expression-count (expression-bind->body expr)))
                 (expression-count expr)))
     :expand ((expression-count expr))
     :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below
  ///
  (verify-guards check-expression
    :hints (("Goal" :in-theory (enable binary-op-strictp
                                       binary-op-nonstrictp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual check-expression-fns))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-product ((tprod type-productp) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type product is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type product is always checked as part of a type definition
     (which may or may not be inside a type recursion).
     Thus, the context in which the type product is checked
     may have type names,
     but never has any functions, variables, or obligtion hypotheses.")
   (xdoc::p
    "The fields must have distinct names and well-formed types.
     If there is an invariant expression,
     we check it in the context augmented with
     the typed variables derived from the fields.
     Note that these are used both to create a variable context
     and to create the obligation variables.
     The obligation hypotheses are initially empty.")
   (xdoc::p
    "The expression must return a single boolean value."))
  (b* ((fields (type-product->fields tprod))
       ((unless (no-duplicatesp-equal (field-list->name-list fields)))
        (mv (list :duplicate-field-names (type-product-fix tprod)) nil))
       ((when (not (check-type-list (field-list->type-list fields) ctxt)))
        (mv (list :malformed-types (type-product-fix tprod)) nil))
       (invariant (type-product->invariant tprod))
       ((when (not invariant)) (mv nil nil))
       (tvars (field-list-to-typed-variable-list fields))
       (var-ctxt (typed-variables-to-variable-context tvars))
       (ctxt (change-context ctxt
                             :variables var-ctxt
                             :obligation-vars tvars
                             :obligation-hyps nil))
       (result (check-expression invariant ctxt)))
    (type-result-case
     result
     :err (mv result.info nil)
     :ok (b* ((type (ensure-single-type result.types))
              ((when (not type)) (mv (list :multi-valued-invariant
                                       (type-product-fix tprod))
                                     nil))
              ((unless (subtypep type (type-boolean) (context->tops ctxt)))
               (mv (list :non-boolean-invariant (type-product-fix tprod))
                   nil)))
           (mv nil result.obligations))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-alternative ((alternative alternativep) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type sum alternative is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the underlying product type.
     The guard assumptions on the context are motivated in the same way as
     in @(tsee check-type-product)."))
  (check-type-product (alternative->product alternative) ctxt)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-alternative-list ((alternatives alternative-listp) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Lift @(tsee check-alternative) to lists."
  (b* (((when (endp alternatives)) (mv nil nil))
       ((mv err? obligs) (check-alternative (car alternatives) ctxt))
       ((when err?) (mv err? nil))
       ((mv err? more-obligs) (check-alternative-list (cdr alternatives) ctxt))
       ((when err?) (mv err? nil)))
    (mv nil (append obligs more-obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-sum ((tsum type-sump) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type sum is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard assumptions on the context are motivated
     as in @(tsee check-type-product).")
   (xdoc::p
    "The alternatives must have distinct names
     and be all statically well-formed."))
  (b* ((alternatives (type-sum->alternatives tsum))
       ((unless (no-duplicatesp-equal
                 (alternative-list->name-list alternatives)))
        (mv (list :duplicate-alternative-names (type-sum-fix tsum)) nil)))
    (check-alternative-list alternatives ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-subset ((tsub type-subsetp) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type subset is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard assumptions on the context are motivated
     as in @(tsee check-type-product).")
   (xdoc::p
    "The supertype must be well-formed.
     We check the restriction expression in a context
     with the type subset variable as the only one;
     the expression must be boolean-valued.
     If a witness expression is present,
     we check it in a context with no variables
     (so it has to be a ground expression);
     we ensures it matches the supertype (which may generate proof obligations)
     and we generate a proof obligation saying that
     the expression satisfies the restriction."))
  (b* (((type-subset tsub) tsub)
       ((when (not (check-type tsub.supertype ctxt)))
        (mv (list :malformed-supertype (type-subset-fix tsub)) nil))
       (tvar (make-typed-variable :name tsub.variable :type tsub.supertype))
       (var-ctxt (typed-variables-to-variable-context (list tvar)))
       (ctxt-restr (change-context ctxt
                                   :variables var-ctxt
                                   :obligation-vars (list tvar)
                                   :obligation-hyps nil))
       (result-restr (check-expression tsub.restriction ctxt-restr)))
    (type-result-case
     result-restr
     :err (mv result-restr.info nil)
     :ok (b* ((type (ensure-single-type result-restr.types))
              ((when (not type)) (mv (list :multi-valued-restriction
                                       (type-subset-fix tsub))
                                     nil))
              ((unless (subtypep type (type-boolean) (context->tops ctxt)))
               (mv (list :non-boolean-restriction (type-subset-fix tsub))
                   nil))
              ((when (not tsub.witness)) (mv nil result-restr.obligations))
              (result-wit (check-expression tsub.witness ctxt)))
           (type-result-case
            result-wit
            :err (mv result-wit.info nil)
            :ok (b* ((type (ensure-single-type result-wit.types))
                     ((when (not type)) (mv (list :multi-valued-restriction
                                              (type-subset-fix tsub))
                                            nil))
                     ((mv okp obligs) (match-type tsub.witness
                                                  type
                                                  tsub.supertype
                                                  ctxt))
                     ((when (not okp)) (mv (list :type-mismatch-witness
                                             (type-subset-fix tsub))
                                           nil))
                     (subst (omap::update tsub.variable tsub.witness nil))
                     (formula (subst-expression subst tsub.restriction))
                     (oblig? (non-trivial-proof-obligation nil nil formula
                                                           ;; place holder
                                                           (expression-literal (literal-string "type-subset")))))
                  (mv nil (append result-restr.obligations
                                  result-wit.obligations
                                  obligs
                                  oblig?)))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-definer ((definer type-definerp) (ctxt contextp))
  :guard (and (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type definer is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard assumptions on the context are motivated
     as in @(tsee check-type-product)."))
  (type-definer-case
   definer
   :product (check-type-product definer.get ctxt)
   :sum (check-type-sum definer.get ctxt)
   :subset (check-type-subset definer.get ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-definition ((typedef type-definitionp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type definition (at the top level)
          is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on top-level type definitions;
     we use @(tsee check-type-definition-in-recursion)
     for type definitions in type recursions.")
   (xdoc::p
    "At the top level, the context has no
     types being defined,
     functions being defined,
     variables in scope,
     obligation variables, or
     obligation hypotheses.
     This motivates the extra guard condition of this ACL2 function.")
   (xdoc::p
    "We ensure that the type being defined here is not already defined.
     In order to allow (singly) recursive type definitions,
     we augment the context with the name of the type being defined,
     and then we check the definition body.
     For now we allow any form of recursion,
     but we will add checks to constrain it to be well-formed,
     so that we can generate a termination proof
     when we translate the type definition to ACL2.
     (For now, ACL2 will stop with an error
     if it cannot automatically prove termination."))
  (b* (((type-definition typedef) typedef)
       ((when (get-type-definition typedef.name (context->tops ctxt)))
        (mv (list :type-already-defined typedef.name) nil))
       (ctxt (change-context ctxt
                             :types (cons typedef.name (context->types ctxt)))))
    (check-type-definer typedef.body ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-definition-in-recursion ((typedef type-definitionp)
                                            (ctxt contextp))
  :guard (and (member-equal (type-definition->name typedef)
                            (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type definition in a type recursion
          is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type recursion is a top-level construct
     that immediately contains type definition.
     Thus, when checking a type definition in a type recursion,
     in general the context has no
     functions, variables, obligation variables, or obligation hypotheses.
     However, it will have the names of the recursive types being defined,
     and in particular the one whose definition is checked here;
     see @(tsee check-type-recursion).
     This motivates the extra guard conditions of this ACL2 function.")
   (xdoc::p
    "We ensure that the type is not already defined.
     Unlike @(tsee check-type-definition), we do not augment the context,
     because @(tsee check-type-recursion) already adds the type names."))
  (b* (((type-definition typedef) typedef)
       ((when (get-type-definition typedef.name (context->tops ctxt)))
        (mv (list :type-already-defined typedef.name) nil)))
    (check-type-definer typedef.body ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-definition-list-in-recursion
  ((typedefs type-definition-listp) (ctxt contextp))
  :guard (and (subsetp-equal (type-definition-list->name-list typedefs)
                             (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Lift @(tsee check-type-definition-in-recursion) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Accumulate all the proof obligations."))
  (b* (((when (endp typedefs)) (mv nil nil))
       ((mv err? obligs)
        (check-type-definition-in-recursion (car typedefs) ctxt))
       ((when err?) (mv err? nil))
       ((mv err? more-obligs)
        (check-type-definition-list-in-recursion (cdr typedefs) ctxt))
       ((when err?) (mv err? nil)))
    (mv nil (append obligs more-obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-type-recursion ((typerec type-recursionp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a type recursion is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type recursion is a top-level construct,
     so the context has no
     types or functions being defined,
     no variables in scope,
     and no obligation variables and hypotheses.
     This motivates the guard of this ACL2 function.")
   (xdoc::p
    "We ensure that there are at least two types
     and that their names are all distinct.
     We add the names to the context and we check the type definitions.")
   (xdoc::p
    "For now we allow any form of mutual recursion,
     but we will add check to constrain the allowed forms
     so that we can generate ACL2 termination proofs.
     For now, ACL2 will stop with an error if it cannot prove termination."))
  (b* ((typedefs (type-recursion->definitions typerec))
       (names (type-definition-list->name-list typedefs))
       ((unless (>= (len names) 2))
        (mv (list :type-recursion-with-less-than-two-types typedefs) nil))
       ((unless (no-duplicatesp-equal names))
        (mv (list :duplicate-recursive-types names) nil))
       (ctxt (change-context ctxt :types names)))
    (check-type-definition-list-in-recursion typedefs ctxt))
  :hooks (:fix)
  :prepwork ((local (include-book "std/lists/sets" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-header ((header function-headerp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns err?
  :short "Check if a function header is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "When checking a function header,
     no types are being defined,
     no variables are in scope,
     and no obligation variables and hypotheses are present.
     But there may be (other) function headers,
     which happens when checking mutually recursive functions.")
   (xdoc::p
    "The name must not be the name of an already defined function.
     Input and output types must be well-formed.
     Input and output names must be all distinct."))
  (b* (((function-header header) header)
       ((when (get-function-definition header.name (context->tops ctxt)))
        (list :function-alread-defined header.name))
       (input-types (typed-variable-list->type-list header.inputs))
       ((when (not (check-type-list input-types ctxt)))
        (list :malformed-input-types header.name input-types))
       (output-types (typed-variable-list->type-list header.outputs))
       ((when (not (check-type-list output-types ctxt)))
        (list :malformed-output-types header.name output-types))
       (input-output-names (append
                            (typed-variable-list->name-list header.inputs)
                            (typed-variable-list->name-list header.outputs)))
       ((unless (no-duplicatesp-equal input-output-names))
        (list :duplicate-input/output-names header.name input-output-names)))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-header-list ((headers function-header-listp)
                                    (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns err?
  :short "Check if a list of function headers is statically well-formed."
  (b* (((when (endp headers)) nil)
       (err? (check-function-header (car headers) ctxt))
       ((when err?) err?)
       (err? (check-function-header-list (cdr headers) ctxt))
       ((when err?) err?))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-definer ((definer function-definerp)
                                (output-types type-listp)
                                (fn-name stringp)
                                (ctxt contextp))
  :guard (null (context->types ctxt))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function definer is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The context has no types being defined,
     but it may have functions (if this definer is part of function recursion),
     as well as variables in scope (namely, the function's inputs);
     it may also have obligation hypotheses,
     coming from preconditions.
     This motivates the guard of this ACL2 function.")
   (xdoc::p
    "For a regular function definition,
     we check the body and ensure that its type(s) is
     the same as the function's output type(s).
     This is too strong in general; we will relax this check.")
   (xdoc::p
    "For a quantifier function definition,
     we ensure that the bound variables do not conflict with the inputs;
     we augment the context with those variables and check the matrix,
     ensuring that it returns a single boolean value.
     We ensure also that the output of the function is a boolean."))
  (declare (ignorable fn-name))
  (function-definer-case
   definer
   :regular
   (b* ((result (check-expression definer.body ctxt)))
     (type-result-case
      result
      :err (mv result.info nil)
      :ok (b* ((result1 (match-to-target definer.body result.types output-types ctxt)))
            (type-result-case
             result1
             :err (mv result1.info nil)
             :ok (mv nil (append result.obligations result1.obligations))))))
   :quantified
   (b* ((bound-names (typed-variable-list->name-list definer.variables))
        (free-names (typed-variable-list->name-list
                     (context->obligation-vars ctxt)))
        ((when (intersectp-equal bound-names free-names))
         (mv (list :bound-variables-conflict-with-inputs
               bound-names free-names)
             nil))
        (bound-var-ctxt (typed-variables-to-variable-context definer.variables))
        (ctxt (context-add-variables bound-var-ctxt ctxt))
        (result (check-expression definer.matrix ctxt)))
     (type-result-case
      result
      :err (mv result.info nil)
      :ok (b* ((type (ensure-single-type result.types))
               ((when (not type)) (mv (list :multi-valued-matrix definer.matrix)
                                      nil))
               ((unless (type-equiv type (type-boolean)))
                (mv (list :non-boolean-matrix definer.matrix) nil))
               ((unless (type-list-equiv output-types (list (type-boolean))))
                (mv (list :non-boolean-quantified-output-types
                      (type-list-fix output-types))
                    nil)))
            (mv nil result.obligations)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define function-called-in ((fn-name stringp) expr)
  (member-equal fn-name (functions-called expr)))

(define check-function-definition-top/nontop ((fundef function-definitionp)
                                              (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (member-equal (function-definition->header fundef)
                            (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function definition (at the top level or not)
          is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used both by @(tsee check-function-definition)
     and by @(tsee check-function-definition-in-recursion).")
   (xdoc::p
    "At the top level, the context has no
     types being defined,
     functions being defined,
     variables in scope,
     obligation variables, or
     obligation hypotheses.
     But the caller of this function,
     either  @(tsee check-function-definition)
     or @(tsee check-function-definition-in-recursion),
     extends the context component for the functions being defined;
     thus, this function definition's header is always in the context.
     This motivates the extra guard condition of this ACL2 function.")
   (xdoc::p
    "First we check the header;
     recall that part of that check is that
     no function with that name is already defined.
     We augment the context with the function's inputs.
     If here is a precondition,
     we check it and ensure it returns a boolean,
     and we add the precondition as an obligation hypothesis to the context.
     We check the function's definer.
     We further augment the context with the function outputs.
     If there is a postcondition,
     we check it and ensure it returns a boolean;
     note that we are assuming the precondition (if any)
     in checking the postcondition.
     We also generate a proof obligation saying that the postcondition holds;
     note that the precondition (if any) is in
     the hypotheses of that proof obligation."))
  (b* (((function-definition fundef) fundef)
       (err? (check-function-header fundef.header ctxt))
       (fn-name (identifier->name (function-header->name fundef.header)))
       ((when err?) (mv err? nil))
       (inputs (function-header->inputs fundef.header))
       (outputs (function-header->outputs fundef.header))
       (in-var-ctxt (typed-variables-to-variable-context inputs))
       (ctxt (context-add-variables in-var-ctxt ctxt))
       (ctxt (change-context ctxt :obligation-vars inputs))
       ((mv err? pre-obligs ctxt)
        (if (not fundef.precondition)
            (mv nil nil ctxt)
          (b* ((pre-result (check-expression fundef.precondition ctxt)))
            (type-result-case
             pre-result
             :err (mv pre-result.info nil ctxt)
             :ok (b* ((type (ensure-single-type pre-result.types))
                      ((when (not type))
                       (mv (list :multi-valued-precondition fundef.precondition)
                           nil
                           ctxt))
                      ((unless (type-equiv type (type-boolean)))
                       (mv (list :non-boolean-precondition fundef.precondition)
                           nil
                           ctxt))
                      (ctxt (context-add-condition fundef.precondition ctxt)))
                   (mv nil pre-result.obligations ctxt))))))
       ((when err?) (mv err? nil))
       (output-types (typed-variable-list->type-list outputs))
       ((mv err? def-obligs) (check-function-definer fundef.definer
                                                     output-types
                                                     fn-name
                                                     ctxt))
       ((when err?) (mv err? nil))
       (ctxt (change-context
              ctxt
              :obligation-vars (append
                                (context->obligation-vars ctxt)
                                outputs)))
       ((mv err? post-obligs)
        (if (not fundef.postcondition)
            (mv nil nil)
          (b* ((var-ctxt (typed-variables-to-variable-context outputs))
               (ctxt (context-add-variables var-ctxt ctxt))
               (post-result (check-expression fundef.postcondition ctxt)))
            (type-result-case
             post-result
             :err (mv post-result.info nil)
             :ok (b* ((type (ensure-single-type post-result.types))
                      ((when (not type))
                       (mv (list :multi-valued-postcondition
                             fundef.postcondition)
                           nil))
                      ((unless (type-equiv type (type-boolean)))
                       (mv (list :non-boolean-postcondition
                             fundef.postcondition)
                           nil)))
                   (mv nil post-result.obligations))))))
       ((when err?) (mv err? nil))
       (fn-body (function-definer-case fundef.definer
                                       :regular fundef.definer.body
                                       :quantified nil))
       (recursive-p (function-called-in fn-name fn-body))
       (fn-result-expr (if (and fn-body fundef.postcondition)
                         (if recursive-p
                             (make-expression-call
                              :function (make-identifier :name fn-name)
                              :types () ; Currently nil because user-defined fns are monomorphic
                              :arguments (typed-variable-list->-expression-variable-list inputs))
                           fn-body)
                       nil))
       (oblig? (if fn-result-expr
                   (non-trivial-proof-obligation
                      (context->obligation-vars ctxt)
                      (append (context->obligation-hyps ctxt)
                              (list (obligation-hyp-binding (make-binding :variables outputs
                                                                          :value fn-result-expr))))
                      fundef.postcondition
                      fn-body)
                 nil)))
    (mv nil (append pre-obligs
                    def-obligs
                    post-obligs
                    oblig?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-definition-list ((fundefs function-definition-listp)
                                        (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (subsetp-equal (function-definition-list->header-list fundefs)
                             (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a list of function definitions is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only used on function definitions inside a function recursion,
     i.e. not at the top level."))
  (b* (((when (endp fundefs)) (mv nil nil))
       ((mv err? obligs)
        (check-function-definition-top/nontop (car fundefs) ctxt))
       ((when err?) (mv err? nil))
       ((mv err? more-obligs)
        (check-function-definition-list (cdr fundefs) ctxt))
       ((when err?) (mv err? nil)))
    (mv nil (append obligs more-obligs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-definition ((fundef function-definitionp)
                                   (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function definition (at the top level)
          is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We augment the context with the header
     and call the more general ACL2 function.
     Thus, we allow the function to be (singly) recursive.")
   (xdoc::p
    "For now we allow any recursion, but we will extend this code
     to only allow certain forms,
     or to generate more explicit termination obligations."))
  (b* ((header (function-definition->header fundef))
       (ctxt (change-context ctxt :functions (list header))))
    (check-function-definition-top/nontop fundef ctxt))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-recursion ((funrec function-recursionp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function recursion is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always at the top level, so the context has
     no types or functions being defined,
     no variables in scope,
     and no obligation variables and hypotheses.")
   (xdoc::p
    "We ensure that there are at least two functions,
     otherwise it would not be a mutual recursion.
     We also ensure that the function names are all distinct.
     We add the headers to the context and check all the definitions."))
  (b* ((fundefs (function-recursion->definitions funrec))
       (headers (function-definition-list->header-list fundefs))
       (names (function-header-list->name-list headers))
       ((unless (>= (len names) 2))
        (mv (list :function-recursion-less-than-two-functions fundefs) nil))
       ((unless (no-duplicatesp-equal names))
        (mv (list :duplicate-recursive-functions names) nil))
       (ctxt (change-context ctxt :functions headers)))
    (check-function-definition-list fundefs ctxt))
  :hooks (:fix)
  :prepwork ((local (include-book "std/lists/sets" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-specifier ((spec function-specifierp)
                                  (inputs/outputs typed-variable-listp)
                                  (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function specifier is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "When checking a function specifier, the context has
     no types being defined, no variables in scope,
     and no obligation variable and hypotheses,
     but there may be function headers:
     Ttese all come from the function specification
     that this specifier is contained in.")
   (xdoc::p
    "The @('inputs/outputs') parameter of this ACL2 function
     is non-@('nil') only when the specifier is an input/output one:
     it consists of the inputs and output of the function header
     (there must be exactly one) of the enclosing function specification.")
   (xdoc::p
    "A specification is a predicate,
     so the body must be always boolean-valued.")
   (xdoc::p
    "For a regular function specifier,
     we simply check the body and ensure it is a boolean.
     The use of this kind of function specifier seems quite limited,
     because there are no ordinary (not function) variables in scope:
     it points to the fact that we'll need to extend Syntheto
     with more general second-order functions
     (still representable in ACL2's first-order logic, e.g. via SOFT).")
   (xdoc::p
    "For a quantifier function specifier,
     we augment the context with the bound variables
     and we check the matrix ensuring it is a boolean.")
   (xdoc::p
    "For an input/output function specifier,
     we augment the context with the input/output variables
     and we check the relation ensuring it is a boolean."))
  (function-specifier-case
   spec
   :regular
   (b* ((result (check-expression spec.body ctxt)))
     (type-result-case
      result
      :err (mv result.info nil)
      :ok (if (type-list-equiv result.types (list (type-boolean)))
              (mv nil result.obligations)
            (mv (list :non-boolean-function-specifier-body spec.body)
                nil))))
   :quantified
   (b* ((bound-var-ctxt (typed-variables-to-variable-context spec.variables))
        (ctxt (context-add-variables bound-var-ctxt ctxt))
        (result (check-expression spec.matrix ctxt)))
     (type-result-case
      result
      :err (mv result.info nil)
      :ok (if (type-list-equiv result.types (list (type-boolean)))
              (mv nil result.obligations)
            (mv (list :non-boolean-function-specifier-matrix spec.matrix)
                nil))))
   :input-output
   (b* ((io-var-ctxt (typed-variables-to-variable-context inputs/outputs))
        (ctxt (context-add-variables io-var-ctxt ctxt))
        (ctxt (change-context ctxt :obligation-vars inputs/outputs))
        (result (check-expression spec.relation ctxt)))
     (type-result-case
      result
      :err (mv result.info nil)
      :ok (if (type-list-equiv result.types (list (type-boolean)))
              (mv nil result.obligations)
            (mv (list :non-boolean-function-specifier-relation spec.relation)
                nil)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-function-specification ((spec function-specificationp)
                                      (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a function specification is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at the top level, so the context has no
     type names, function headers, variables, and hypotheses.")
   (xdoc::p
    "We ensure that the name is not already used by
     an existing function specification.")
   (xdoc::p
    "We check all the headers, and augment the context with them.
     We ensure there is at least one header.")
   (xdoc::p
    "If the specifier is an input/output one,
     we ensure that there is exactly one header,
     and we pass its inputs and outputs to
     the ACL2 function that checks the specifier."))
  (b* (((function-specification spec) spec)
       ((when (get-function-definition spec.name (context->tops ctxt)))
        (mv (list :function-specification-already-defined spec.name) nil))
       (names (function-header-list->name-list spec.functions))
       ((unless (consp names))
        (mv (list :no-function-headers-in-specification spec.name) nil))
       ((unless (no-duplicatesp-equal names))
        (mv (list :duplicate-functions-in-specification names) nil))
       (ctxt (change-context ctxt :functions spec.functions)))
    (if (function-specifier-case spec.specifier :input-output)
        (if (= (len spec.functions) 1)
            (b* ((header (car spec.functions))
                 (inputs/outputs (append (function-header->inputs header)
                                         (function-header->outputs header))))
              (check-function-specifier spec.specifier
                                        inputs/outputs
                                        ctxt))
          (mv (list :input-output-specifier-multi-functions names) nil))
      (check-function-specifier spec.specifier nil ctxt)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-theorem ((thm theoremp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a theorem is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at the top level, so the context has no
     type names, function headers, variables, and hypotheses.")
   (xdoc::p
    "We ensure that a theorem with the same name does not already exist.")
   (xdoc::p
    "We extend the context with the variables,
     and we check the formula, ensuring it is a boolean."))
  (b* (((theorem thm) thm)
       ((when (get-theorem thm.name (context->tops ctxt)))
        (mv (list :theorem-already-exists thm.name) nil))
       (var-ctxt (typed-variables-to-variable-context thm.variables))
       (ctxt (change-context ctxt
                             :variables var-ctxt
                             :obligation-vars thm.variables))
       (result (check-expression thm.formula ctxt)))
    (type-result-case
     result
     :err (mv result.info nil)
     :ok (if (type-list-equiv result.types (list (type-boolean)))
             (mv nil result.obligations)
           (mv (list :non-boolean-theorem-formula thm.formula) nil))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; transform

(define args-without-defaults ((arg-info alistp)
                               (default-arg-info alistp))
  (if (endp arg-info)
      ()
    (let ((r (args-without-defaults (cdr arg-info) default-arg-info)))
      (if (assoc-equal (caar arg-info) default-arg-info)
          r
        (cons (caar arg-info) r)))))

(define check-transform-args ((args transform-argument-listp)
                              (arg-info alistp)
                              (default-arg-info alistp)
                              (ctxt contextp))
  :returns err?
  (if (endp args)
      (let ((remaining-required-args (args-without-defaults arg-info default-arg-info)))
        (and remaining-required-args
             (list :missing-fields remaining-required-args)))
    (b* (((transform-argument arg) (car args))
         (arg-name (identifier->name arg.name))
         (this-arg-info (assoc-equal arg-name arg-info))
         ((unless this-arg-info) (list :unknown-transform-field arg-name)))
      (check-transform-args (cdr args) (remove-equal this-arg-info arg-info) default-arg-info ctxt)))
  :hooks (:fix))

(define check-transform ((transform transformp) (ctxt contextp))
  :returns (mv err?
               (obligs proof-obligation-listp))
  (b* (((transform transfm) transform)
       (transfm-name transfm.transform-name)
       (arg-info (assoc-equal transfm-name *transform-argument-table*))
       ((unless arg-info)
        (mv (list :unsupported-transform transfm-name) ()))
       (default-arg-info (assoc-equal transfm-name *transform-argument-defaults-table*))
       (fn-def (get-function-definition transfm.old-function-name (context->tops ctxt)))
       ((unless fn-def)
        (mv (list :function-not-found (identifier->name transfm.old-function-name)) ()))
       (new-fn-def (get-function-definition transfm.new-function-name (context->tops ctxt)))
       ((when new-fn-def)
        (mv (list :function-already-defined (identifier->name transfm.new-function-name)) ()))
       (err? (check-transform-args transfm.arguments (cdr arg-info) (cdr default-arg-info) ctxt))
       ((when err?)
        (mv err? ())))
    (mv nil ()))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-toplevel ((top toplevelp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp)
               (new-ctxt contextp))
  :short "Check if a top-level construct is statically well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the context updated with the top-level construct."))
  (b* (((mv err? obligs)
        (toplevel-case
         top
         :type (check-type-definition top.get ctxt)
         :types (check-type-recursion top.get ctxt)
         :function (check-function-definition top.get ctxt)
         :functions (check-function-recursion top.get ctxt)
         :specification (check-function-specification top.get ctxt)
         :theorem (check-theorem top.get ctxt)
         :transform (check-transform top.get ctxt)))
       ((when err?) (mv err? nil (context-fix ctxt)))
       (new-ctxt (context-add-toplevel top ctxt)))
    (mv nil obligs new-ctxt))
  :hooks (:fix)
  ///

  (defret not-of-check-toplevel-new-ctxt-types
    (not (context->types new-ctxt))
    :hyp (not (context->types ctxt)))

  (defret not-of-check-toplevel-new-ctxt-functions
    (not (context->functions new-ctxt))
    :hyp (not (context->functions ctxt)))

  (defret empty-of-check-toplevel-new-ctxt-variables
    (omap::empty (context->variables new-ctxt))
    :hyp (omap::empty (context->variables ctxt)))

  (defret not-of-check-toplevel-new-ctxt-obligation-vars
    (not (context->obligation-vars new-ctxt))
    :hyp (not (context->obligation-vars ctxt)))

  (defret not-of-check-toplevel-new-ctxt-obligation-hyps
    (not (context->obligation-hyps new-ctxt))
    :hyp (not (context->obligation-hyps ctxt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-toplevel-list ((tops toplevel-listp) (ctxt contextp))
  :guard (and (null (context->types ctxt))
              (null (context->functions ctxt))
              (omap::empty (context->variables ctxt))
              (null (context->obligation-vars ctxt))
              (null (context->obligation-hyps ctxt)))
  :returns (mv err?
               (obligs proof-obligation-listp))
  :short "Check if a list of top-level constructs is statically well-formed."
  (b* (((when (endp tops)) (mv nil nil))
       ((mv err? obligs ctxt) (check-toplevel (car tops) ctxt))
       ((when err?) (mv err? nil))
       ((mv err? more-obligs) (check-toplevel-list (cdr tops) ctxt))
       ((when err?) (mv err? nil)))
    (mv nil (append obligs more-obligs)))
  :hooks (:fix))
