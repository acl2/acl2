; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-matcher")
(include-book "type-equivalence-checker")
(include-book "abstract-syntax-matching-operations")
(include-book "abstract-syntax-structurals")
(include-book "variable-substitution-operations")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable type+ispace-p-when-result-not-error
                          typevar+type-p-when-result-not-error
                          ispacevar+type-p-when-result-not-error
                          ispacevarlist+type-p-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-matcher
  :parents (static-semantics)
  :short "A matcher for types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is matching in the sense of one-sided unification,
     like the @(see ispace-matcher), on which this matcher builds:
     the ispaces in types are matched via the ispace matcher.
     As for ispaces, we will extend this to a full unifier,
     or perhaps we will add a separate unifier.")
   (xdoc::h3
    "Type Matching")
   (xdoc::p
    "We use the following approach to match types.")
   (xdoc::p
    "The difficulty is that equivalent types may have different structures
     (see @(tsee type-equivp)):
     besides containing ispaces,
     which must be matched modulo ispace equivalence,
     a type may be an array or bracket type,
     an atom type may stand for a scalar array type,
     n-ary function, universal, product, and sum types
     stand for nestings of unary ones,
     and bound variables may be renamed.
     So type patterns must be matched modulo type equivalence:
     this is the task of @(tsee type-match), described here.")
   (xdoc::p
    "The key idea is to mirror the structure of @(tsee type-equivp),
     which checks type equivalence,
     with the pattern in the role of the first type
     and the type being matched in the role of the second one,
     and with recursive matches in place of recursive equivalence checks.
     Thus, the type is normalized via @(tsee normalize-type) before matching,
     so that a scalar array type is matched as its element type,
     and an n-ary function type without inputs is matched as its output type;
     array and bracket types are identified,
     and atom types are regarded as scalar array types,
     when matched to pattern array and bracket types,
     with their ispaces matched by the @(see ispace-matcher);
     function types are matched in the curried view, one input at a time,
     so that unary and n-ary function types are identified;
     and universal, product, and sum types are matched in the curried view,
     one bound variable at a time,
     and modulo the renaming of their bound variables, as explained next.
     A pattern variable that is not bound yet is bound to the type,
     while one that is already bound must be equivalent to the type;
     an array-kind pattern variable also matches an atom type,
     which is lifted to a scalar array type
     (see @(tsee type-var-match)).")
   (xdoc::p
    "The variables bound in the pattern are not pattern variables,
     so we cannot just match the body of a binder in the pattern
     to the body of a binder in the type:
     the bound variables may be different,
     and a pattern variable in the body could be bound to
     a type or ispace that mentions the variable bound by the type,
     which has no meaning outside its binder.
     As in @(tsee type-equivp),
     we rename the two bound variables,
     which must have the same kind or sort,
     to a common fresh variable in the two bodies.
     Unlike @(tsee type-equivp),
     we then bind the fresh variable to itself
     in the substitution for its kind or sort,
     so that, while matching the bodies,
     the fresh variable in the pattern matches only itself in the type,
     i.e. it is a rigid variable (see below);
     after matching the bodies, we remove that binding,
     and we check that no pattern variable has been bound
     to a type or ispace that mentions the fresh variable,
     which would be a variable capture:
     for instance, matching @('(Forall (&t) (-> &t &t))')
     to the pattern @('(Forall (&t) (-> &t &s))') fails,
     because @('&s') would have to be the bound variable
     (see @(tsee type-match-type-var-rename),
     @(tsee type-match-type-var-restore),
     @(tsee type-match-ispace-var-rename), and
     @(tsee type-match-ispace-var-restore)).")
   (xdoc::p
    "Since types contain dimension, shape, and type variables,
     the matching builds four substitutions:
     one for dimension variables,
     one for shape variables,
     one for atom-kind type variables, and
     one for array-kind type variables.
     All four are threaded through the matching,
     analogously to the substitutions in the @(see ispace-matcher),
     so that the bindings from earlier matches constrain the current match,
     and all four are meant to be applied simultaneously,
     as @(tsee type-subst-ispace-vars) and @(tsee type-subst-type-vars) do.
     The entry points @(tsee type-match-vars) and @(tsee type-list-match-vars)
     restrict the pattern variables to given ones,
     by binding the other free variables of the pattern to themselves
     before matching,
     which makes them rigid, i.e. matching only themselves,
     and by removing those bindings after matching.")
   (xdoc::p
    "The approach is intended to be sound,
     i.e. a successful match yields substitutions
     that instantiate the pattern to a type
     equivalent to the type being matched,
     and complete modulo type equivalence
     to the extent that @(tsee type-equivp) captures it
     and under the uniqueness restrictions of the @(see ispace-matcher);
     neither has been proved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-subst-self-bind ((vars ispace-var-setp)
                                   (dim-subst string-dim-mapp)
                                   (shape-subst string-shape-mapp))
  :returns (mv (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Bind a set of ispace variables to themselves
          in a dimension substitution and a shape substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each dimension variable in @('vars') is bound,
     in the dimension substitution,
     to the dimension consisting of the variable;
     each shape variable in @('vars') is bound,
     in the shape substitution,
     to the shape consisting of the variable.
     Any existing bindings of those variables are overridden.")
   (xdoc::p
    "This is used to match types under binders of ispace variables;
     see @(tsee type-match)."))
  (b* (((when (set::emptyp (ispace-var-set-fix vars)))
        (mv (string-dim-map-fix dim-subst)
            (string-shape-map-fix shape-subst)))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-self-bind (set::tail vars) dim-subst shape-subst))
       (var (set::head vars)))
    (ispace-var-case
     var
     :dim (mv (omap::update var.name (dim-var var.name) dim-subst)
              shape-subst)
     :shape (mv dim-subst
                (omap::update var.name (shape-var var.name) shape-subst))))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-subst-self-bind ((vars type-var-setp)
                                    (atom-subst string-type-mapp)
                                    (array-subst string-type-mapp))
  :returns (mv (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Bind a set of type variables to themselves
          in an atom-kind and an array-kind type substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each atom-kind type variable in @('vars') is bound,
     in the atom-kind type substitution,
     to the type consisting of the variable;
     each array-kind type variable in @('vars') is bound,
     in the array-kind type substitution,
     to the type consisting of the variable.
     Any existing bindings of those variables are overridden.")
   (xdoc::p
    "This is used to match types under binders of type variables;
     see @(tsee type-match)."))
  (b* (((when (set::emptyp (type-var-set-fix vars)))
        (mv (string-type-map-fix atom-subst)
            (string-type-map-fix array-subst)))
       ((mv atom-subst array-subst)
        (atom/array-subst-self-bind (set::tail vars) atom-subst array-subst))
       (var (set::head vars)))
    (type-var-case
     var
     :atom (mv (omap::update var.name
                             (type-var (type-var-atom var.name))
                             atom-subst)
               array-subst)
     :array (mv atom-subst
                (omap::update var.name
                              (type-var (type-var-array var.name))
                              array-subst))))
  :prepwork ((local (in-theory (enable emptyp-of-type-var-set-fix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var-match ((type typep)
                        (var type-varp)
                        (atom-subst string-type-mapp)
                        (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Match a type to a pattern variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee type-match), which matches types to patterns,
     when the pattern is a variable.
     The type has been normalized by @(tsee type-match)
     (see @(tsee normalize-type)),
     so it is an atom type rather than a scalar array type,
     when equivalent to one.")
   (xdoc::p
    "The kinds are respected.
     An atom-kind pattern variable matches only an atom-kind type.
     An array-kind pattern variable matches any type,
     but an atom-kind type is first lifted to a scalar array type,
     via @(tsee type-ensure-array),
     since Remora allows atom types where array types are expected
     (see @(tsee type)).
     This way, the substitutions always bind
     atom-kind variables to atom-kind types and
     array-kind variables to array-kind types,
     as expected by the rest of the type checker
     (e.g. see @(tsee senv-type-subst)).")
   (xdoc::p
    "The substitution for the kind of the variable is consulted:
     a pattern variable that is bound in the substitution
     matches only a type equivalent to the one bound to it
     (see @(tsee type-equivp));
     a pattern variable that is not bound in the substitution
     matches any type (of the appropriate kind, as explained above),
     which is bound to the variable.
     The substitution for the other kind is unchanged.
     If the matching fails, @('nil') is returned as both substitutions."))
  (b* ((atom-subst (string-type-map-fix atom-subst))
       (array-subst (string-type-map-fix array-subst)))
    (type-var-case
     var
     :atom (b* (((unless (type-atom-kindp type)) (mv nil nil nil))
                (var+type (omap::assoc var.name atom-subst)))
             (cond ((not var+type)
                    (mv t
                        (omap::update var.name (type-fix type) atom-subst)
                        array-subst))
                   ((type-equivp (cdr var+type) type)
                    (mv t atom-subst array-subst))
                   (t (mv nil nil nil))))
     :array (b* ((type (type-ensure-array type))
                 (var+type (omap::assoc var.name array-subst)))
              (cond ((not var+type)
                     (mv t
                         atom-subst
                         (omap::update var.name type array-subst)))
                    ((type-equivp (cdr var+type) type)
                     (mv t atom-subst array-subst))
                    (t (mv nil nil nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-type-var-rename ((pat-param type-varp)
                                    (pat-body typep)
                                    (type-param type-varp)
                                    (type-body typep)
                                    (used type-var-setp)
                                    (atom-subst string-type-mapp)
                                    (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (fresh type-varp)
               (new-pat-body typep)
               (new-type-body typep)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Rename the bound variables
          of a pattern universal type
          and of a universal type
          to a common fresh variable,
          in preparation for matching their bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee type-match)
     to match universal types modulo the renaming of bound variables,
     analogously to @(tsee type-equivp).
     The inputs are the (first) bound variables and the (curried) bodies
     of the pattern and of the type,
     the set of type variables to avoid when generating the fresh variable,
     and the current type substitutions.")
   (xdoc::p
    "The two bound variables must have the same kind; otherwise, we fail.
     We generate a fresh variable of that kind,
     avoiding the variables in @('used'),
     which the caller sets to all the variables of the type and of the pattern,
     and also the free variables of the substitutions:
     these include the fresh variables generated for enclosing binders,
     which are bound to themselves (see below),
     and which must be distinct from the new fresh variable.
     We rename the bound variable of the pattern to the fresh variable
     in the body of the pattern,
     and the bound variable of the type to the fresh variable
     in the body of the type
     (see @(tsee type-rename-type-vars)).
     We bind the fresh variable to itself in the substitutions
     (see @(tsee atom/array-subst-self-bind)),
     so that, when the bodies are matched,
     the fresh variable in the pattern matches only itself in the type,
     as a rigid variable.
     After the bodies are matched,
     @(tsee type-match-type-var-restore) undoes this binding.")
   (xdoc::p
    "The renamed body of the pattern has the same counts as the original one,
     as needed for the termination of @(tsee type-match)."))
  (b* (((unless (equal (type-var-kind pat-param)
                       (type-var-kind type-param)))
        (mv nil
            (type-var-fix pat-param)
            (type-fix pat-body)
            (type-fix type-body)
            nil
            nil))
       (used (set::union
              (type-var-set-fix used)
              (set::union (string-type-map-free-type-vars atom-subst)
                          (string-type-map-free-type-vars array-subst))))
       ((mv fresh new-pat-body new-type-body)
        (type-var-case
         pat-param
         :atom (b* ((fresh (fresh-atom-type-var "_fresh_type_" used))
                    (pat-renam (omap::update pat-param.name
                                             (type-var->name fresh)
                                             nil))
                    (type-renam (omap::update (type-var->name type-param)
                                              (type-var->name fresh)
                                              nil)))
                 (mv fresh
                     (type-rename-type-vars pat-body pat-renam nil)
                     (type-rename-type-vars type-body type-renam nil)))
         :array (b* ((fresh (fresh-array-type-var "_fresh_type_" used))
                     (pat-renam (omap::update pat-param.name
                                              (type-var->name fresh)
                                              nil))
                     (type-renam (omap::update (type-var->name type-param)
                                               (type-var->name fresh)
                                               nil)))
                  (mv fresh
                      (type-rename-type-vars pat-body nil pat-renam)
                      (type-rename-type-vars type-body nil type-renam)))))
       ((mv atom-subst array-subst)
        (atom/array-subst-self-bind (set::insert fresh nil)
                                    atom-subst
                                    array-subst)))
    (mv t fresh new-pat-body new-type-body atom-subst array-subst))

  ///

  (defret type-count-of-type-match-type-var-rename
    (equal (type-count new-pat-body)
           (type-count pat-body)))

  (defret type-binders-count-of-type-match-type-var-rename
    (equal (type-binders-count new-pat-body)
           (type-binders-count pat-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-type-var-restore ((fresh type-varp)
                                     (atom-subst string-type-mapp)
                                     (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Remove the binding of the fresh variable
          after matching the bodies of a pattern universal type
          and of a universal type,
          checking that no pattern variable has captured it."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee type-match)
     after matching the bodies prepared by @(tsee type-match-type-var-rename).
     We remove the binding of the fresh variable to itself
     (see @(tsee atom/array-subst-remove-bound));
     there is no previous binding to restore,
     because the variable is fresh.
     Then we check that the fresh variable does not occur
     in the bindings of the substitutions
     (see @(tsee atom/array-subst-no-type-capture-p)):
     the fresh variable stands for
     the variables bound by the pattern and by the type,
     which have no meaning outside their binders,
     so a pattern variable bound to a type that mentions the fresh variable
     would be a variable capture,
     and the match fails.
     For instance, matching @('(Forall (&t) (-> &t &t))')
     to the pattern @('(Forall (&t) (-> &t &s))') fails,
     because @('&s') would have to be the bound variable."))
  (b* ((vars (set::insert (type-var-fix fresh) nil))
       ((mv atom-subst array-subst)
        (atom/array-subst-remove-bound vars atom-subst array-subst))
       ((unless (atom/array-subst-no-type-capture-p vars
                                                    atom-subst
                                                    array-subst))
        (mv nil nil nil)))
    (mv t atom-subst array-subst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-ispace-var-rename ((pat-param ispace-varp)
                                      (pat-body typep)
                                      (type-param ispace-varp)
                                      (type-body typep)
                                      (used ispace-var-setp)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp)
                                      (atom-subst string-type-mapp)
                                      (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (fresh ispace-varp)
               (new-pat-body typep)
               (new-type-body typep)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Rename the bound variables
          of a pattern product or sum type
          and of a product or sum type
          to a common fresh variable,
          in preparation for matching their bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the analogue of @(tsee type-match-type-var-rename)
     for binders of ispace variables:
     it is used by @(tsee type-match)
     to match product and sum types modulo the renaming of bound variables,
     analogously to @(tsee type-equivp).
     The inputs are the (first) bound variables and the (curried) bodies
     of the pattern and of the type,
     the set of ispace variables to avoid when generating the fresh variable,
     and the current substitutions.")
   (xdoc::p
    "The two bound variables must have the same sort
     (dimension or shape); otherwise, we fail.
     We generate a fresh variable of that sort,
     avoiding the variables in @('used'),
     which the caller sets to all the variables of the type and of the pattern,
     and also the free ispace variables of all the substitutions
     (the types in the type substitutions contain ispaces):
     these include the fresh variables generated for enclosing binders,
     which are bound to themselves (see below),
     and which must be distinct from the new fresh variable.
     We rename the bound variable of the pattern to the fresh variable
     in the body of the pattern,
     and the bound variable of the type to the fresh variable
     in the body of the type
     (see @(tsee type-rename-ispace-vars)).
     We bind the fresh variable to itself
     in the dimension or shape substitution
     (see @(tsee dim/shape-subst-self-bind)),
     so that, when the bodies are matched,
     the fresh variable in the pattern matches only itself in the type,
     as a rigid variable.
     After the bodies are matched,
     @(tsee type-match-ispace-var-restore) undoes this binding.")
   (xdoc::p
    "The renamed body of the pattern has the same counts as the original one,
     as needed for the termination of @(tsee type-match)."))
  (b* (((unless (equal (ispace-var-kind pat-param)
                       (ispace-var-kind type-param)))
        (mv nil
            (ispace-var-fix pat-param)
            (type-fix pat-body)
            (type-fix type-body)
            nil
            nil))
       (used (set::union
              (ispace-var-set-fix used)
              (set::union
               (set::union (string-dim-map-free-ispace-vars dim-subst)
                           (string-shape-map-free-ispace-vars shape-subst))
               (set::union (string-type-map-free-ispace-vars atom-subst)
                           (string-type-map-free-ispace-vars array-subst)))))
       ((mv fresh new-pat-body new-type-body)
        (ispace-var-case
         pat-param
         :dim (b* ((fresh (fresh-dim-ispace-var "_fresh_ispace_" used))
                   (pat-renam (omap::update pat-param.name
                                            (ispace-var->name fresh)
                                            nil))
                   (type-renam (omap::update (ispace-var->name type-param)
                                             (ispace-var->name fresh)
                                             nil)))
                (mv fresh
                    (type-rename-ispace-vars pat-body pat-renam nil)
                    (type-rename-ispace-vars type-body type-renam nil)))
         :shape (b* ((fresh (fresh-shape-ispace-var "_fresh_ispace_" used))
                     (pat-renam (omap::update pat-param.name
                                              (ispace-var->name fresh)
                                              nil))
                     (type-renam (omap::update (ispace-var->name type-param)
                                               (ispace-var->name fresh)
                                               nil)))
                  (mv fresh
                      (type-rename-ispace-vars pat-body nil pat-renam)
                      (type-rename-ispace-vars type-body nil type-renam)))))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-self-bind (set::insert fresh nil)
                                   dim-subst
                                   shape-subst)))
    (mv t fresh new-pat-body new-type-body dim-subst shape-subst))

  ///

  (defret type-count-of-type-match-ispace-var-rename
    (equal (type-count new-pat-body)
           (type-count pat-body)))

  (defret type-binders-count-of-type-match-ispace-var-rename
    (equal (type-binders-count new-pat-body)
           (type-binders-count pat-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-ispace-var-restore ((fresh ispace-varp)
                                       (dim-subst string-dim-mapp)
                                       (shape-subst string-shape-mapp)
                                       (atom-subst string-type-mapp)
                                       (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Remove the binding of the fresh variable
          after matching the bodies of a pattern product or sum type
          and of a product or sum type,
          checking that no pattern variable has captured it."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the analogue of @(tsee type-match-type-var-restore)
     for binders of ispace variables:
     it is used by @(tsee type-match)
     after matching the bodies prepared by
     @(tsee type-match-ispace-var-rename).
     We remove the binding of the fresh variable to itself
     (see @(tsee dim/shape-subst-remove-bound));
     there is no previous binding to restore,
     because the variable is fresh.
     Then we check that the fresh variable does not occur
     in the bindings of any of the substitutions,
     including the type substitutions,
     whose types contain ispaces
     (see @(tsee dim/shape-subst-no-capture-p)
     and @(tsee atom/array-subst-no-ispace-capture-p)):
     the fresh variable stands for
     the variables bound by the pattern and by the type,
     which have no meaning outside their binders,
     so a pattern variable bound to a type or ispace
     that mentions the fresh variable
     would be a variable capture,
     and the match fails.
     For instance, matching @('(Pi ($d) (A Int (dims $d)))')
     to the pattern @('(Pi ($d) *x)') fails,
     because @('*x') would have to mention the bound variable.
     The type substitutions are only checked, not changed,
     so they are not returned."))
  (b* ((vars (set::insert (ispace-var-fix fresh) nil))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-remove-bound vars dim-subst shape-subst))
       ((unless (and (dim/shape-subst-no-capture-p vars
                                                   dim-subst
                                                   shape-subst)
                     (atom/array-subst-no-ispace-capture-p vars
                                                           atom-subst
                                                           array-subst)))
        (mv nil nil nil)))
    (mv t dim-subst shape-subst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match ((type typep)
                    (pat typep)
                    (dim-subst string-dim-mapp)
                    (shape-subst string-shape-mapp)
                    (atom-subst string-type-mapp)
                    (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Match a type to a pattern (another type)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This realizes the approach described in @(see type-matcher).
     We normalize the type via @(tsee normalize-type),
     and then we dispatch on the pattern, as follows.
     If the matching fails, @('nil') is returned as all four substitutions.")
   (xdoc::p
    "A pattern variable is matched via @(tsee type-var-match).")
   (xdoc::p
    "A pattern base type matches only the same base type.")
   (xdoc::p
    "A pattern array or bracket type matches
     an array or bracket type, in either summand,
     or an atom type, regarded as a scalar array type:
     we use @(tsee type-match-array) to obtain
     the element type and the ispace of the type
     (this fails on an array type variable, which thus does not match),
     and we match them to the element type and the ispace of the pattern,
     where the ispaces of a bracket pattern are combined
     into a single shape ispace, as @(tsee type-match-array) does.
     The ispaces are matched via the @(see ispace-matcher),
     modulo ispace equivalence.")
   (xdoc::p
    "A pattern function type, unary or n-ary,
     matches a function type, unary or n-ary,
     in the curried view of function types
     (see @(tsee fun-curried-out) and @(tsee type-equivp)):
     the first input type of the type must match
     the first input type of the pattern,
     and the rest of the type must match the rest of the pattern,
     where the rest of a function type is
     its output type if it has one input,
     or otherwise the function type over the remaining inputs.
     Thus, a unary function type may match an n-ary pattern, and vice versa,
     and n-ary function types with different numbers of inputs may match.
     An n-ary pattern without inputs stands for its output type,
     which is matched to the type.")
   (xdoc::p
    "A pattern universal type, unary or n-ary,
     matches a universal type, unary or n-ary,
     in the curried view of universal types
     (see @(tsee type-match-forall) and @(tsee type-equivp)):
     one bound variable is peeled off from the type and from the pattern,
     the two variables must have the same kind,
     and the rest of the type must match the rest of the pattern,
     after renaming both variables to a common fresh variable,
     as explained in @(see type-matcher).
     Thus, a unary universal type may match an n-ary pattern, and vice versa,
     and n-ary universal types with different numbers of bound variables
     may match.")
   (xdoc::p
    "A pattern product or sum type, unary or n-ary,
     matches a product or sum type (respectively), unary or n-ary,
     in the curried view of product and sum types
     (see @(tsee type-equivp)):
     one bound variable is peeled off from the type
     (via @(tsee type-match-product),
     or via @(tsee type-match-sum) and @(tsee sigma-curried-body))
     and from the pattern,
     the two variables must have the same sort,
     and the rest of the type must match the rest of the pattern,
     after renaming both variables to a common fresh variable,
     as explained in @(see type-matcher).
     Thus, a unary product or sum type may match an n-ary pattern,
     and vice versa,
     and n-ary product or sum types
     with different numbers of bound variables may match."))
  (b* ((type (normalize-type type)))
    (type-case
     pat
     :var (b* (((mv okp atom-subst array-subst)
                (type-var-match type pat.var atom-subst array-subst))
               ((unless okp) (mv nil nil nil nil nil)))
            (mv t
                (string-dim-map-fix dim-subst)
                (string-shape-map-fix shape-subst)
                atom-subst
                array-subst))
     :base (if (equal type (type-base pat.type))
               (mv t
                   (string-dim-map-fix dim-subst)
                   (string-shape-map-fix shape-subst)
                   (string-type-map-fix atom-subst)
                   (string-type-map-fix array-subst))
             (mv nil nil nil nil nil))
     :array (b* ((array (type-match-array type))
                 ((when (reserrp array)) (mv nil nil nil nil nil))
                 ((type+ispace array) array)
                 ((mv okp dim-subst shape-subst atom-subst array-subst)
                  (type-match array.type
                              pat.elem
                              dim-subst
                              shape-subst
                              atom-subst
                              array-subst))
                 ((unless okp) (mv nil nil nil nil nil))
                 ((mv okp dim-subst shape-subst)
                  (ispace-match array.ispace
                                pat.ispace
                                dim-subst
                                shape-subst))
                 ((unless okp) (mv nil nil nil nil nil)))
              (mv t dim-subst shape-subst atom-subst array-subst))
     :bracket (b* ((array (type-match-array type))
                   ((when (reserrp array)) (mv nil nil nil nil nil))
                   ((type+ispace array) array)
                   ((mv okp dim-subst shape-subst atom-subst array-subst)
                    (type-match array.type
                                pat.elem
                                dim-subst
                                shape-subst
                                atom-subst
                                array-subst))
                   ((unless okp) (mv nil nil nil nil nil))
                   ((mv okp dim-subst shape-subst)
                    (ispace-match array.ispace
                                  (ispace-shape
                                   (shape-append
                                    (shape-list-from-ispace-list pat.ispaces)))
                                  dim-subst
                                  shape-subst))
                   ((unless okp) (mv nil nil nil nil nil)))
                (mv t dim-subst shape-subst atom-subst array-subst))
     :fun (cond
           ((type-case type :fun)
            (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                  (type-match (type-fun->in type)
                              pat.in
                              dim-subst
                              shape-subst
                              atom-subst
                              array-subst))
                 ((unless okp) (mv nil nil nil nil nil)))
              (type-match (type-fun->out type)
                          pat.out
                          dim-subst
                          shape-subst
                          atom-subst
                          array-subst)))
           ((and (type-case type :funn)
                 (consp (type-funn->in type)))
            (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                  (type-match (car (type-funn->in type))
                              pat.in
                              dim-subst
                              shape-subst
                              atom-subst
                              array-subst))
                 ((unless okp) (mv nil nil nil nil nil)))
              (type-match (fun-curried-out (type-funn->in type)
                                           (type-funn->out type))
                          pat.out
                          dim-subst
                          shape-subst
                          atom-subst
                          array-subst)))
           (t (mv nil nil nil nil nil)))
     :funn (cond
            ((endp pat.in)
             (type-match type
                         pat.out
                         dim-subst
                         shape-subst
                         atom-subst
                         array-subst))
            ((type-case type :fun)
             (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                   (type-match (type-fun->in type)
                               (car pat.in)
                               dim-subst
                               shape-subst
                               atom-subst
                               array-subst))
                  ((unless okp) (mv nil nil nil nil nil)))
               (type-match (type-fun->out type)
                           (fun-curried-out pat.in pat.out)
                           dim-subst
                           shape-subst
                           atom-subst
                           array-subst)))
            ((and (type-case type :funn)
                  (consp (type-funn->in type)))
             (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                   (type-match (car (type-funn->in type))
                               (car pat.in)
                               dim-subst
                               shape-subst
                               atom-subst
                               array-subst))
                  ((unless okp) (mv nil nil nil nil nil)))
               (type-match (fun-curried-out (type-funn->in type)
                                            (type-funn->out type))
                           (fun-curried-out pat.in pat.out)
                           dim-subst
                           shape-subst
                           atom-subst
                           array-subst)))
            (t (mv nil nil nil nil nil)))
     :forall (b* ((var+type (type-match-forall type))
                  ((when (reserrp var+type)) (mv nil nil nil nil nil))
                  ((typevar+type var+type) var+type)
                  ((mv okp fresh pat-body type-body atom-subst1 array-subst1)
                   (type-match-type-var-rename pat.param
                                               pat.body
                                               var+type.var
                                               var+type.type
                                               (set::union
                                                (type-all-type-vars type)
                                                (type-all-type-vars pat))
                                               atom-subst
                                               array-subst))
                  ((unless okp) (mv nil nil nil nil nil))
                  ((mv okp dim-subst shape-subst atom-subst1 array-subst1)
                   (type-match type-body
                               pat-body
                               dim-subst
                               shape-subst
                               atom-subst1
                               array-subst1))
                  ((unless okp) (mv nil nil nil nil nil))
                  ((mv okp atom-subst array-subst)
                   (type-match-type-var-restore fresh
                                                atom-subst1
                                                array-subst1))
                  ((unless okp) (mv nil nil nil nil nil)))
               (mv t dim-subst shape-subst atom-subst array-subst))
     :foralln (b* ((var+type (type-match-forall type))
                   ((when (reserrp var+type)) (mv nil nil nil nil nil))
                   ((typevar+type var+type) var+type)
                   ((mv okp fresh pat-body type-body atom-subst1 array-subst1)
                    (type-match-type-var-rename (car pat.params)
                                                (forall-curried-body pat.params
                                                                     pat.body)
                                                var+type.var
                                                var+type.type
                                                (set::union
                                                 (type-all-type-vars type)
                                                 (type-all-type-vars pat))
                                                atom-subst
                                                array-subst))
                   ((unless okp) (mv nil nil nil nil nil))
                   ((mv okp dim-subst shape-subst atom-subst1 array-subst1)
                    (type-match type-body
                                pat-body
                                dim-subst
                                shape-subst
                                atom-subst1
                                array-subst1))
                   ((unless okp) (mv nil nil nil nil nil))
                   ((mv okp atom-subst array-subst)
                    (type-match-type-var-restore fresh
                                                 atom-subst1
                                                 array-subst1))
                   ((unless okp) (mv nil nil nil nil nil)))
                (mv t dim-subst shape-subst atom-subst array-subst))
     :pi (b* ((var+type (type-match-product type))
              ((when (reserrp var+type)) (mv nil nil nil nil nil))
              ((ispacevar+type var+type) var+type)
              ((mv okp fresh pat-body type-body dim-subst1 shape-subst1)
               (type-match-ispace-var-rename pat.param
                                             pat.body
                                             var+type.var
                                             var+type.type
                                             (set::union
                                              (type-all-ispace-vars type)
                                              (type-all-ispace-vars pat))
                                             dim-subst
                                             shape-subst
                                             atom-subst
                                             array-subst))
              ((unless okp) (mv nil nil nil nil nil))
              ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
               (type-match type-body
                           pat-body
                           dim-subst1
                           shape-subst1
                           atom-subst
                           array-subst))
              ((unless okp) (mv nil nil nil nil nil))
              ((mv okp dim-subst shape-subst)
               (type-match-ispace-var-restore fresh
                                              dim-subst1
                                              shape-subst1
                                              atom-subst
                                              array-subst))
              ((unless okp) (mv nil nil nil nil nil)))
           (mv t dim-subst shape-subst atom-subst array-subst))
     :pin (b* ((var+type (type-match-product type))
               ((when (reserrp var+type)) (mv nil nil nil nil nil))
               ((ispacevar+type var+type) var+type)
               ((mv okp fresh pat-body type-body dim-subst1 shape-subst1)
                (type-match-ispace-var-rename (car pat.params)
                                              (pi-curried-body pat.params
                                                               pat.body)
                                              var+type.var
                                              var+type.type
                                              (set::union
                                               (type-all-ispace-vars type)
                                               (type-all-ispace-vars pat))
                                              dim-subst
                                              shape-subst
                                              atom-subst
                                              array-subst))
               ((unless okp) (mv nil nil nil nil nil))
               ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                (type-match type-body
                            pat-body
                            dim-subst1
                            shape-subst1
                            atom-subst
                            array-subst))
               ((unless okp) (mv nil nil nil nil nil))
               ((mv okp dim-subst shape-subst)
                (type-match-ispace-var-restore fresh
                                               dim-subst1
                                               shape-subst1
                                               atom-subst
                                               array-subst))
               ((unless okp) (mv nil nil nil nil nil)))
            (mv t dim-subst shape-subst atom-subst array-subst))
     :sigma (b* ((vars+type (type-match-sum type))
                 ((when (reserrp vars+type)) (mv nil nil nil nil nil))
                 ((ispacevarlist+type vars+type) vars+type)
                 ((mv okp fresh pat-body type-body dim-subst1 shape-subst1)
                  (type-match-ispace-var-rename pat.param
                                                pat.body
                                                (car vars+type.vars)
                                                (sigma-curried-body
                                                 vars+type.vars
                                                 vars+type.type)
                                                (set::union
                                                 (type-all-ispace-vars type)
                                                 (type-all-ispace-vars pat))
                                                dim-subst
                                                shape-subst
                                                atom-subst
                                                array-subst))
                 ((unless okp) (mv nil nil nil nil nil))
                 ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                  (type-match type-body
                              pat-body
                              dim-subst1
                              shape-subst1
                              atom-subst
                              array-subst))
                 ((unless okp) (mv nil nil nil nil nil))
                 ((mv okp dim-subst shape-subst)
                  (type-match-ispace-var-restore fresh
                                                 dim-subst1
                                                 shape-subst1
                                                 atom-subst
                                                 array-subst))
                 ((unless okp) (mv nil nil nil nil nil)))
              (mv t dim-subst shape-subst atom-subst array-subst))
     :sigman (b* ((vars+type (type-match-sum type))
                  ((when (reserrp vars+type)) (mv nil nil nil nil nil))
                  ((ispacevarlist+type vars+type) vars+type)
                  ((mv okp fresh pat-body type-body dim-subst1 shape-subst1)
                   (type-match-ispace-var-rename (car pat.params)
                                                 (sigma-curried-body
                                                  pat.params
                                                  pat.body)
                                                 (car vars+type.vars)
                                                 (sigma-curried-body
                                                  vars+type.vars
                                                  vars+type.type)
                                                 (set::union
                                                  (type-all-ispace-vars type)
                                                  (type-all-ispace-vars pat))
                                                 dim-subst
                                                 shape-subst
                                                 atom-subst
                                                 array-subst))
                  ((unless okp) (mv nil nil nil nil nil))
                  ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                   (type-match type-body
                               pat-body
                               dim-subst1
                               shape-subst1
                               atom-subst
                               array-subst))
                  ((unless okp) (mv nil nil nil nil nil))
                  ((mv okp dim-subst shape-subst)
                   (type-match-ispace-var-restore fresh
                                                  dim-subst1
                                                  shape-subst1
                                                  atom-subst
                                                  array-subst))
                  ((unless okp) (mv nil nil nil nil nil)))
               (mv t dim-subst shape-subst atom-subst array-subst))))
  :measure (two-nats-measure (type-count pat) (type-binders-count pat))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match ((types type-listp)
                         (pats type-listp)
                         (dim-subst string-dim-mapp)
                         (shape-subst string-shape-mapp)
                         (atom-subst string-type-mapp)
                         (array-subst string-type-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Match a list of types to a list of patterns (other types)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and each type must match the corresponding pattern,
     with the substitutions threaded through the successive matches."))
  (b* (((when (endp pats))
        (if (endp types)
            (mv t
                (string-dim-map-fix dim-subst)
                (string-shape-map-fix shape-subst)
                (string-type-map-fix atom-subst)
                (string-type-map-fix array-subst))
          (mv nil nil nil nil nil)))
       ((when (endp types)) (mv nil nil nil nil nil))
       ((mv okp dim-subst shape-subst atom-subst array-subst)
        (type-match (car types)
                    (car pats)
                    dim-subst
                    shape-subst
                    atom-subst
                    array-subst))
       ((unless okp) (mv nil nil nil nil nil)))
    (type-list-match (cdr types)
                     (cdr pats)
                     dim-subst
                     shape-subst
                     atom-subst
                     array-subst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-vars ((type typep)
                         (pat typep)
                         (ivars ispace-var-setp)
                         (tvars type-var-setp))
  :returns (mv (okp booleanp)
               (dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp)
               (atom-subst string-type-mapp)
               (array-subst string-type-mapp))
  :short "Match a type to a pattern (another type),
          with respect to given pattern variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee type-match),
     but the pattern variables are exactly
     the ispace variables in @('ivars') and the type variables in @('tvars'):
     any other free variable of the pattern is rigid,
     i.e. it matches only itself.
     The substitutions are initially empty.")
   (xdoc::p
    "We achieve this by binding the rigid variables to themselves
     (via @(tsee dim/shape-subst-self-bind)
     and @(tsee atom/array-subst-self-bind))
     before the matching,
     and by removing them from the resulting substitutions
     (via @(tsee dim/shape-subst-remove-bound)
     and @(tsee atom/array-subst-remove-bound))
     after the matching.
     Thus, the resulting substitutions only bind pattern variables;
     a pattern variable that does not occur free in the pattern
     is not bound in the resulting substitutions.")
   (xdoc::p
    "The kind rules of @(tsee type-var-match) apply to rigid variables too:
     e.g. a rigid array-kind variable does not match an atom-kind type,
     because the type is lifted to a scalar array type,
     which differs from the variable."))
  (b* ((rigid-ivars (set::difference (type-free-ispace-vars pat)
                                     (ispace-var-set-fix ivars)))
       (rigid-tvars (set::difference (type-free-type-vars pat)
                                     (type-var-set-fix tvars)))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-self-bind rigid-ivars nil nil))
       ((mv atom-subst array-subst)
        (atom/array-subst-self-bind rigid-tvars nil nil))
       ((mv okp dim-subst shape-subst atom-subst array-subst)
        (type-match type pat dim-subst shape-subst atom-subst array-subst))
       ((unless okp) (mv nil nil nil nil nil))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-remove-bound rigid-ivars dim-subst shape-subst))
       ((mv atom-subst array-subst)
        (atom/array-subst-remove-bound rigid-tvars atom-subst array-subst)))
    (mv t dim-subst shape-subst atom-subst array-subst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match-vars ((types type-listp)
                              (pats type-listp)
                              (ivars ispace-var-setp)
                              (tvars type-var-setp))
  :returns (mv (okp booleanp)
               (dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp)
               (atom-subst string-type-mapp)
               (array-subst string-type-mapp))
  :short "Match a list of types to a list of patterns (other types),
          with respect to given pattern variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee type-list-match),
     but with the pattern variables restricted to the given ones,
     as in @(tsee type-match-vars); see that function for details.
     The rigid variables are the free variables of all the patterns,
     other than the pattern variables."))
  (b* ((rigid-ivars (set::difference (type-list-free-ispace-vars pats)
                                     (ispace-var-set-fix ivars)))
       (rigid-tvars (set::difference (type-list-free-type-vars pats)
                                     (type-var-set-fix tvars)))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-self-bind rigid-ivars nil nil))
       ((mv atom-subst array-subst)
        (atom/array-subst-self-bind rigid-tvars nil nil))
       ((mv okp dim-subst shape-subst atom-subst array-subst)
        (type-list-match types
                         pats
                         dim-subst
                         shape-subst
                         atom-subst
                         array-subst))
       ((unless okp) (mv nil nil nil nil nil))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-remove-bound rigid-ivars dim-subst shape-subst))
       ((mv atom-subst array-subst)
        (atom/array-subst-remove-bound rigid-tvars atom-subst array-subst)))
    (mv t dim-subst shape-subst atom-subst array-subst)))
