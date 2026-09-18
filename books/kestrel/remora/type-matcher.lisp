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
(include-book "abstract-syntax-structurals")
(include-book "variable-substitution-operations")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

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
     or perhaps we will add a separate unifier."))
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
     see @(tsee types-match)."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-subst-restore-bound ((vars ispace-var-setp)
                                       (old-dim-subst string-dim-mapp)
                                       (old-shape-subst string-shape-mapp)
                                       (dim-subst string-dim-mapp)
                                       (shape-subst string-shape-mapp))
  :returns (mv (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Restore the bindings of a set of ispace variables
          in a dimension substitution and a shape substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each dimension variable in @('vars'),
     its binding in the old dimension substitution, if any,
     replaces its binding in the dimension substitution,
     which is instead removed
     if the variable has no binding in the old dimension substitution;
     similarly for each shape variable in @('vars')
     and the shape substitutions.")
   (xdoc::p
    "This undoes @(tsee dim/shape-subst-self-bind),
     after matching types under binders of ispace variables;
     see @(tsee types-match)."))
  (b* (((when (set::emptyp (ispace-var-set-fix vars)))
        (mv (string-dim-map-fix dim-subst)
            (string-shape-map-fix shape-subst)))
       ((mv dim-subst shape-subst)
        (dim/shape-subst-restore-bound (set::tail vars)
                                       old-dim-subst
                                       old-shape-subst
                                       dim-subst
                                       shape-subst))
       (var (set::head vars)))
    (ispace-var-case
     var
     :dim (b* ((old-dim-subst (string-dim-map-fix old-dim-subst))
               (var+dim (omap::assoc var.name old-dim-subst)))
            (mv (if var+dim
                    (omap::update var.name (cdr var+dim) dim-subst)
                  (omap::delete var.name dim-subst))
                shape-subst))
     :shape (b* ((old-shape-subst (string-shape-map-fix old-shape-subst))
                 (var+shape (omap::assoc var.name old-shape-subst)))
              (mv dim-subst
                  (if var+shape
                      (omap::update var.name (cdr var+shape) shape-subst)
                    (omap::delete var.name shape-subst))))))
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
     see @(tsee types-match)."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-subst-restore-bound ((vars type-var-setp)
                                        (old-atom-subst string-type-mapp)
                                        (old-array-subst string-type-mapp)
                                        (atom-subst string-type-mapp)
                                        (array-subst string-type-mapp))
  :returns (mv (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Restore the bindings of a set of type variables
          in an atom-kind and an array-kind type substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each atom-kind type variable in @('vars'),
     its binding in the old atom-kind type substitution, if any,
     replaces its binding in the atom-kind type substitution,
     which is instead removed
     if the variable has no binding in the old atom-kind type substitution;
     similarly for each array-kind type variable in @('vars')
     and the array-kind type substitutions.")
   (xdoc::p
    "This undoes @(tsee atom/array-subst-self-bind),
     after matching types under binders of type variables;
     see @(tsee types-match)."))
  (b* (((when (set::emptyp (type-var-set-fix vars)))
        (mv (string-type-map-fix atom-subst)
            (string-type-map-fix array-subst)))
       ((mv atom-subst array-subst)
        (atom/array-subst-restore-bound (set::tail vars)
                                        old-atom-subst
                                        old-array-subst
                                        atom-subst
                                        array-subst))
       (var (set::head vars)))
    (type-var-case
     var
     :atom (b* ((old-atom-subst (string-type-map-fix old-atom-subst))
                (var+type (omap::assoc var.name old-atom-subst)))
             (mv (if var+type
                     (omap::update var.name (cdr var+type) atom-subst)
                   (omap::delete var.name atom-subst))
                 array-subst))
     :array (b* ((old-array-subst (string-type-map-fix old-array-subst))
                 (var+type (omap::assoc var.name old-array-subst)))
              (mv atom-subst
                  (if var+type
                      (omap::update var.name (cdr var+type) array-subst)
                    (omap::delete var.name array-subst))))))
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
     when the pattern is a variable.")
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
     matches only the type bound to it;
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
                   ((equal (cdr var+type) (type-fix type))
                    (mv t atom-subst array-subst))
                   (t (mv nil nil nil))))
     :array (b* ((type (type-ensure-array type))
                 (var+type (omap::assoc var.name array-subst)))
              (cond ((not var+type)
                     (mv t
                         atom-subst
                         (omap::update var.name type array-subst)))
                    ((equal (cdr var+type) type)
                     (mv t atom-subst array-subst))
                    (t (mv nil nil nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-match
  :short "Match types to patterns (other types)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we perform a purely syntactical match,
     as in the @(see ispace-matcher),
     which is incomplete with respect to type equivalence
     (see @(tsee type-equivp)):
     for instance, there is no normalization of scalar types,
     no currying of n-ary function, universal, product, and sum types
     (which are thus distinct from the unary ones),
     and no renaming of bound variables.
     We will need to extend this to matching modulo equivalence.
     The only exception to the purely syntactical treatment is
     the lifting of atom types to scalar array types
     at array-kind pattern variables,
     explained in @(tsee type-var-match).")
   (xdoc::p
    "Since types contain dimension, shape, and type variables,
     the matching builds four substitutions:
     one for dimension variables,
     one for shape variables,
     one for atom-kind type variables, and
     one for array-kind type variables.
     All four are threaded through these functions,
     analogously to the substitutions in the @(see ispace-matcher),
     and all four are meant to be applied simultaneously,
     as @(tsee type-subst-ispace-vars) and @(tsee type-subst-type-vars) do.
     If the matching fails, @('nil') is returned as all four substitutions.")
   (xdoc::p
    "The pattern variables are the free variables of the patterns.
     The variables bound in the patterns,
     by universal, product, and sum types,
     are not pattern variables:
     since the matching is syntactical,
     a bound variable matches only the same variable,
     bound by the same binder.
     We achieve this by binding each bound variable to itself,
     in the appropriate substitution,
     while matching the body of the binder
     (see @(tsee atom/array-subst-self-bind)
     and @(tsee dim/shape-subst-self-bind)),
     so that the occurrences of the variable in the body of the pattern
     match only the same variable in the body of the type;
     after matching the body,
     we restore the binding that the variable had before the binder, if any
     (see @(tsee atom/array-subst-restore-bound)
     and @(tsee dim/shape-subst-restore-bound)).")
   (xdoc::p
    "We do not check for variable capture:
     a pattern variable may be bound to a type or ispace
     that contains a variable bound, in the type being matched,
     at the occurrence of the pattern variable.
     For instance, matching @('(Forall (&t) (-> &t &t))')
     to the pattern @('(Forall (&t) (-> &t &s))')
     binds @('&s') to @('&t').
     The resulting substitutions should be checked for capture
     via the no-capture predicates,
     as with the substitution operations;
     we will revisit this when extending the matching."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    :parents (type-matcher types-match)
    :short "Match a type to a pattern (another type)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A pattern variable is matched via @(tsee type-var-match).")
     (xdoc::p
      "A pattern base type matches only the same base type.")
     (xdoc::p
      "A pattern array type matches only an array type
       whose element type and ispace match the ones of the pattern;
       similarly for bracket types, with lists of ispaces.
       The ispaces are matched via the @(see ispace-matcher).")
     (xdoc::p
      "A pattern function type matches only
       a function type of the same form (unary or n-ary)
       whose input type(s) and output type match the ones of the pattern.")
     (xdoc::p
      "A pattern universal, product, or sum type matches only
       a type of the same form (unary or n-ary)
       with the same bound variable(s)
       and whose body matches the body of the pattern,
       with the bound variable(s) bound to themselves
       as explained in @(tsee types-match)."))
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
     :base (if (equal (type-fix type) (type-base pat.type))
               (mv t
                   (string-dim-map-fix dim-subst)
                   (string-shape-map-fix shape-subst)
                   (string-type-map-fix atom-subst)
                   (string-type-map-fix array-subst))
             (mv nil nil nil nil nil))
     :array (if (type-case type :array)
                (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                      (type-match (type-array->elem type)
                                  pat.elem
                                  dim-subst
                                  shape-subst
                                  atom-subst
                                  array-subst))
                     ((unless okp) (mv nil nil nil nil nil))
                     ((mv okp dim-subst shape-subst)
                      (ispace-match (type-array->ispace type)
                                    pat.ispace
                                    dim-subst
                                    shape-subst))
                     ((unless okp) (mv nil nil nil nil nil)))
                  (mv t dim-subst shape-subst atom-subst array-subst))
              (mv nil nil nil nil nil))
     :bracket (if (type-case type :bracket)
                  (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                        (type-match (type-bracket->elem type)
                                    pat.elem
                                    dim-subst
                                    shape-subst
                                    atom-subst
                                    array-subst))
                       ((unless okp) (mv nil nil nil nil nil))
                       ((mv okp dim-subst shape-subst)
                        (ispace-list-match (type-bracket->ispaces type)
                                           pat.ispaces
                                           dim-subst
                                           shape-subst))
                       ((unless okp) (mv nil nil nil nil nil)))
                    (mv t dim-subst shape-subst atom-subst array-subst))
                (mv nil nil nil nil nil))
     :fun (if (type-case type :fun)
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
                            array-subst))
            (mv nil nil nil nil nil))
     :funn (if (type-case type :funn)
               (b* (((mv okp dim-subst shape-subst atom-subst array-subst)
                     (type-list-match (type-funn->in type)
                                      pat.in
                                      dim-subst
                                      shape-subst
                                      atom-subst
                                      array-subst))
                    ((unless okp) (mv nil nil nil nil nil)))
                 (type-match (type-funn->out type)
                             pat.out
                             dim-subst
                             shape-subst
                             atom-subst
                             array-subst))
             (mv nil nil nil nil nil))
     :forall (if (and (type-case type :forall)
                      (equal (type-forall->param type) pat.param))
                 (b* ((vars (set::insert pat.param nil))
                      ((mv atom-subst1 array-subst1)
                       (atom/array-subst-self-bind vars atom-subst array-subst))
                      ((mv okp dim-subst shape-subst atom-subst1 array-subst1)
                       (type-match (type-forall->body type)
                                   pat.body
                                   dim-subst
                                   shape-subst
                                   atom-subst1
                                   array-subst1))
                      ((unless okp) (mv nil nil nil nil nil))
                      ((mv atom-subst array-subst)
                       (atom/array-subst-restore-bound vars
                                                       atom-subst
                                                       array-subst
                                                       atom-subst1
                                                       array-subst1)))
                   (mv t dim-subst shape-subst atom-subst array-subst))
               (mv nil nil nil nil nil))
     :foralln (if (and (type-case type :foralln)
                       (equal (type-foralln->params type) pat.params))
                  (b* ((vars (set::mergesort pat.params))
                       ((mv atom-subst1 array-subst1)
                        (atom/array-subst-self-bind vars
                                                    atom-subst
                                                    array-subst))
                       ((mv okp dim-subst shape-subst atom-subst1 array-subst1)
                        (type-match (type-foralln->body type)
                                    pat.body
                                    dim-subst
                                    shape-subst
                                    atom-subst1
                                    array-subst1))
                       ((unless okp) (mv nil nil nil nil nil))
                       ((mv atom-subst array-subst)
                        (atom/array-subst-restore-bound vars
                                                        atom-subst
                                                        array-subst
                                                        atom-subst1
                                                        array-subst1)))
                    (mv t dim-subst shape-subst atom-subst array-subst))
                (mv nil nil nil nil nil))
     :pi (if (and (type-case type :pi)
                  (equal (type-pi->param type) pat.param))
             (b* ((vars (set::insert pat.param nil))
                  ((mv dim-subst1 shape-subst1)
                   (dim/shape-subst-self-bind vars dim-subst shape-subst))
                  ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                   (type-match (type-pi->body type)
                               pat.body
                               dim-subst1
                               shape-subst1
                               atom-subst
                               array-subst))
                  ((unless okp) (mv nil nil nil nil nil))
                  ((mv dim-subst shape-subst)
                   (dim/shape-subst-restore-bound vars
                                                  dim-subst
                                                  shape-subst
                                                  dim-subst1
                                                  shape-subst1)))
               (mv t dim-subst shape-subst atom-subst array-subst))
           (mv nil nil nil nil nil))
     :pin (if (and (type-case type :pin)
                   (equal (type-pin->params type) pat.params))
              (b* ((vars (set::mergesort pat.params))
                   ((mv dim-subst1 shape-subst1)
                    (dim/shape-subst-self-bind vars dim-subst shape-subst))
                   ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                    (type-match (type-pin->body type)
                                pat.body
                                dim-subst1
                                shape-subst1
                                atom-subst
                                array-subst))
                   ((unless okp) (mv nil nil nil nil nil))
                   ((mv dim-subst shape-subst)
                    (dim/shape-subst-restore-bound vars
                                                   dim-subst
                                                   shape-subst
                                                   dim-subst1
                                                   shape-subst1)))
                (mv t dim-subst shape-subst atom-subst array-subst))
            (mv nil nil nil nil nil))
     :sigma (if (and (type-case type :sigma)
                     (equal (type-sigma->param type) pat.param))
                (b* ((vars (set::insert pat.param nil))
                     ((mv dim-subst1 shape-subst1)
                      (dim/shape-subst-self-bind vars dim-subst shape-subst))
                     ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                      (type-match (type-sigma->body type)
                                  pat.body
                                  dim-subst1
                                  shape-subst1
                                  atom-subst
                                  array-subst))
                     ((unless okp) (mv nil nil nil nil nil))
                     ((mv dim-subst shape-subst)
                      (dim/shape-subst-restore-bound vars
                                                     dim-subst
                                                     shape-subst
                                                     dim-subst1
                                                     shape-subst1)))
                  (mv t dim-subst shape-subst atom-subst array-subst))
              (mv nil nil nil nil nil))
     :sigman (if (and (type-case type :sigman)
                      (equal (type-sigman->params type) pat.params))
                 (b* ((vars (set::mergesort pat.params))
                      ((mv dim-subst1 shape-subst1)
                       (dim/shape-subst-self-bind vars dim-subst shape-subst))
                      ((mv okp dim-subst1 shape-subst1 atom-subst array-subst)
                       (type-match (type-sigman->body type)
                                   pat.body
                                   dim-subst1
                                   shape-subst1
                                   atom-subst
                                   array-subst))
                      ((unless okp) (mv nil nil nil nil nil))
                      ((mv dim-subst shape-subst)
                       (dim/shape-subst-restore-bound vars
                                                      dim-subst
                                                      shape-subst
                                                      dim-subst1
                                                      shape-subst1)))
                   (mv t dim-subst shape-subst atom-subst array-subst))
               (mv nil nil nil nil nil)))
    :measure (type-count pat))

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
    :parents (type-matcher types-match)
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
                       array-subst))
    :measure (type-list-count pats))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual types-match))

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
