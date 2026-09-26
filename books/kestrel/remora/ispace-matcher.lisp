; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")
(include-book "ispace-equivalence-checker")
(include-book "variable-substitution-operations")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-matcher
  :parents (static-semantics)
  :short "A matcher for ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is matching in the sense of one-sided unification;
     we will extend this to a full unifier,
     or perhaps we will add a separate unifier.")
   (xdoc::h3
    "Dimension Matching")
   (xdoc::p
    "We use the following approach to match dimensions.")
   (xdoc::p
    "The difficulty is with additions.
     Matching @('5') to the pattern @('(+ 1 i)') should succeed,
     by binding @('i') to @('4'),
     because @('(+ 1 4)') is equivalent to @('5'),
     even though the two have different structures.
     So addition patterns must be matched modulo additive equivalence:
     this is the task of @(tsee dim-add-match), described here;
     the other kinds of patterns are matched structurally,
     as described in @(tsee dims-match);
     indeed, for now we only have equivalence checking for additions,
     not for multiplications and subtractions of dimensions,
     which are treated as black boxes essentially.")
   (xdoc::p
    "The key observation is that
     a normalized dimension (see @(tsee normalize-dim))
     has a canonical form:
     a constant plus a multiset of other addends,
     each of which is a variable, a multiplication, or a subtraction.
     Two normalized dimensions are equivalent exactly when
     their constants are equal and their multisets are equal.
     Thus, instead of solving an equation over terms,
     we solve one over a number and a multiset.
     Consider matching @('(+ 2 k)') to the pattern @('(+ 1 i)').
     The dimension is the number @('2')
     with the multiset consisting of @('k').
     The pattern contributes the number @('1') and the unknown @('i').
     Whatever @('i') stands for must supply
     the missing number @('1') and the missing @('k'),
     so @('i') must be @('(+ 1 k)').")
   (xdoc::p
    "This is the whole approach:
     we subtract from the dimension what the pattern already accounts for,
     and the unknown gets what is left.
     What is left is the remainder,
     which is the central notion of the approach.
     We split the dimension into a constant and a list of other addends
     (see @(tsee dim-addends)),
     which form the initial remainder.
     Each addend of the pattern that we can account for
     subtracts something from the remainder.
     At the end, the remainder is
     what the unbound pattern variables must produce.")
   (xdoc::p
    "So we go through the addends of the pattern,
     and there are only two cases.
     If the addend is a pattern variable without a binding yet,
     we cannot account for it (i.e. we cannot remove it from the remainder),
     so we just add it to a list of unbound pattern variables.
     Any other addend is known:
     a constant is known outright,
     a bound pattern variable is known through its binding,
     and a multiplication, subtraction, or nested addition is known
     if all the variables in it are bound
     (see @(tsee dim-vars-bound-p));
     if some variable in it is unbound, the match fails,
     because a multiset equation cannot tell us
     what a variable inside a multiplication or subtraction should be.
     In all the known cases we do the same thing:
     we instantiate the addend with the substitution,
     which turns a bound variable into its binding
     and leaves a constant alone,
     and we account for the resulting known dimension in the remainder
     (see @(tsee dim-add-match-known)).")
   (xdoc::p
    "Accounting for a known dimension in the remainder
     means normalizing it,
     splitting it into its own constant and addends,
     and subtracting them:
     the constant must fit under the constant of the remainder,
     and each addend must be found in the multiset of the remainder,
     modulo equivalence, and is removed once.
     For instance,
     with the remainder consisting of
     the constant @('5') and the addends @('k') and @('l'),
     accounting for @('(+ 2 l)') leaves
     the constant @('3') and the addend @('k'),
     while accounting for @('6') fails on the constant
     and accounting for @('m') fails on the addends.
     A failure here means that no substitution can work,
     because the known part of the pattern already exceeds the dimension.")
   (xdoc::p
    "After going through the addends of the pattern,
     we have the remainder and the list of unbound pattern variables.
     If there are no unbound variables, the pattern was fully known,
     so the remainder must be exactly the constant @('0') with no addends,
     otherwise the two sides differ.
     If there is exactly one unbound variable, occurring once,
     it is forced to be the remainder,
     so we bind it to the remainder turned back into a dimension
     and normalized:
     e.g. @('4') rather than @('(+ 4)'),
     and @('k') rather than @('(+ 0 k)').
     Otherwise, the match fails, rather than guessing:
     two unbound variables could split the remainder in many ways,
     and one unbound variable occurring twice would need division.
     In the future, we may extend this to
     collect equations from multiple matches
     (e.g. of the different components of a type)
     and solve them together,
     since the equations from one match
     may disambiguate the solutions of another match.")
   (xdoc::p
    "The substitution is threaded through matches (see @(tsee dims-match)):
     the bindings come from earlier matches of other components,
     and they constrain the current match.
     This is what makes matching @('(+ 3 k)') to @('(+ i j)') succeed
     when @('i') is already bound to @('3'):
     @('i') is a known addend,
     the remainder becomes just @('k'),
     and @('j') is forced to be @('k').
     It is also how rigid variables work:
     the entry points bind them to themselves
     (see @(tsee type-match-vars)),
     so a rigid variable @('k') in the pattern is instantiated to @('k'),
     and must be found in the dimension.")
   (xdoc::p
    "Every conclusion drawn by this approach
     is an equality of numbers and multisets,
     so the approach is sound on any dimension and pattern.
     Completeness,
     modulo additive equivalence and under the uniqueness restriction above,
     requires the dimension and the pattern to be normalized:
     if the dimension were the unflattened @('(+ 1 (+ 2 k))'),
     the split would treat @('(+ 2 k)') as one opaque addend,
     and matching to @('(+ 3 i)') would fail,
     although binding @('i') to @('k') works.
     Thus, the callers are expected to normalize both sides
     before matching."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove1-equiv-dim ((dim dimp) (dims dim-listp))
  :returns (mv (foundp booleanp) (new-dims dim-listp))
  :short "Remove from a list of dimensions
          the first one equivalent to a given dimension, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like ACL2's @('remove1-equal'),
     but modulo dimension equivalence (see @(tsee dim-equivp)).
     We also return a flag saying whether an equivalent dimension was found;
     if not, the list is returned unchanged."))
  (b* (((when (endp dims)) (mv nil nil))
       ((when (dim-equivp dim (car dims)))
        (mv t (dim-list-fix (cdr dims))))
       ((mv foundp new-dims) (remove1-equiv-dim dim (cdr dims))))
    (mv foundp (cons (dim-fix (car dims)) new-dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove1-equiv-dims ((dims1 dim-listp) (dims2 dim-listp))
  :returns (mv (okp booleanp) (new-dims dim-listp))
  :short "Remove from a list of dimensions
          one dimension equivalent to each dimension of another list."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the first list,
     removing from the second list, via @(tsee remove1-equiv-dim),
     one dimension equivalent to each dimension of the first list.
     If some dimension of the first list has no equivalent dimension
     in what remains of the second list, we fail:
     we return @('nil') as the flag,
     and also as the list, which is irrelevant in that case.
     Otherwise, we return @('t') and what remains of the second list.")
   (xdoc::p
    "This amounts to checking that the first list is included
     in the second list as a multiset (i.e. counting repetitions),
     modulo dimension equivalence,
     and to returning the multiset difference if so."))
  (b* (((when (endp dims1)) (mv t (dim-list-fix dims2)))
       ((mv foundp dims2) (remove1-equiv-dim (car dims1) dims2))
       ((unless foundp) (mv nil nil)))
    (remove1-equiv-dims (cdr dims1) dims2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-vars-bound-p ((dim dimp) (subst string-dim-mapp))
  :returns (yes/no booleanp)
  :short "Check if all the variables of a dimension
          are bound in a dimension substitution."
  (dim-vars-bound-p-loop (dim-free-ispace-vars dim) subst)

  :prepwork

  ((define dim-vars-bound-p-loop ((vars ispace-var-setp)
                                  (subst string-dim-mapp))
     :returns (yes/no booleanp)
     :parents nil
     (b* (((when (set::emptyp (ispace-var-set-fix vars))) t)
          (var (set::head vars)))
       (and (ispace-var-case
             var
             :dim (consp (omap::assoc var.name (string-dim-map-fix subst)))
             :shape nil) ; never happens (a dimension has no shape variables)
            (dim-vars-bound-p-loop (set::tail vars) subst)))
     :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-add-match-known ((known dimp) (const natp) (rest dim-listp))
  :returns (mv (okp booleanp)
               (new-const natp
                          :rule-classes (:rewrite :type-prescription)
                          :hints (("Goal" :in-theory (enable natp))))
               (new-rest dim-listp))
  :short "Account for a known dimension in the remainder of a dimension
          being matched to an addition pattern."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee dim-add-match);
     see the approach described in @(see ispace-matcher).
     The remainder is passed as @('const') and @('rest'),
     in the form produced by @(tsee dim-addends);
     the dimension being matched is not passed to this function.
     A known dimension is a dimension without unbound pattern variables:
     a constant,
     the binding of a bound pattern variable,
     or an addend instantiated with the substitution.")
   (xdoc::p
    "We normalize the known dimension before splitting it
     (see @(tsee dim-addends)),
     so that its constant and addends are in canonical form
     even if the pattern or the substitution are not normalized.
     Then the constant must not exceed the constant of the remainder,
     from which it is subtracted,
     and the addends must be removable from the addends of the remainder
     (see @(tsee remove1-equiv-dims)), and they are removed.
     If either condition fails, the match fails,
     and the returned remainder is irrelevant."))
  (b* (((mv known-const known-addends) (dim-addends (normalize-dim known)))
       ((when (> known-const (lnfix const))) (mv nil 0 nil))
       ((mv okp rest) (remove1-equiv-dims known-addends rest))
       ((unless okp) (mv nil 0 nil)))
    (mv t (- (lnfix const) known-const) rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-add-match ((dim dimp) (addends dim-listp) (subst string-dim-mapp))
  :returns (mv (okp booleanp) (new-subst string-dim-mapp))
  :short "Match a dimension to an addition pattern,
          modulo additive equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "The pattern is an addition, whose addends are passed to this function,
     since the caller has them at hand:
     we match the dimension @('dim') to the pattern @('(dim-add addends)'),
     modulo additive equivalence,
     with the approach described in @(see ispace-matcher).")
   (xdoc::p
    "We split the dimension into the initial remainder
     (see @(tsee dim-addends)),
     and we go through the addends of the pattern
     via @('dim-add-match-loop'),
     which threads the remainder and the list of unbound pattern variables,
     and which fails as soon as an addend cannot be accounted for
     (see @(tsee dim-add-match-known)).
     If the loop succeeds,
     we resolve the remainder with the unbound pattern variables:
     if there are none,
     the remainder must be the constant @('0') with no addends;
     if there is one,
     we bind it to the dimension formed from the remainder,
     which we normalize (see @(tsee normalize-dim));
     if there are more, including one occurring twice, we fail.")
   (xdoc::p
    "The unbound pattern variables are collected as ispace variables,
     but they are always dimension variables,
     because they come from dimensions;
     the case of a shape variable never happens.")
   (xdoc::p
    "As explained in @(see ispace-matcher),
     this is sound on all dimensions and patterns,
     but it is complete,
     modulo additive equivalence and under the uniqueness restriction,
     only on normalized dimensions and patterns."))
  (b* (((mv const rest) (dim-addends dim))
       ((mv okp const rest unbound)
        (dim-add-match-loop addends subst const rest nil))
       ((unless okp) (mv nil nil))
       (subst (string-dim-map-fix subst))
       ((unless (consp unbound))
        (if (and (= const 0) (not (consp rest)))
            (mv t subst)
          (mv nil nil)))
       ((when (consp (cdr unbound))) (mv nil nil))
       (var (car unbound))
       (remainder (normalize-dim (dim-add (cons (dim-const const) rest)))))
    (ispace-var-case
     var
     :dim (mv t (omap::update var.name remainder subst))
     :shape (mv nil nil))) ; never happens (only dimension variables collected)
  :prepwork
  ((define dim-add-match-loop ((addends dim-listp)
                               (subst string-dim-mapp)
                               (const natp)
                               (rest dim-listp)
                               (unbound ispace-var-listp))
     :returns (mv (okp booleanp)
                  (new-const natp :rule-classes (:rewrite :type-prescription))
                  (new-rest dim-listp)
                  (new-unbound ispace-var-listp))
     :parents nil
     (b* (((when (endp addends))
           (mv t
               (lnfix const)
               (dim-list-fix rest)
               (ispace-var-list-fix unbound)))
          (addend (car addends))
          ((when (and (dim-case addend :var)
                      (not (omap::assoc (dim-var->name addend)
                                        (string-dim-map-fix subst)))))
           (dim-add-match-loop (cdr addends)
                               subst
                               const
                               rest
                               (cons (ispace-var-dim (dim-var->name addend))
                                     (ispace-var-list-fix unbound))))
          ((unless (dim-vars-bound-p addend subst)) (mv nil 0 nil nil))
          ((mv okp const rest)
           (dim-add-match-known (dim-subst-dim-vars addend subst) const rest))
          ((unless okp) (mv nil 0 nil nil)))
       (dim-add-match-loop (cdr addends) subst const rest unbound)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dims-match
  :short "Match dimensions to patterns (other dimensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The matching is modulo dimension equivalence:
     we look for a substitution that makes the pattern
     equivalent (not necessarily equal) to the dimension.
     It is structural for all kinds of patterns except additions,
     which are matched modulo additive equivalence via @(tsee dim-add-match),
     according to the approach described in @(see ispace-matcher).
     As explained there,
     the matching is intended for normalized dimensions and patterns
     (see @(tsee normalize-dim)),
     for which it is complete modulo additive equivalence,
     under the uniqueness restriction described there;
     it is sound on all dimensions and patterns.")
   (xdoc::p
    "The variables in the patterns are the pattern variables.
     The matching builds a substitution for the pattern variables,
     which is threaded through these functions as an additional argument,
     so that it can be extended by successive matches
     (e.g. of the elements of a list);
     it is initially empty.
     If the matching succeeds, the resulting substitution is returned;
     if the matching fails, @('nil') is returned as the substitution,
     which is irrelevant in that case.")
   (xdoc::p
    "The substitution is meant to be applied simultaneously,
     as @(tsee dim-subst-dim-vars) does:
     applying it to the pattern yields a dimension
     equivalent to the dimension being matched.
     The variables of the dimension are not pattern variables,
     but they may have the same names as pattern variables,
     in which case the dimensions in the substitution mention those names;
     thus, the substitution must not be applied repeatedly
     or composed with itself.
     For instance, matching @('(+ 3 i)') to the pattern @('(+ 1 j)'),
     with @('i') already bound to @('5') by a previous match,
     binds @('j') to @('(+ 2 i)'):
     applying the substitution to the pattern yields @('(+ 1 (+ 2 i))'),
     which is equivalent to @('(+ 3 i)'),
     but applying it once more would yield @('(+ 1 (+ 2 5))')."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dim-match ((dim dimp) (pat dimp) (subst string-dim-mapp))
    :returns (mv (okp booleanp) (new-subst string-dim-mapp))
    :parents (ispace-matcher dims-match)
    :short "Match a dimension to a pattern (another dimension)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A pattern variable that is bound in the substitution
       matches only a dimension equivalent to the one bound to it.
       A pattern variable that is not bound in the substitution
       matches any dimension, which is bound to the variable.")
     (xdoc::p
      "A pattern constant matches only an equivalent dimension,
       i.e. one that normalizes to the same constant.")
     (xdoc::p
      "A pattern addition is matched modulo additive equivalence,
       via @(tsee dim-add-match).")
     (xdoc::p
      "A pattern multiplication matches only a multiplication
       whose operands match the operands of the pattern,
       in the same order;
       similarly for subtractions."))
    (dim-case
     pat
     :var (b* ((subst (string-dim-map-fix subst))
               (var+dim (omap::assoc pat.name subst)))
            (cond ((not var+dim)
                   (mv t (omap::update pat.name (dim-fix dim) subst)))
                  ((dim-equivp (cdr var+dim) dim)
                   (mv t subst))
                  (t (mv nil nil))))
     :const (if (dim-equivp dim (dim-const pat.val))
                (mv t (string-dim-map-fix subst))
              (mv nil nil))
     :add (dim-add-match dim pat.dims subst)
     :mul (if (dim-case dim :mul)
              (dim-list-match (dim-mul->dims dim) pat.dims subst)
            (mv nil nil))
     :sub (if (dim-case dim :sub)
              (dim-list-match (dim-sub->dims dim) pat.dims subst)
            (mv nil nil)))
    :measure (dim-count pat))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dim-list-match ((dims dim-listp)
                          (pats dim-listp)
                          (subst string-dim-mapp))
    :returns (mv (okp booleanp) (new-subst string-dim-mapp))
    :parents (ispace-matcher dims-match)
    :short "Match a list of dimensions
            to a list of patterns (other dimensions)."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and each dimension must match the corresponding pattern,
       with the substitution threaded through the successive matches."))
    (b* (((when (endp pats))
          (if (endp dims)
              (mv t (string-dim-map-fix subst))
            (mv nil nil)))
         ((when (endp dims)) (mv nil nil))
         ((mv okp subst) (dim-match (car dims) (car pats) subst))
         ((unless okp) (mv nil nil)))
      (dim-list-match (cdr dims) (cdr pats) subst))
    :measure (dim-list-count pats))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual dims-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines shapes/ispaces-match
  :short "Match shapes and ispaces to patterns (other shapes and ispaces)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we perform a purely syntactical match, as in @(tsee dims-match),
     which is incomplete with respect to shape and ispace equivalence.
     For instance, the pattern @('(++ s (dims 1))')
     is not matched by the shape @('(dims 2 1)'),
     even though replacing @('s') with @('(dims 2)') in the pattern
     yields a shape equivalent to @('(dims 2 1)').
     We will need to extend this to matching modulo equivalence.")
   (xdoc::p
    "Since shapes and ispaces contain
     both dimension variables and shape variables,
     the matching builds two substitutions,
     one for dimension variables and one for shape variables.
     Both are threaded through these functions,
     analogously to the single substitution in @(tsee dims-match),
     and both are meant to be applied simultaneously,
     as @(tsee shape-subst-ispace-vars)
     and @(tsee ispace-subst-ispace-vars) do.
     If the matching fails, @('nil') is returned as both substitutions."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define shape-match ((shape shapep)
                       (pat shapep)
                       (dim-subst string-dim-mapp)
                       (shape-subst string-shape-mapp))
    :returns (mv (okp booleanp)
                 (new-dim-subst string-dim-mapp)
                 (new-shape-subst string-shape-mapp))
    :parents (ispace-matcher shapes/ispaces-match)
    :short "Match a shape to a pattern (another shape)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A pattern variable that is bound in the shape substitution
       matches only the shape bound to it.
       A pattern variable that is not bound in the shape substitution
       matches any shape, which is bound to the variable.")
     (xdoc::p
      "A pattern @(':dims') shape matches only a @(':dims') shape
       whose dimensions match the dimensions of the pattern,
       via @(tsee dim-list-match).")
     (xdoc::p
      "A pattern concatenation matches only a concatenation
       whose shapes match the shapes of the pattern,
       in the same order.
       A pattern splice matches only a splice
       whose ispaces match the ispaces of the pattern,
       in the same order."))
    (shape-case
     pat
     :var (b* ((shape-subst (string-shape-map-fix shape-subst))
               (var+shape (omap::assoc pat.name shape-subst)))
            (cond ((not var+shape)
                   (mv t
                       (string-dim-map-fix dim-subst)
                       (omap::update pat.name (shape-fix shape) shape-subst)))
                  ((equal (cdr var+shape) (shape-fix shape))
                   (mv t (string-dim-map-fix dim-subst) shape-subst))
                  (t (mv nil nil nil))))
     :dims (if (shape-case shape :dims)
               (b* (((mv okp dim-subst)
                     (dim-list-match (shape-dims->dims shape)
                                     pat.dims
                                     dim-subst))
                    ((unless okp) (mv nil nil nil)))
                 (mv t dim-subst (string-shape-map-fix shape-subst)))
             (mv nil nil nil))
     :append (if (shape-case shape :append)
                 (shape-list-match (shape-append->shapes shape)
                                   pat.shapes
                                   dim-subst
                                   shape-subst)
               (mv nil nil nil))
     :splice (if (shape-case shape :splice)
                 (ispace-list-match (shape-splice->ispaces shape)
                                    pat.ispaces
                                    dim-subst
                                    shape-subst)
               (mv nil nil nil)))
    :measure (shape-count pat))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define shape-list-match ((shapes shape-listp)
                            (pats shape-listp)
                            (dim-subst string-dim-mapp)
                            (shape-subst string-shape-mapp))
    :returns (mv (okp booleanp)
                 (new-dim-subst string-dim-mapp)
                 (new-shape-subst string-shape-mapp))
    :parents (ispace-matcher shapes/ispaces-match)
    :short "Match a list of shapes to a list of patterns (other shapes)."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and each shape must match the corresponding pattern,
       with the substitutions threaded through the successive matches."))
    (b* (((when (endp pats))
          (if (endp shapes)
              (mv t
                  (string-dim-map-fix dim-subst)
                  (string-shape-map-fix shape-subst))
            (mv nil nil nil)))
         ((when (endp shapes)) (mv nil nil nil))
         ((mv okp dim-subst shape-subst)
          (shape-match (car shapes) (car pats) dim-subst shape-subst))
         ((unless okp) (mv nil nil nil)))
      (shape-list-match (cdr shapes) (cdr pats) dim-subst shape-subst))
    :measure (shape-list-count pats))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ispace-match ((ispace ispacep)
                        (pat ispacep)
                        (dim-subst string-dim-mapp)
                        (shape-subst string-shape-mapp))
    :returns (mv (okp booleanp)
                 (new-dim-subst string-dim-mapp)
                 (new-shape-subst string-shape-mapp))
    :parents (ispace-matcher shapes/ispaces-match)
    :short "Match an ispace to a pattern (another ispace)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A pattern dimension ispace matches only a dimension ispace
       whose dimension matches the dimension of the pattern,
       via @(tsee dim-match).
       A pattern shape ispace matches only a shape ispace
       whose shape matches the shape of the pattern."))
    (ispace-case
     pat
     :dim (if (ispace-case ispace :dim)
              (b* (((mv okp dim-subst)
                    (dim-match (ispace-dim->dim ispace) pat.dim dim-subst))
                   ((unless okp) (mv nil nil nil)))
                (mv t dim-subst (string-shape-map-fix shape-subst)))
            (mv nil nil nil))
     :shape (if (ispace-case ispace :shape)
                (shape-match (ispace-shape->shape ispace)
                             pat.shape
                             dim-subst
                             shape-subst)
              (mv nil nil nil)))
    :measure (ispace-count pat))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define ispace-list-match ((ispaces ispace-listp)
                             (pats ispace-listp)
                             (dim-subst string-dim-mapp)
                             (shape-subst string-shape-mapp))
    :returns (mv (okp booleanp)
                 (new-dim-subst string-dim-mapp)
                 (new-shape-subst string-shape-mapp))
    :parents (ispace-matcher shapes/ispaces-match)
    :short "Match a list of ispaces to a list of patterns (other ispaces)."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists must have the same length,
       and each ispace must match the corresponding pattern,
       with the substitutions threaded through the successive matches."))
    (b* (((when (endp pats))
          (if (endp ispaces)
              (mv t
                  (string-dim-map-fix dim-subst)
                  (string-shape-map-fix shape-subst))
            (mv nil nil nil)))
         ((when (endp ispaces)) (mv nil nil nil))
         ((mv okp dim-subst shape-subst)
          (ispace-match (car ispaces) (car pats) dim-subst shape-subst))
         ((unless okp) (mv nil nil nil)))
      (ispace-list-match (cdr ispaces) (cdr pats) dim-subst shape-subst))
    :measure (ispace-list-count pats))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual shapes/ispaces-match))
