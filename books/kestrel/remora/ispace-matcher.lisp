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
  :parents (validator)
  :short "A matcher for ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is matching in the sense of one-sided unification;
     we will extend this to a full unifier,
     or perhaps we will add a separate unifier.")
   (xdoc::p
    "The matching is modulo ispace equivalence,
     to the extent that the @(see ispace-equivalence-checker) captures it;
     the following sections describe the approach,
     for dimensions and for shapes (and ispaces).
     The @(see type-matcher) builds on this matcher.")
   (xdoc::h3
    "Dimension Matching")
   (xdoc::p
    "We use the following approach to match dimensions.")
   (xdoc::p
    "The difficulty is with additions.
     Matching @('5') to the pattern @('(+ 1 $i)') should succeed,
     by binding @('$i') to @('4'),
     because @('(+ 1 4)') is equivalent to @('5'),
     even though the two have different structures.
     So addition patterns must be matched modulo additive equivalence:
     this is the task of @(tsee dim-add-match), described here;
     the other kinds of patterns are matched structurally,
     as described in @(tsee dims-match);
     indeed, although the @(see ispace-equivalence-checker) interprets
     multiplications and subtractions of dimensions,
     the matcher treats them as black boxes:
     with them, the equations discussed below would no longer be linear,
     so we restrict the patterns instead,
     requiring the variables
     in a multiplication or subtraction addend of an addition pattern
     to be already bound (see below).")
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
     Consider matching @('(+ 2 $k)') to the pattern @('(+ 1 $i)').
     The dimension is the number @('2')
     with the multiset consisting of @('$k').
     The pattern contributes the number @('1') and the unknown @('$i').
     Whatever @('$i') stands for must supply
     the missing number @('1') and the missing @('$k'),
     so @('$i') must be @('(+ 1 $k)').")
   (xdoc::p
    "Put differently,
     for dimensions that only use addition,
     whose equivalence is decidable (see @(see ispace-equivalence-checker)),
     matching modulo equivalence amounts to
     solving linear equations over the natural numbers.
     The unknowns are the unbound pattern variables,
     each standing for a constant plus a multiset of addends;
     the equations say that
     the constant of the pattern plus the constants of the unknowns
     must equal the constant of the dimension,
     and that each addend of the dimension
     must be contributed by the pattern or by the unknowns
     exactly as many times as it occurs in the dimension.
     If the pattern has a single unknown occurring once,
     as in the example above,
     there is at most one solution,
     obtained by subtracting the constant of the pattern
     from the constant of the dimension
     (there is no solution if the former is larger)
     and by adding the addends of the dimension
     that the pattern does not account for.
     If the pattern has multiple unknowns,
     e.g. @('(+ $i $j)') matched to @('(+ 3 $k $l)'),
     there may be multiple solutions,
     corresponding to the ways of distributing
     the constant and the addends of the dimension among the unknowns;
     if the pattern has a single unknown occurring multiple times,
     e.g. @('(+ $i $i)') matched to @('4'),
     the solution, if any, requires division.
     For now, we only handle the case of a single unknown occurring once,
     failing in the other cases (see below).
     In the future, we may extend this to
     collect equations from multiple matches
     (e.g. of the different components of a type)
     and solve them together,
     since the equations from one match
     may disambiguate the solutions of another match.")
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
     the constant @('5') and the addends @('$k') and @('$l'),
     accounting for @('(+ 2 $l)') leaves
     the constant @('3') and the addend @('$k'),
     while accounting for @('6') fails on the constant
     and accounting for @('$m') fails on the addends.
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
     and @('$k') rather than @('(+ 0 $k)').
     Otherwise, the match fails, rather than guessing,
     because the solution is not unique or requires division,
     as discussed above.")
   (xdoc::p
    "The substitution is threaded through matches (see @(tsee dims-match)):
     the bindings come from earlier matches of other components,
     and they constrain the current match.
     This is what makes matching @('(+ 3 $k)') to @('(+ $i $j)') succeed
     when @('$i') is already bound to @('3'):
     @('$i') is a known addend,
     the remainder becomes just @('$k'),
     and @('$j') is forced to be @('$k').
     It is also how rigid variables work:
     the entry points bind them to themselves
     (see @(tsee type-match-vars)),
     so a rigid variable @('$k') in the pattern is instantiated to @('$k'),
     and must be found in the dimension.")
   (xdoc::p
    "Every conclusion drawn by this approach
     is an equality of numbers and multisets,
     so the approach is sound on any dimension and pattern.
     Completeness,
     modulo additive equivalence and under the uniqueness restriction above,
     requires the dimension and the pattern to be normalized:
     if the dimension were the unflattened @('(+ 1 (+ 2 $k))'),
     the split would treat @('(+ 2 $k)') as one opaque addend,
     and matching to @('(+ 3 $i)') would fail,
     although binding @('$i') to @('$k') works.
     Thus, the callers are expected to normalize both sides
     before matching.")
   (xdoc::h3
    "Shape Matching")
   (xdoc::p
    "We use the following approach to match shapes,
     and also ispaces, which normalize to shapes.")
   (xdoc::p
    "The difficulty is that
     concatenations, splices, and shapes with multiple dimensions
     are different ways to write equivalent shapes.
     Matching @('(dims 2 1)') to the pattern @('(++ @s (dims 1))')
     should succeed,
     by binding @('@s') to the shape with the single dimension @('2'),
     because @('(++ (dims 2) (dims 1))') is equivalent to @('(dims 2 1)').
     Matching @('(dims 3)') to the pattern @('[$i @s]'),
     i.e. the splice of the dimension variable @('$i')
     and the shape variable @('@s'),
     should succeed,
     by binding @('$i') to @('3') and @('@s') to the empty shape.
     So shape patterns must be matched modulo shape equivalence:
     this is the task of @(tsee shape-match) and @(tsee ispace-match),
     which normalize both sides
     and match their elements via @(tsee shape-elements-match),
     as described here.")
   (xdoc::p
    "The key observation is that
     a normalized shape (see @(tsee normalize-shape))
     has a canonical form:
     a concatenation of elements,
     each of which is a shape variable
     or a shape with a single (normalized) dimension.
     Two normalized shapes are equivalent exactly when
     their lists of elements are equal, element by element.
     Thus, instead of matching trees of
     concatenations, splices, and shapes with multiple dimensions,
     we match two sequences of elements,
     in which a shape variable of the pattern may stand for a segment,
     i.e. zero or more consecutive elements, of the shape being matched.
     Consider matching @('(dims 2 1)') to the pattern @('(++ @s (dims 1))').
     The shape normalizes to the elements @('(dims 2)') and @('(dims 1)'),
     and the pattern to the elements @('@s') and @('(dims 1)').
     The last elements are matched together,
     and @('@s') must stand for the rest, i.e. the element @('(dims 2)').")
   (xdoc::p
    "This is the whole approach:
     we go through the elements of the pattern,
     consuming elements of the shape,
     and a shape variable of the pattern consumes
     as many elements as the other elements of the pattern leave to it.
     There are three cases, described next.")
   (xdoc::p
    "An element of the pattern with a single dimension
     consumes exactly one element of the shape,
     which must also have a single dimension:
     the two dimensions are matched via @(tsee dim-match).
     Since that is modulo additive equivalence,
     matching @('(dims 3)') to @('[(+ 1 $i) @s]')
     binds @('$i') to @('2'), and @('@s') to the empty shape.
     A shape variable of the shape being matched
     never matches such an element of the pattern,
     because it may stand for any number of dimensions.")
   (xdoc::p
    "A shape variable of the pattern that is already bound
     consumes as many elements of the shape
     as the elements of its (normalized) binding,
     which must be equivalent to those elements
     (see @(tsee shape-equivp)).")
   (xdoc::p
    "A shape variable of the pattern that is not bound yet
     consumes a segment whose length is forced by counting:
     the number of remaining elements of the shape,
     minus the number of elements needed by
     the remaining elements of the pattern,
     namely one for each element with a single dimension
     and the length of the binding for each bound shape variable
     (see @(tsee shape-pattern-elements-length)).
     If the remaining elements of the pattern include
     another unbound shape variable, or the same variable again,
     the length is undetermined and the match fails, rather than guessing,
     as in the corresponding case of dimension matching.
     Otherwise, the variable is bound to the concatenation of the segment,
     e.g. to @('(++ (dims 2))') in the first example above,
     and to the empty concatenation @('(++)') in the second example above,
     which is the only solution.
     The position of the unbound variable does not matter:
     matching @('(++ @t (dims 3))') to the pattern @('(++ @s (dims $i))')
     binds @('@s') to @('(++ @t)') and @('$i') to @('3').")
   (xdoc::p
    "Ispaces are matched in the same way,
     because a normalized ispace (see @(tsee normalize-ispace))
     is always a shape ispace with a concatenation.
     For instance, a dimension ispace @('3')
     is matched to a dimension ispace pattern @('$i')
     as the shape with the single dimension @('3')
     to the shape with the single dimension @('$i').")
   (xdoc::p
    "As with dimension matching,
     the substitutions (one for dimension variables and one for shape variables)
     are threaded through matches,
     so that the bindings from earlier matches constrain the current match,
     including the bindings of rigid variables to themselves
     made by the entry points (see @(tsee type-match-vars)).
     The approach is sound on any shape and pattern,
     because it only ever consumes elements that are equivalent,
     or binds a variable to exactly the elements that it must stand for.
     It is complete, modulo shape equivalence
     and under the uniqueness restriction above,
     when the shape and the pattern are normalized:
     @(tsee shape-match) and @(tsee ispace-match) ensure that,
     by normalizing both sides before matching their elements,
     which also normalizes the dimensions in them,
     as dimension matching expects."))
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

(define dim-pattern-polys-mul ((known1 dim-polyp)
                               (unknown1 dim-polyp)
                               (known2 dim-polyp)
                               (unknown2 dim-polyp))
  :returns (mv (okp booleanp) (known dim-polyp) (unknown dim-polyp))
  :short "Multiply two pairs of known and unknown polynomials,
          if the product is linear in the unknowns."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn multiplication patterns into polynomials
     (see @(tsee dim-pattern-polys-product));
     the meaning of the known and unknown polynomials of a pattern
     is explained in @(see dim-patterns-to-polys).
     A pair denotes the sum of its two polynomials,
     so the product of the pairs @('(K1, U1)') and @('(K2, U2)')
     denotes @('(K1 + U1) * (K2 + U2)').
     We compute it only when the result is still a known polynomial
     plus a linear polynomial in the unknowns without constant term:
     if @('U1') and @('U2') are both 0,
     the product is @('(K1 * K2, 0)');
     if @('U1') is 0 and @('K1') is a constant,
     the product is @('(K1 * K2, K1 * U2)'),
     because multiplying the linear polynomial @('U2') by a constant
     yields a linear polynomial without constant term,
     e.g. @('(2, 0)') times @('(1, $i)') is @('(2, 2 $i)');
     symmetrically, if @('U2') is 0 and @('K2') is a constant,
     the product is @('(K1 * K2, K2 * U1)').")
   (xdoc::p
    "In all other cases we fail,
     returning @('nil') as the flag,
     and also as the polynomials, which are irrelevant in that case.
     The product of two unknown polynomials,
     e.g. for the patterns @('(* $i $j)') and @('(* $i $i)'),
     is not linear in the unknowns.
     The product of an unknown polynomial by a non-constant known polynomial,
     e.g. for the pattern @('(* $k $i)') with @('$k') bound to @('$l'),
     would give the unknowns non-constant coefficients,
     which the matching does not handle;
     we may extend this in the future."))
  (cond ((and (omap::emptyp (dim-poly-fix unknown1))
              (omap::emptyp (dim-poly-fix unknown2)))
         (mv t (dim-poly-mul known1 known2) nil))
        ((and (omap::emptyp (dim-poly-fix unknown1))
              (dim-poly-constp known1))
         (mv t (dim-poly-mul known1 known2) (dim-poly-mul known1 unknown2)))
        ((and (omap::emptyp (dim-poly-fix unknown2))
              (dim-poly-constp known2))
         (mv t (dim-poly-mul known1 known2) (dim-poly-mul known2 unknown1)))
        (t (mv nil nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-pattern-polys-product ((knowns dim-poly-listp)
                                   (unknowns dim-poly-listp))
  :returns (mv (okp booleanp) (known dim-polyp) (unknown dim-polyp))
  :short "Multiply a list of pairs of known and unknown polynomials,
          if the product is linear in the unknowns."
  :long
  (xdoc::topstring
   (xdoc::p
    "The pairs are passed as two parallel lists,
     of known polynomials and of unknown polynomials,
     which have the same length in the intended use;
     if they do not, the extra elements of the longer list are ignored.
     We multiply the pairs via @(tsee dim-pattern-polys-mul),
     failing as soon as a product fails.
     The product of no pairs is @('(1, 0)')."))
  (b* (((when (or (endp knowns) (endp unknowns)))
        (mv t (dim-poly-const 1) nil))
       ((mv okp known unknown)
        (dim-pattern-polys-product (cdr knowns) (cdr unknowns)))
       ((unless okp) (mv nil nil nil)))
    (dim-pattern-polys-mul (car knowns) (car unknowns) known unknown))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dim-patterns-to-polys
  :short "Turn patterns and lists of patterns
          into known and unknown polynomials."
  :long
  (xdoc::topstring
   (xdoc::p
    "A pattern is a dimension whose variables are pattern variables,
     some of which may be already bound in a substitution
     (see @(tsee dims-match)).
     Since dimension equivalence is equality of polynomials
     (see @(see dimension-polynomials)),
     matching a dimension to a pattern modulo equivalence
     amounts to solving a polynomial equation:
     the polynomial of the dimension must be equal to
     the polynomial of the pattern instantiated with the substitution,
     whose unbound pattern variables are the unknowns.
     For instance, matching @('5') to the pattern @('(+ 1 $i)')
     amounts to solving @('5 = 1 + $i') for @('$i'),
     and matching @('(+ 4 (* 2 $k))') to the pattern @('(* 2 $i)')
     amounts to solving @('4 + 2 $k = 2 $i') for @('$i').")
   (xdoc::p
    "These functions turn a pattern into the right-hand side of the equation,
     split into two polynomials:
     the known polynomial, which is the polynomial of
     the part of the pattern without unbound pattern variables,
     with each bound pattern variable replaced by its binding;
     and the unknown polynomial,
     which is a linear polynomial in the unbound pattern variables,
     with integer coefficients and no constant term.
     For instance, the pattern @('(+ 1 $i $i)') yields
     the known polynomial @('1') and the unknown polynomial @('2 $i'),
     while the pattern @('(+ $i $j)'), with @('$i') bound to @('(+ 1 $k)'),
     yields the known polynomial @('1 + $k') and the unknown polynomial @('$j').
     The pattern instantiated with any values of the unbound variables
     denotes the sum of the known polynomial
     and of the unknown polynomial instantiated with those values:
     e.g. @('(+ 1 $i $i)') with @('$i') instantiated to @('3')
     denotes @('1 + 2 * 3'), i.e. @('7').
     Thus, if @('D') is the polynomial of the dimension being matched
     and @('K') and @('U') are the known and unknown polynomials,
     the matching must find values of the unknowns such that @('K + U = D'),
     i.e. such that @('U = D - K').")
   (xdoc::p
    "The two polynomials are kept separate, and must not be added together,
     because the bindings may mention variables of the dimension being matched
     that have the same names as pattern variables
     (see @(tsee dims-match)):
     with @('$i') bound to @('$j'),
     the pattern @('(+ $i $j)') yields
     the known polynomial @('$j'),
     where @('$j') is a variable of the dimension,
     and the unknown polynomial @('$j'),
     where @('$j') is a pattern variable;
     adding them would conflate the two.
     For the same reason, we do not apply the substitution to the pattern:
     we go through the pattern, looking up the bindings of its variables.")
   (xdoc::p
    "A product of unknowns,
     e.g. for the patterns @('(* $i $j)') and @('(* $i $i)'),
     would make the unknown polynomial non-linear,
     and a product of an unknown by a non-constant known polynomial,
     e.g. for the pattern @('(* $k $i)') with @('$k') bound to @('$l'),
     would give the unknowns non-constant coefficients:
     the matching does not handle these cases,
     so these functions fail on such patterns
     (see @(tsee dim-pattern-polys-mul)),
     returning @('nil') as the flag,
     and also as the polynomials, which are irrelevant in that case."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dim-pattern-to-polys ((pat dimp) (subst string-dim-mapp))
    :returns (mv (okp booleanp) (known dim-polyp) (unknown dim-polyp))
    :parents (ispace-matcher dim-patterns-to-polys)
    :short "Turn a pattern into its known and unknown polynomials."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(see dim-patterns-to-polys) for the meaning of the two polynomials.
       The rules follow @(tsee dim-to-poly),
       with the two polynomials computed side by side.")
     (xdoc::p
      "A pattern variable bound in the substitution yields
       the polynomial of its binding as the known polynomial
       and 0 as the unknown polynomial;
       this is the only place where the substitution is consulted.
       A pattern variable not bound in the substitution yields
       0 as the known polynomial
       and itself, as a factor with coefficient 1, as the unknown polynomial.
       A constant yields itself as the known polynomial
       and 0 as the unknown polynomial.")
     (xdoc::p
      "An addition yields the sums of
       the known polynomials and of the unknown polynomials of its addends.
       A subtraction with one operand yields the negations of
       the known polynomial and of the unknown polynomial of the operand;
       with two or more operands, it yields
       the known polynomial and the unknown polynomial of the first operand
       minus the sums of the ones of the other operands;
       the invalid subtraction with no operands is an indeterminate,
       as in @(tsee dim-to-poly).")
     (xdoc::p
      "A multiplication yields the product of
       the pairs of polynomials of its factors
       (see @(tsee dim-pattern-polys-product)),
       which exists only if the result is linear in the unknowns:
       e.g. @('(* 2 $i)') yields 0 and @('2 $i'),
       while @('(* $i $j)') fails."))
    (dim-case
     pat
     :var (b* ((var+dim (omap::assoc pat.name (string-dim-map-fix subst))))
            (if var+dim
                (mv t (dim-to-poly (cdr var+dim)) nil)
              (mv t nil (dim-poly-factor (dim-var pat.name)))))
     :const (mv t (dim-poly-const pat.val) nil)
     :add (b* (((mv okp knowns unknowns)
                (dim-list-pattern-to-polys pat.dims subst))
               ((unless okp) (mv nil nil nil)))
            (mv t (dim-poly-list-sum knowns) (dim-poly-list-sum unknowns)))
     :mul (b* (((mv okp knowns unknowns)
                (dim-list-pattern-to-polys pat.dims subst))
               ((unless okp) (mv nil nil nil)))
            (dim-pattern-polys-product knowns unknowns))
     :sub (b* (((when (endp pat.dims))
                (mv t (dim-poly-factor (dim-sub nil)) nil))
               ((mv okp known unknown)
                (dim-pattern-to-polys (car pat.dims) subst))
               ((unless okp) (mv nil nil nil))
               ((when (endp (cdr pat.dims)))
                (mv t (dim-poly-neg known) (dim-poly-neg unknown)))
               ((mv okp knowns unknowns)
                (dim-list-pattern-to-polys (cdr pat.dims) subst))
               ((unless okp) (mv nil nil nil)))
            (mv t
                (dim-poly-sub known (dim-poly-list-sum knowns))
                (dim-poly-sub unknown (dim-poly-list-sum unknowns)))))
    :measure (dim-count pat))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dim-list-pattern-to-polys ((pats dim-listp) (subst string-dim-mapp))
    :returns (mv (okp booleanp)
                 (knowns dim-poly-listp)
                 (unknowns dim-poly-listp))
    :parents (ispace-matcher dim-patterns-to-polys)
    :short "Turn a list of patterns into
            the lists of their known and unknown polynomials."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two lists are parallel to the list of patterns.
       We fail if any pattern fails."))
    (b* (((when (endp pats)) (mv t nil nil))
         ((mv okp known unknown) (dim-pattern-to-polys (car pats) subst))
         ((unless okp) (mv nil nil nil))
         ((mv okp knowns unknowns)
          (dim-list-pattern-to-polys (cdr pats) subst))
         ((unless okp) (mv nil nil nil)))
      (mv t (cons known knowns) (cons unknown unknowns)))
    :measure (dim-list-count pats))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual dim-patterns-to-polys))

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
     For instance, matching @('(+ 3 $i)') to the pattern @('(+ 1 $j)'),
     with @('$i') already bound to @('5') by a previous match,
     binds @('$j') to @('(+ 2 $i)'):
     applying the substitution to the pattern yields @('(+ 1 (+ 2 $i))'),
     which is equivalent to @('(+ 3 $i)'),
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

(define shape-pattern-elements-length ((pats shape-listp)
                                       (shape-subst string-shape-mapp))
  :returns (mv (okp booleanp)
               (len natp :rule-classes (:rewrite :type-prescription)))
  :short "Calculate the number of elements of a shape
          that a list of elements of a pattern needs, if determined."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to match shapes; see @(see ispace-matcher).
     The elements are the ones of a normalized pattern concatenation.
     An element that is not a shape variable needs one element of the shape.
     A shape variable bound in the substitution needs
     as many elements as its normalized binding has.
     An unbound shape variable needs an undetermined number of elements,
     in which case we fail, returning @('nil') as the flag,
     and 0 as the number, which is irrelevant in that case.")
   (xdoc::p
    "This is defined on all lists of shapes,
     treating every non-variable shape as needing one element,
     but it is intended for use on the elements of normalized concatenations
     (see @(tsee normalize-shape)),
     which do not include concatenations or splices."))
  (b* (((when (endp pats)) (mv t 0))
       (pat (car pats))
       ((mv okp len1)
        (shape-case
         pat
         :var (b* ((var+shape
                    (omap::assoc pat.name (string-shape-map-fix shape-subst)))
                   ((unless var+shape) (mv nil 0)))
                (mv t (len (shape-append->shapes
                            (normalize-shape (cdr var+shape))))))
         :dims (mv t 1)
         :append (mv t 1) ; never happens for normalized concatenations
         :splice (mv t 1))) ; never happens for normalized concatenations
       ((unless okp) (mv nil 0))
       ((mv okp len2) (shape-pattern-elements-length (cdr pats) shape-subst))
       ((unless okp) (mv nil 0)))
    (mv t (+ len1 len2)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-elements-match ((elements shape-listp)
                              (pats shape-listp)
                              (dim-subst string-dim-mapp)
                              (shape-subst string-shape-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Match the elements of a shape to the elements of a pattern shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "This realizes the approach described in @(see ispace-matcher).
     The elements are the ones of the normalized concatenations
     of the shape being matched and of the pattern
     (see @(tsee normalize-shape)).
     The two substitutions are threaded as in @(tsee shape-match).")
   (xdoc::p
    "We go through the elements of the pattern.
     A pattern element with dimensions consumes the first element of the shape,
     which must also have dimensions,
     matched via @(tsee dim-list-match);
     for normalized concatenations, both elements have a single dimension.
     A bound shape variable in the pattern consumes
     as many elements of the shape as its normalized binding has
     (see @(tsee shape-pattern-elements-length)),
     and their concatenation must be equivalent to the binding.
     An unbound shape variable in the pattern consumes
     as many elements of the shape as
     the remaining elements of the pattern leave to it
     (see @(tsee shape-pattern-elements-length)),
     and it is bound to their concatenation;
     if the remaining elements of the pattern include an unbound variable,
     the match fails.
     A concatenation or splice never occurs
     among the elements of a normalized concatenation,
     so we fail in that case.
     At the end, all the elements of the shape must have been consumed.")
   (xdoc::p
    "As explained in @(see ispace-matcher),
     this is sound on all lists of shapes,
     but it is complete,
     modulo shape equivalence and under the uniqueness restriction,
     only on the elements of normalized concatenations."))
  (b* (((when (endp pats))
        (if (endp elements)
            (mv t
                (string-dim-map-fix dim-subst)
                (string-shape-map-fix shape-subst))
          (mv nil nil nil)))
       (pat (car pats)))
    (shape-case
     pat
     :var
     (b* ((var+shape
           (omap::assoc pat.name (string-shape-map-fix shape-subst))))
       (if var+shape
           (b* ((binding (cdr var+shape))
                (n (len (shape-append->shapes (normalize-shape binding))))
                ((when (> n (len elements))) (mv nil nil nil))
                ((unless (shape-equivp binding
                                       (shape-append (take n elements))))
                 (mv nil nil nil)))
             (shape-elements-match (nthcdr n elements)
                                   (cdr pats)
                                   dim-subst
                                   shape-subst))
         (b* (((mv okp needed)
               (shape-pattern-elements-length (cdr pats) shape-subst))
              ((unless okp) (mv nil nil nil))
              ((when (> needed (len elements))) (mv nil nil nil))
              (k (- (len elements) needed))
              (shape-subst (omap::update pat.name
                                         (shape-append (take k elements))
                                         (string-shape-map-fix shape-subst))))
           (shape-elements-match (nthcdr k elements)
                                 (cdr pats)
                                 dim-subst
                                 shape-subst))))
     :dims
     (b* (((when (endp elements)) (mv nil nil nil))
          (element (car elements))
          ((unless (shape-case element :dims)) (mv nil nil nil))
          ((mv okp dim-subst)
           (dim-list-match (shape-dims->dims element) pat.dims dim-subst))
          ((unless okp) (mv nil nil nil)))
       (shape-elements-match (cdr elements)
                             (cdr pats)
                             dim-subst
                             shape-subst))
     :append (mv nil nil nil) ; never happens for normalized concatenations
     :splice (mv nil nil nil))) ; never happens for normalized concatenations
  :measure (acl2-count pats)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :prepwork ((local (in-theory (enable nthcdr-of-shape-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-match ((shape shapep)
                     (pat shapep)
                     (dim-subst string-dim-mapp)
                     (shape-subst string-shape-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Match a shape to a pattern (another shape)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is matching modulo shape equivalence,
     according to the approach described in @(see ispace-matcher):
     we normalize both the shape and the pattern
     (see @(tsee normalize-shape)),
     obtaining two concatenations,
     and we match the elements of the two concatenations
     via @(tsee shape-elements-match).
     Note that the shape variables of the pattern
     are bound to normalized concatenations,
     e.g. @('(++ (dims 2))') rather than @('(dims 2)').")
   (xdoc::p
    "Since shapes contain both dimension variables and shape variables,
     the matching builds two substitutions,
     one for dimension variables and one for shape variables.
     Both are threaded through the matching of the elements,
     analogously to the single substitution in @(tsee dims-match),
     and both are meant to be applied simultaneously,
     as @(tsee shape-subst-ispace-vars)
     and @(tsee ispace-subst-ispace-vars) do.
     If the matching fails, @('nil') is returned as both substitutions."))
  (shape-elements-match (shape-append->shapes (normalize-shape shape))
                        (shape-append->shapes (normalize-shape pat))
                        dim-subst
                        shape-subst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-match ((ispace ispacep)
                      (pat ispacep)
                      (dim-subst string-dim-mapp)
                      (shape-subst string-shape-mapp))
  :returns (mv (okp booleanp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Match an ispace to a pattern (another ispace)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee shape-match), but for ispaces:
     we normalize both the ispace and the pattern
     (see @(tsee normalize-ispace)),
     obtaining two shape ispaces with concatenations,
     and we match the elements of the two concatenations
     via @(tsee shape-elements-match).
     Thus, a dimension ispace is matched as
     the shape with that single dimension;
     see @(see ispace-matcher)."))
  (shape-elements-match
   (shape-append->shapes (ispace-shape->shape (normalize-ispace ispace)))
   (shape-append->shapes (ispace-shape->shape (normalize-ispace pat)))
   dim-subst
   shape-subst))
