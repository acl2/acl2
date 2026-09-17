; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-checker")

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
     or perhaps we will add a separate unifier."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dims-match
  :short "Match dimensions to patterns (other dimensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we perform a purely syntactical match,
     which is incomplete with respect to dimension equivalence.
     For instance, the pattern @('(+ 1 n)')
     is not matched by the dimension @('5'),
     even though replacing @('n') with @('4') in the pattern
     yields a dimension equivalent to @('5').
     We will need to extend this to matching modulo equivalence,
     i.e. to finding a substitution that makes the pattern
     equivalent (not just equal) to the dimension.")
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
     applying it to the pattern yields the dimension.
     The variables of the dimension are not pattern variables,
     but they may have the same names as pattern variables,
     in which case the dimensions in the substitution mention those names;
     thus, the substitution must not be applied repeatedly
     or composed with itself.
     For instance, matching @('(+ 3 i)') to the pattern @('(+ i j)')
     yields a substitution that maps @('i') to @('3') and @('j') to @('i'):
     applying it to the pattern yields @('(+ 3 i)'),
     but applying it once more would yield @('(+ 3 3)')."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define dim-match ((dim dimp) (pat dimp) (subst string-dim-mapp))
    :returns (mv (okp booleanp) (new-subst string-dim-mapp))
    :parents (ispace-matcher dims-match)
    :short "Match a dimension to a pattern (another dimension)."
    :long
    (xdoc::topstring
     (xdoc::p
      "A pattern variable that is bound in the substitution
       matches only the dimension bound to it.
       A pattern variable that is not bound in the substitution
       matches any dimension, which is bound to the variable.")
     (xdoc::p
      "A pattern constant matches only the same constant.")
     (xdoc::p
      "A pattern addition matches only an addition
       whose dimensions match the dimensions of the pattern,
       in the same order.
       Multiplications and subtractions are treated like additions."))
    (dim-case
     pat
     :var (b* ((subst (string-dim-map-fix subst))
               (var+dim (omap::assoc pat.name subst)))
            (cond ((not var+dim)
                   (mv t (omap::update pat.name (dim-fix dim) subst)))
                  ((equal (cdr var+dim) (dim-fix dim))
                   (mv t subst))
                  (t (mv nil nil))))
     :const (if (equal (dim-fix dim) (dim-const pat.val))
                (mv t (string-dim-map-fix subst))
              (mv nil nil))
     :add (if (dim-case dim :add)
              (dim-list-match (dim-add->dims dim) pat.dims subst)
            (mv nil nil))
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
