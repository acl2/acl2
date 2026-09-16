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
     but we will need to extend that.")
   (xdoc::p
    "The variables in the patterns are the pattern variables.
     The matching builds a substitution for the pattern variables,
     which is threaded through these functions as an additional argument,
     so that it can be extended by successive matches
     (e.g. of the elements of a list);
     it is initially empty.
     If the matching succeeds, the resulting substitution is returned;
     if the matching fails, @('nil') is returned as the substitution,
     which is irrelevant in that case."))

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

; TODO: continue (shapes and ispaces)
