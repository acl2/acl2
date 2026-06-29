; OMP Library
; (Orthogonal Matching Pursuit)
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (uses-acl2r)

(in-package "OMP")

(include-book "dictionary")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ sparse-approximation
  :parents (omp)
  :short "The sparse approximation problem and its two standard formulations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library is only available in "
    (xdoc::seetopic "acl2::real" "ACL2(r)") ".")
   (xdoc::p
    "Fix a signal @($x \\in \\mathcal{H} = \\mathbb{R}^d$), a
     dictionary @($D$) with @($N$) atoms (in matrix view, @($\\Phi
     \\in \\mathbb{R}^{d \\times N}$)), a sparsity budget @($k \\in
     \\mathbb{N}$) with @($k \\ll N$), and a tolerance @($\\epsilon
     \\ge 0$).  The sparse approximation problem has two standard
     forms:")
   (xdoc::ol
    (xdoc::li
     "<b>Tolerance-constrained.</b>
      Minimize @($\\|c\\|_0$) over @($c \\in \\mathbb{R}^N$) subject
      to @($\\|x - \\Phi c\\|_2 \\le \\epsilon$).
      See @(tsee tolerance-feasiblep) and @(tsee tolerance-optimalp).")
    (xdoc::li
     "<b>Budgeted (sparsity-constrained).</b>
      Minimize @($\\|x - \\Phi c\\|_2$) over @($c \\in \\mathbb{R}^N$)
      subject to @($\\|c\\|_0 \\le k$).
      See @(tsee budget-feasiblep) and @(tsee budget-optimalp)."))
   (xdoc::p
    "Here @($\\|c\\|_0 := |\\{i : c_i \\neq 0\\}|$) is the size of the
     <b>support</b> of @($c$) -- the so-called \"@($\\ell_0$) norm\",
     which fails homogeneity and so is not a norm in the topological
     sense.  We call it @(tsee support-size) below to avoid the abuse.")
   (xdoc::p
    "Geometrically, @($\\Sigma_k = \\{c \\in \\mathbb{R}^N : \\|c\\|_0
     \\le k\\}$) is a finite union of @($k$)-dimensional coordinate
     subspaces of @($\\mathbb{R}^N$), not itself a linear space.
     Form (1) minimizes the nonconvex objective @($\\|c\\|_0$) over a
     convex feasible set (a sublevel set of the residual norm); form
     (2) minimizes a convex objective over the nonconvex set
     @($\\Sigma_k$).  Either way the nonconvexity of @($\\ell_0$) is
     the source of all the algorithmic difficulty; convex relaxations
     (basis pursuit) and greedy algorithms (@('OMP')) are the two main
     practical approaches.")
   (xdoc::p
    "Both norm comparisons (@($\\|x - \\Phi c\\|_2 \\le \\epsilon$) and
     \"minimize @($\\|x - \\Phi c\\|_2$)\") are stated via their
     squares, which is equivalent over nonnegative reals and keeps us
     free of @('sqrt').  Where the textbook says \"tolerance
     @($\\epsilon$)\", we parameterize by @($\\epsilon^2$) (named
     @('eps-sq')) for the same reason."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Support and the l_0 "norm".
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define support-size ((c t))
  :returns (n natp :rule-classes :type-prescription)
  :short "Number of nonzero (real) entries of @($c$) -- the size of
          its support."
  :long
  (xdoc::topstring
   (xdoc::p
    "Same value whether or not @($c$) is a @(see real-listp), but the
     intended domain is real coefficient vectors.  Non-real entries
     pass through as zero (i.e., they do not contribute to the
     count)."))
  (cond ((atom c) 0)
        (t (+ (if (and (realp (car c))
                       (not (equal (car c) 0)))
                  1
                0)
              (support-size (cdr c))))))

(define k-sparsep ((c t) (k natp))
  :returns (ok booleanp)
  :short "@($c$) is @($k$)-sparse: at most @($k$) nonzero entries."
  :long
  (xdoc::topstring
   (xdoc::p
    "@($\\Sigma_k$) is the set of @($k$)-sparse coefficient vectors
     in @($\\mathbb{R}^N$).")
   (xdoc::p
    "Like @(tsee support-size), this is left polymorphic -- non-real
     entries pass through as zero -- so the @($\\mathbb{R}^N$) domain
     constraint is enforced one level up in @(tsee budget-feasiblep),
     which conjoins @('(real-listp c)') before testing sparsity."))
  (<= (support-size c) (nfix k)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Residual and its squared norm.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define residual ((x t) (c t) (d t) (dim natp))
  :guard (and (real-listp x)
              (equal (len x) (nfix dim))
              (real-listp c)
              (dictionaryp d dim)
              (equal (len c) (n-atoms d)))
  :returns (r real-listp)
  :short "The residual @($r = x - \\Phi c$),
          computed via @('vec-+') and @('scalar-*') to avoid
          committing to a particular name for vector subtraction."
  (vec-+ x (scalar-* -1 (linear-combo c d dim)))
  ///
  (defthm len-of-residual
    (implies (and (real-listp x)
                  (equal (len x) (nfix dim))
                  (real-listp c)
                  (dictionaryp d dim)
                  (equal (len c) (n-atoms d)))
             (equal (len (residual x c d dim)) (nfix dim)))
    :hints (("Goal" :in-theory (enable residual))))
  (defthm vectorp-of-residual
    (implies (and (vectorp x dim)
                  (real-listp c)
                  (dictionaryp d dim)
                  (equal (len c) (n-atoms d)))
             (vectorp (residual x c d dim) dim))
    :hints (("Goal" :in-theory (enable vectorp)))))

(define residual-norm^2 ((x t) (c t) (d t) (dim natp))
  :guard (and (real-listp x)
              (equal (len x) (nfix dim))
              (real-listp c)
              (dictionaryp d dim)
              (equal (len c) (n-atoms d)))
  :returns (s realp :rule-classes :type-prescription)
  :short "@($\\|x - \\Phi c\\|^2$): the squared norm of the residual."
  :long
  (xdoc::topstring
   (xdoc::p
    "Comparing residuals through their squares is equivalent to
     comparing 2-norms, since @('norm^2') is monotone in the norm for
     nonnegative values."))
  (norm^2 (residual x c d dim))
  ///
  (defthm nonneg-of-residual-norm^2
    (<= 0 (residual-norm^2 x c d dim))
    :rule-classes ((:rewrite) (:linear))
    :hints (("Goal" :in-theory (enable residual-norm^2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tolerance-constrained sparse approximation problem.
;;
;;   minimize  ||c||_0  subject to  ||x - Phi c||_2  <=  eps
;;   (equivalently,                  ||x - Phi c||^2 <=  eps^2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tolerance-feasiblep ((c t) (d t) (dim natp)
                             (x t) (eps-sq realp))
  :guard (and (vectorp x dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "Recognize coefficient vectors @($c$) lying inside the
          tolerance ball, with the correct shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "The c-shape predicates (@('(real-listp c)') and the length
     constraint) stay in the body, not the guard, because
     @(tsee tolerance-supp-lower-boundp) universally quantifies over
     candidate vectors and calls this on each witness."))
  (and (real-listp c)
       (equal (len c) (n-atoms d))
       (realp eps-sq)
       (<= 0 eps-sq)
       (<= (residual-norm^2 x c d dim) eps-sq)))

(define-sk tolerance-supp-lower-boundp (c d dim x eps-sq)
  :guard (and (natp dim)
              (realp eps-sq)
              (vectorp x dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "@(tsee support-size) of @($c$) is a lower bound on the
          supports of all tolerance-feasible candidates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does <b>not</b> require @($c$) itself to be feasible -- a
     vector with @('support-size 0') trivially witnesses it.  See
     @(tsee tolerance-optimalp) for the optimality predicate that
     adds feasibility.")
   (xdoc::p
    "The guard mirrors @(tsee tolerance-feasiblep)'s full guard (after
     @(see define) adds the formal-type guards): @('(natp dim)') and
     @('(realp eps-sq)') in addition to the dictionary shape."))
  (forall c2
    (implies (tolerance-feasiblep c2 d dim x eps-sq)
             (<= (support-size c)
                 (support-size c2)))))

(define tolerance-optimalp ((c t) (d t) (dim natp)
                            (x t) (eps-sq realp))
  :guard (and (vectorp x dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "@($c$) is optimal for the tolerance-constrained problem:
          it is itself tolerance-feasible AND no tolerance-feasible
          candidate has strictly smaller support."
  (and (tolerance-feasiblep c d dim x eps-sq)
       (tolerance-supp-lower-boundp c d dim x eps-sq)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Budgeted (sparsity-constrained) sparse approximation problem.
;;
;;   minimize  ||x - Phi c||_2  subject to  ||c||_0 <= k
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define budget-feasiblep ((c t) (d t) (k natp))
  :returns (ok booleanp)
  :short "Recognize @($k$)-sparse coefficient vectors of the right shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "The support-size check is dimension-agnostic, so @($\\mathit{dim}$)
     is not threaded in here; the @('(dictionaryp d dim)') precondition
     is established by callers.")
   (xdoc::p
    "The c-shape predicates stay in the body (not the guard) for the
     same reason as in @(tsee tolerance-feasiblep):
     @(tsee budget-residual-lower-boundp) universally quantifies over
     candidates @('c2') and calls @('(budget-feasiblep c2 d k)') on
     the witness."))
  (and (real-listp c)
       (equal (len c) (n-atoms d))
       (k-sparsep c k))
  ///
  (defthm real-listp-when-budget-feasiblep
    (implies (budget-feasiblep c d k)
             (real-listp c))
    :rule-classes (:rewrite :forward-chaining))
  (defthm len-when-budget-feasiblep
    (implies (budget-feasiblep c d k)
             (equal (len c) (n-atoms d)))))

(define-sk budget-residual-lower-boundp (c d dim x k)
  :guard (and (natp dim)
              (natp k)
              (vectorp x dim)
              (real-listp c)
              (dictionaryp d dim)
              (equal (len c) (n-atoms d)))
  :returns (ok booleanp)
  :short "@($\\|x - \\Phi c\\|^2$) is a lower bound on the residual
          norm^2 of all budget-feasible candidates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does <b>not</b> require @($c$) itself to be feasible -- see
     @(tsee budget-optimalp) for the predicate that adds feasibility.")
   (xdoc::p
    "The @('implies') form is auto-translated to @('if') in the
     function body by @(see define-sk) (see @(see
     std::define-sk-implies-handling)), so guard verification of
     @(tsee residual-norm^2) on the unconstrained witness @('c2')
     case-splits on @('(budget-feasiblep c2 d k)') being true.  The
     @('-necc') rewrite still reads with @('implies')."))
  (forall c2
    (implies (budget-feasiblep c2 d k)
             (<= (residual-norm^2 x c d dim)
                 (residual-norm^2 x c2 d dim)))))

(define budget-optimalp ((c t) (d t) (dim natp)
                         (x t) (k natp))
  :guard (and (vectorp x dim)
              (dictionaryp d dim))
  :returns (ok booleanp)
  :short "@($c$) is optimal for the budgeted problem:
          it is itself budget-feasible AND no budget-feasible
          candidate has strictly smaller residual^2."
  (and (budget-feasiblep c d k)
       (budget-residual-lower-boundp c d dim x k)))
