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
(include-book "sparse-approximation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omp
  :parents (acl2::projects acl2::kestrel-books)
  :short "An ACL2(r) library for OMP (Orthogonal Matching Pursuit)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library is only available in "
    (xdoc::seetopic "acl2::real" "ACL2(r)") ".")
   (xdoc::p
    "@('OMP') is a greedy algorithm for sparse approximation:
     given a signal @($x \\in \\mathbb{R}^d$),
     a dictionary @($D$) of @($N$) unit-norm atoms in @($\\mathbb{R}^d$),
     and a sparsity budget @($k$),
     find a coefficient vector @($c \\in \\mathbb{R}^N$) with at most
     @($k$) nonzero entries that minimizes @($\\|x - \\Phi c\\|_2$),
     where @($\\Phi$) is the matrix whose columns are the atoms of @($D$).")
   (xdoc::p
    "The library is structured in two layers:")
   (xdoc::ul
    (xdoc::li
     "@(see dictionary) -- dictionaries, completeness, redundancy, and frames.")
    (xdoc::li
     "@(see sparse-approximation) -- the two standard problem
      formulations (tolerance-constrained and budget-constrained)
      and their optimality predicates."))
   (xdoc::p
    "The vector and norm infrastructure is inherited from
     @('books/workshops/2018/kwan-greenstreet/'),
     which is why ACL2(r) is required (the books are marked
     @('uses-acl2r') in their build certification parameters).")
   (xdoc::p
    "The reference companion paper is:")
   (xdoc::p
    "J. A. Tropp, \"Greed is Good: Algorithmic Results for Sparse
     Approximation,\" IEEE Trans. Info. Theory 50(10), 2004.
     @('https://users.cms.caltech.edu/~jtropp/papers/Tro04-Greed-Good.pdf')")
   (xdoc::p
    "Section II (\"Background\") of that paper is the source of
     conventions for the dictionary and frame definitions; the
     tolerance / budget formulations follow its (Sparse) and
     (Sparsity) problems."))
  :order-subtopics t)
