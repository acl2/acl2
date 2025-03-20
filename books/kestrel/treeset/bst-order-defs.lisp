; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "hash")
(include-book "total-order")

(set-induction-depth-limit 0)

(local (include-book "bst-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst< (x y)
  (declare (xargs :type-prescription (booleanp (bst< x y))))
  :short "The total order used by @(tsee bst-p)."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee <<). It is provided so that we may
      easily switch the total order to experiment with performance."))
  (<< x y)
  :no-function t
  :inline t)

(define bst<-with-hashes (x y hash-x hash-y)
  (declare (xargs :type-prescription
                  (booleanp (bst<-with-hashes x y hash-x hash-y)))
           (ignore hash-x hash-y))
  :short "Variant of @(tsee bst<) which may use pre-computed hashes."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is currently a dummy function warpping @(tsee bst<). It is provided
      in case we wish to change the order to make use of hash values, as @(tsee
      heap<) currently does."))
  (bst< x y)
  :enabled t
  :no-function t
  :inline t)
