; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defrule" :dir :system)

(include-book "jenkins-hash")

(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash (x)
  (declare (xargs :type-prescription (natp (hash x))))
  :returns (hash (unsigned-byte-p 32 hash))
  :parents (implementation)
  :short "The hash function used by @('heap<')."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee jenkins-hash). This function is
      defined to allow us to easily switch hash functions if needed. To hash
      objects (e.g., for use with @(tsee heap<-with-hashes)), users should call
      this function instead of @(tsee jenkins-hash)."))
  (jenkins-hash x)
  :no-function t
  :inline t)
