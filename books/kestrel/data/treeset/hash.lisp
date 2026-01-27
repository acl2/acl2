; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/hash/jenkins-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/hash/jenkins" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash (x)
  :returns (hash (unsigned-byte-p 32 hash))
  :parents (implementation)
  :short "The hash function used by @('heap<')."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is just a wrapper around @(tsee hash::jenkins). This function is
      defined to allow us to easily switch hash functions if needed. To hash
      objects (e.g., for use with @(tsee heap<-with-hashes)), users should call
      this function instead of @(tsee hash::jenkins)."))
  (hash::jenkins x)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t hash)))

(defrule hash-type-prescription
  (natp (hash x))
  :rule-classes :type-prescription
  :enable hash)

(define acl2-number-hash
  ((x acl2-numberp))
  (mbe :logic (hash x)
       :exec (hash::acl2-number-jenkins x))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable hash))))

(define symbol-hash
  ((x symbolp))
  (mbe :logic (hash x)
       :exec (hash::symbol-jenkins x))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable hash))))

(define eqlable-hash
  ((x eqlablep))
  (mbe :logic (hash x)
       :exec (hash::eqlable-jenkins x))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable hash))))
