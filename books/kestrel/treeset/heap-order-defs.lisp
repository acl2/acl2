; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "total-order")
(include-book "hash")

(set-induction-depth-limit 0)

(local (include-book "heap-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc heap<
  :parents (implementation))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define heap<-with-hashes (x y hash-x hash-y)
  :guard (and (unsigned-byte-p 32 hash-x)
              (unsigned-byte-p 32 hash-y)
              (int= (hash x) hash-x)
              (int= (hash y) hash-y))
  (declare (type (unsigned-byte 32) hash-x)
           (type (unsigned-byte 32) hash-y)
           (xargs :type-prescription
                  (booleanp (heap<-with-hashes x y hash-x hash-y)))
           (optimize (speed 3) (safety 0)))
  :short "Variant of @(tsee heap<) which uses pre-computed hashes."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this variant of @('heap<') just ignores the @('hash-x') and
      @('hash-y') arguments, but in execution, these hash values are used
      instead of calculated new hashe values. This may be more efficient when
      used to avoid recalculating hashes.")
   (xdoc::p
     "For instance, instead of @('(and (heap< x y) (heap< y z))'), one may
      do:")
   (xdoc::codeblock
     "(let ((hash-x (hash x))"
     "      (hash-y (hash y))"
     "      (hash-z (hash z)))"
     "  (and (heap< x y hash-x hash-y)"
     "       (heap< y z hash-y hash-z)))")
   (xdoc::p
     "This performs just one call of @('(hash y)') instead of two."))
  (mbe :logic (or (< (hash x) (hash y))
                  (and (equal (hash x) (hash y))
                       (<< x y)))
       :exec (or (< hash-x hash-y)
                 (and (int= hash-x hash-y)
                      (<< x y))))
  :no-function t
  :inline t)

(define heap< (x y)
  (declare (xargs :type-prescription (booleanp (heap< x y)))
           (optimize (speed 3) (safety 0)))
  :parents nil
  (let ((hash-x (hash x))
        (hash-y (hash y)))
    (declare (type (unsigned-byte 32) hash-x)
             (type (unsigned-byte 32) hash-y))
    (heap<-with-hashes x y hash-x hash-y))
  :no-function t
  :inline t)
