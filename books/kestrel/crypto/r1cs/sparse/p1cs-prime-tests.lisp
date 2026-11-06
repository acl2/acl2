; Tests that the primes in p1cs are the primes defined with defprime.
;
; Copyright (C) 2026 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (bendyarm on GitHub)

(in-package "R1CS")

;; This is separate from p1cs-tests.lisp because the books that define the
;; primes install I/O pairs for primep, which p1cs itself avoids.

(include-book "p1cs")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/util/add-io-pairs" :dir :system)

;; Each of these books adds I/O pairs for primep, so including both needs
;; merge-io-pairs.
(acl2::merge-io-pairs
  dm::primep
  (include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)
  (include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system))

(acl2::assert-equal (fp1) (primes::bn-254-group-prime))
(acl2::assert-equal (fp2) (primes::bls12-377-scalar-field-prime))
