; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Proof support for R1CS proofs

(include-book "kestrel/crypto/r1cs/proof-support" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/utilities/split-list-fast-rules" :dir :system)
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system)

;; the default evisceration put in for this prime is too verbose:
(table acl2::evisc-table 8444461749428370424248824938781546531375899335154063827935233455917409239041 "<p>")
