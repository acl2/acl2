; Supporting utilities for R1CS proofs
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

;; Common proof tools and utilities for R1CS proofs.  Doesn't include many rules (yet).

(include-book "lift-semaphore-r1cs")
(include-book "verify-semaphore-r1cs")
(include-book "printing")
(include-book "json-to-r1cs/load-circom-json")
(include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/prime-fields/fe-listp-fast" :dir :system)
