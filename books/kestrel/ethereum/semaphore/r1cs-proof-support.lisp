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

(include-book "kestrel/crypto/r1cs/tools/axe-prover-r1cs" :dir :system)
(include-book "kestrel/ethereum/semaphore/lift-semaphore-r1cs" :dir :system)
(include-book "kestrel/ethereum/semaphore/json-to-r1cs/load-circom-json" :dir :system)
(include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)
(include-book "kestrel/ethereum/semaphore/printing" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/crypto/r1cs/fe-listp-fast" :dir :system)
