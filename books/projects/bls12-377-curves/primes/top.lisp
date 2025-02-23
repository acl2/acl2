; bls12-377-curves Library
;
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "std/util/add-io-pairs" :dir :system)

(acl2::merge-io-pairs
 dm::primep
 (include-book "bls12-377-base-prime")
 (include-book "bls12-377-prime")
 (include-book "edwards-bls12-377-subgroup-prime"))
