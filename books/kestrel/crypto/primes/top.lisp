(in-package "PRIMES")

(include-book "bn-254-group-prime")
(acl2::merge-io-pairs
 dm::primep
 (include-book "bls12-381-prime")
 (include-book "secp256k1-field-prime")
 (include-book "goldilocks-field-prime"))
