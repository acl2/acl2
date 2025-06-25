(in-package "PRIMES")

(include-book "baby-jubjub-subgroup-prime")
(acl2::merge-io-pairs
 dm::primep
 (include-book "bls12-381-prime")
 (include-book "bn-254-group-prime")
 (include-book "ed25519-base-prime")
 (include-book "ed25519-group-prime")
 (include-book "goldilocks-field-prime")
 (include-book "jubjub-subgroup-prime")
 (include-book "nist-p-256-base-prime")
 (include-book "nist-p-256-group-prime")
 (include-book "secp256k1-field-prime")
 (include-book "secp256k1-group-prime"))
