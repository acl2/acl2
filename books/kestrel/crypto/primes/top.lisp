(in-package "PRIMES")

(include-book "bn-254-group-prime")
(acl2::merge-io-pairs
 rtl::primep
 (include-book "bls12-377-prime")
 (include-book "bls12-381-prime")
 (include-book "secp256k1-field-prime"))
