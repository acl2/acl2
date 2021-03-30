; Rules and rule lists for proving things about mimc
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE") ;change?

(include-book "mimcsponge")
(include-book "kestrel/prime-fields/rule-lists" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/arithmetic-light/mod" :dir :system)

(acl2::defopeners mimc::mimc-2p/p-block-cipher-body)

(defun mimc-spec-rules ()
  (declare (xargs :guard t))
  (append '(mimc::mimcsponge-semaphore
            mimc::mimcsponge
            mimc::mimcsponge-absorb
            mimc::mimcsponge-squeeze
            mimc::mimc-2p/p-permutation
            mimc::mimc-2p/p-block-cipher
            mimc::mimc-2p/p-block-cipher-body-base
            mimc::mimc-2p/p-block-cipher-body-unroll
            pfield::pow-of-0-arg2
            pfield::fep-of-0
            pfield::add-of-0-arg1-gen
            pfield::add-of-0-arg2-gen
            pfield::mul-of-1-arg1
            ;; pfield::mul-of-1-arg1-gen
            pfield::mul-of-1-arg2
            pfield::fep-of-mod
            acl2::integerp-of-mod
            pfield::integerp-when-fep
            acl2::fix-when-acl2-numberp
            acl2::acl2-numberp-when-integerp
            acl2::rationalp-when-integerp
            acl2::mod-of-mod-same-arg2
            posp
            pfield::mul-of-mod-arg1
            pfield::mul-of-mod-arg2
            pfield::integerp-of-add
            pfield::add-of-mod-arg1
            pfield::add-of-mod-arg2
            pfield::add-of-ifix-arg1
            pfield::add-of-ifix-arg2
            pfield::mul-of-ifix-arg1
            pfield::mul-of-ifix-arg2
            acl2::integerp-of-ifix
            acl2::ifix-does-nothing
            primes::bn-254-group-prime
            mimc::mimc-feistel-220-constants)
          (pfield::prime-field-proof-rules)))
