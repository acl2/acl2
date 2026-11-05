; Ethereum Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "addresses")

;; Attach the executable pieces needed to calculate addresses.
(include-book "kestrel/crypto/attachments/keccak-256" :dir :system)
(include-book "kestrel/crypto/ecurve/secp256k1-attachment" :dir :system)

(include-book "kestrel/utilities/strings/hexstrings" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Known-answer tests with values published outside this code base.

;; The private key used in the example of
;; https://github.com/ethereum/EIPs/blob/master/EIPS/eip-155.md
;; (also used in transactions-tests.lisp),
;; whose address is the sender of the example transaction.
(assert-event
 (equal (private-key-to-address
         #x4646464646464646464646464646464646464646464646464646464646464646)
        (acl2::hexstring=>ubyte8s "9d8a62f656a8d1615c1294fd71e9cfb3e4855a4f")))

;; The default accounts 0 and 1 of the Hardhat and Anvil development tools.
(assert-event
 (equal (private-key-to-address
         #xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80)
        (acl2::hexstring=>ubyte8s "f39fd6e51aad88f6f4ce6ab8827279cfffb92266")))

(assert-event
 (equal (private-key-to-address
         #x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d)
        (acl2::hexstring=>ubyte8s "70997970c51812dc3a010c7d01b50e0d17dc79c8")))

;; The 64 bytes hashed for an address are
;; the SEC 1 uncompressed form without its leading byte 4.
(assert-event
 (b* ((pub (secp256k1-priv-to-pub
            #xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80)))
   (equal (secp256k1-point-to-bytes pub nil)
          (cons 4 (public-key-to-bytes pub)))))
