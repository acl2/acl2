; Proving equivalence between the sha-3 spec and the spec from ../keccak
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/crypto/keccak/keccak" :dir :system)
(include-book "kestrel/crypto/sha-3/sha-3" :dir :system)
(include-book "kestrel/axe/equivalence-checker" :dir :system)
(include-book "kestrel/axe/unroll-spec-basic" :dir :system)

;; TODO: Add proofs for longer messages, or even a general proof for arbitrary messages

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Assumes a 256-bit message
(acl2::unroll-spec-basic *sha-3-keccak-256-256bit*
                   `(sha3::keccak-256 ,(acl2::symbolic-list 'in 256))
                   :rules :auto
                   :extra-rules '(acl2::len-of-cdr
                                  acl2::car-of-nthcdr
                                  acl2::update-nth-of-cons
                                  acl2::car-becomes-nth-of-0
                                  acl2::cdr-of-append
                                  acl2::consp-when-len-equal-constant
                                  acl2::consp-when-len-equal-constant-alt
                                  acl2::consp-of-cdr
                                  acl2::nth-of-cdr))

;; Assumes a 256-bit message
(acl2::unroll-spec-basic *keccak-256-256bit*
                         `(keccak::keccak-256 ,(acl2::symbolic-list 'in 256))
                         :rules :auto
                         :extra-rules '(acl2::len-of-cdr
                                        acl2::car-of-nthcdr
                                        acl2::update-nth-of-cons
                                        acl2::car-becomes-nth-of-0
                                        acl2::cdr-of-append
                                        acl2::consp-when-len-equal-constant
                                        acl2::consp-when-len-equal-constant-alt
                                        acl2::consp-of-cdr
                                        acl2::nth-of-cdr
                                        acl2::leftrotate))

(acl2::prove-equivalence *sha-3-keccak-256-256bit*
                         *keccak-256-256bit*
                         ;; :initial-rule-sets (list (make-axe-rules! (amazing-rules-bv) (w state))) ;don't bit-blast
                         :normalize-xors nil ; todo: heap exhaustion (many xor nests, each with thousands of nodes, dag grows without bound) !
                         :tactic :rewrite-and-sweep)
