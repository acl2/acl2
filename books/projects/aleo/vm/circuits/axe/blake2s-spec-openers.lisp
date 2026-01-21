; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "support-blake2s")
;(include-book "kestrel/crypto/r1cs/tools/lift-r1cs-new" :dir :system)
;(include-book "kestrel/axe/prover-basic" :dir :system)
;(include-book "kestrel/axe/dag-info" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/crypto/blake/blake2s" :dir :system)

;;;
;;; unroll the spec (just to see what's there)
;;;

(acl2::defopeners blake::bytes-to-blocks)
(acl2::defopeners blake::bytes-to-words)
(acl2::defopeners blake::words-to-bytes)
(acl2::defopeners blake::f-loop-1)
(acl2::defopeners blake::f-loop-2)
(acl2::defopeners blake::loop1)

(acl2::def-constant-opener acl2::bvshr)
(acl2::def-constant-opener acl2::slice)
(acl2::def-constant-opener acl2::logtail$inline)

(defthm blake::bytes-to-blocks-base-2
  (implies (equal 0 (len blake::bytes))
           (equal (blake::bytes-to-blocks blake::bytes)
                  'nil)))

;todo: introduce vars for blake input bytes
;; (acl2::def-simplified *spec-unrolled*
;;                       '(blake::blake2s data-bytes nil 32) ; no key
;;                       :assumptions '((equal (len data-bytes) 64)
;;                                      (true-listp data-bytes)
;;                                      (equal key-bytes nil))
;;                       :monitor '( ;;BLAKE::LEN-OF-BYTES-TO-BLOCKS
;;                                  BLAKE::BYTES-TO-BLOCKS-BASE-2
;;                                  ;;BLAKE::BYTES-TO-WORDS-UNROLL
;;                                  )
;;                       :rules (append (acl2::list-rules)
;;                                      '(ACL2::CONSP-OF-NTHCDR
;;                                        acl2::len-of-nthcdr
;;                                        acl2::nthcdr-of-nthcdr)
;;                                      (acl2::base-rules)
;;                                      '(BLAKE::BLAKE2S
;;                                        BLAKE::D-BLOCKS
;;                                        BLAKE::PAD-DATA-BYTES
;;                                        BLAKE::BYTES-TO-BLOCKS-BASE-2
;;                                        BLAKE::BYTES-TO-BLOCKS-UNROLL
;;                                        ACL2::CONSP-WHEN-LEN-EQUAL
;;                                        ACL2::CONSP-WHEN-LEN-EQUAL-alt
;;                                        ;;endp
;;                                        BLAKE::BYTES-TO-BLOCK
;;                                        BLAKE::BYTES-TO-WORDS-BASE
;;                                        BLAKE::BYTES-TO-WORDS-UNROLL
;;                                        ;; ACL2::NTHCDR-WHEN-EQUAL-OF-LEN
;;                                        BLAKE::BYTES-TO-WORD
;;                                        BLAKE::BLAKE2S-MAIN
;;                                        BLAKE::F
;;                                        BLAKE::f-LOOP-1-BASE
;;                                        BLAKE::f-LOOP-1-UNROLL
;;                                        BLAKE::f-LOOP-2-BASE
;;                                        BLAKE::f-LOOP-2-UNROLL
;;                                        BLAKE::LOOP1-BASE
;;                                        BLAKE::LOOP1-UNROLL
;;                                        BLAKE::WORDXOR
;;                                        blake::g
;;                                        BLAKE::ROT-WORD
;;                                        ACL2::NTH-OF-NTHCDR
;;                                        BLAKE::LEN-OF-BYTES-TO-BLOCKS
;;                                        blake::sigma
;;                                        BLAKE::IV
;;                                        BLAKE::WORDS-TO-BYTES-BASE
;;                                        BLAKE::WORDS-TO-BYTES-UNROLL
;;                                        BLAKE::WORD-TO-BYTES
;;                                        mod-of-+-of-4294967296
;;                                        ACL2::BVPLUS-OF-+-ARG2
;;                                        ACL2::BVPLUS-OF-+-ARG3
;;                                        ACL2::UPDATE-NTH-OF-UPDATE-NTH-SAME
;;                                        ACL2::CDR-OF-UPDATE-NTH
;;                                        ACL2::CAR-OF-UPDATE-NTH
;;                                        ACL2::BVSHL-OF-0-ARG2
;;                                        ACL2::BVSHR-CONSTANT-OPENER
;;                                        ACL2::slice-CONSTANT-OPENER
;;                                        ACL2::LOGTAIL$INLINE-CONSTANT-OPENER
;;                                        ACL2::EXPT2$INLINE
;;                                        ACL2::ifloor$INLINE
;;                                        ACL2::BVPLUS-COMBINE-CONSTANTS
;;                                        )

;;                                      (acl2::type-rules)))

;(acl2::dag-fns *SPEC-UNROLLED*)
