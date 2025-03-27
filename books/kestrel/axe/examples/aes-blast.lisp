; Bit-blasting the spec for AES-128
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also aes-blast-boolean.lisp

(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/rewriter-basic" :dir :system)
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)

;; Unroll the spec:
(unroll-spec-basic *aes-128-encrypt-spec-dag*
                   ;; The result here is a list of 16 bytes:
                   `(aes::aes-128-encrypt ,(bit-blasted-symbolic-byte-list 'in 16) ; 16 bytes of input
                                          ,(bit-blasted-symbolic-byte-list 'key 16)) ; AES-128 has 128 key bits (= 16 bytes)
                   :rules :auto
                   :extra-rules (append (bit-blast-rules)
                                        (introduce-bv-array-rules)) ; turns nth into bv-array-read
                   )

(def-simplified-basic *aes-128-encrypt-spec-dag-bit-blasted*
  *aes-128-encrypt-spec-dag*
  :rules (append '(bv-array-read-blast-one-step
                   bitor-becomes-bitnot-of-bitand-of-bitnot-and-bitnot
                   bitxor-becomes-bitor-of-bitand-of-bitnot-and-bitand-of-bitnot)
                 (core-rules-bv) (type-rules)))

;; Now, doing (dag-info *aes-128-encrypt-spec-dag-bit-blasted*) shows that
;; almost all the functions are BITAND and BITNOT.  The exceptions are the
;; calls of CONS and BVCAT that assemble the final bits into a list of bytes.
