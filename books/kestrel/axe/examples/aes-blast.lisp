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

(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/rewriter-basic" :dir :system)
(include-book "kestrel/axe/merge-term-into-dag-array-simple" :dir :system) ; for wrap-term-around-dag
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)

(defconst *key-byte-count* 16) ; AES-128 has 128 key bits (= 16 bytes)

;; Unroll the spec:
(unroll-spec-basic *aes-128-encrypt-spec-dag*
                   ;; The result here is a list of 16 bytes:
                   `(aes::aes-128-encrypt ,(bit-blasted-symbolic-byte-list 'in 16)
                                          ,(bit-blasted-symbolic-byte-list 'key *key-byte-count*))
                   :rules :auto
                   :count-hits t
                   ;; :interpreted-function-alist (make-interpreted-function-alist '(getbit-list) (w state)) ; todo: build in ;; todo why did this take forever unless done separately?
                   :extra-rules (append (bit-blast-rules3)
                                        (introduce-bv-array-rules)) ; turns nth into bv-array-read
                   )

;todo: move to library
(defthm bitor-becomes-bitnot-of-bitand-of-bitnot-and-bitnot
  (equal (bitor x y)
         (bitnot (bitand (bitnot x) (bitnot y))))
  :hints (("Goal" :in-theory (enable bitor bvor BITAND BITAND bitnot))))

;todo: move to library
(defthm bitxor-becomes-bitor-of-bitand-of-bitnot-and-bitand-of-bitnot
  (equal (bitxor x y)
         (bitor (bitand x (bitnot y))
                (bitand (bitnot x) y)))
  :hints (("Goal" :in-theory (enable bitor bvor bitand bitand bitnot))))

;; todo: convert the bit operations to boolean operations?
(def-simplified-dag-basic *aes-128-encrypt-spec-dag-bit-blasted*
  *aes-128-encrypt-spec-dag*
  :rules (append '(bv-array-read-blast-one-step-better
                   bif-rewrite ;bif
                   bitor-becomes-bitnot-of-bitand-of-bitnot-and-bitnot
                   bitxor-becomes-bitor-of-bitand-of-bitnot-and-bitand-of-bitnot
                   )
                 (core-rules-bv) (type-rules))
  :interpreted-function-alist (make-interpreted-function-alist '(getbit-list subrange) (w state)))

;; Now, doing (dag-info *aes-128-encrypt-spec-dag-bit-blasted*) shows that
;; almost all the functions are BITAND and BITNOT.  The exception is the
;; functions uses to assemble the final bits into a list of bytes.

