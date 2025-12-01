; Bit-blasting the spec for AES-128
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod, due to regression failure 9/4/2025 using Allegro CL 10.1:
; cert_param: (non-allegro)

(in-package "ACL2")

;; A variant of aes-blast,lisp that uses boolean operations for NOT and AND.

(include-book "kestrel/axe/unroll-spec-basic" :dir :system)
(include-book "kestrel/axe/rewriter-basic" :dir :system)
(include-book "kestrel/axe/merge-term-into-dag-array-simple" :dir :system) ; for wrap-term-around-dag
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)
(include-book "kestrel/bv-lists/bit-listp" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes" :dir :system)
(local (include-book "kestrel/bv/bit-to-bool" :dir :system))

(defconst *key-byte-count* 16) ; AES-128 has 128 key bits (= 16 bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library material (TODO: Move to libraries!):

(defopeners bytes-to-bits)

;; Converts each of the BITS to a boolean, returning a list of booleans.
(defund map-bit-to-bool (bits)
  (declare (xargs :guard (bit-listp bits)))
  (if (endp bits)
      nil
    (cons (bit-to-bool (first bits))
          (map-bit-to-bool (rest bits)))))

(defopeners map-bit-to-bool)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts each of the BOOLS to a bit, returning a list of bits.
(defund map-bool-to-bit (bools)
  (declare (xargs :guard (boolean-listp bools)))
  (if (endp bools)
      nil
    (cons (bool-to-bit (first bools))
          (map-bool-to-bit (rest bools)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unroll the spec:
(unroll-spec-basic *aes-128-encrypt-spec-dag*
                   ;; The result here is a list of 128 booleans:
                   ;; Unlike in aes-blast.lisp, the variables here are booleans:
                   `(map-bit-to-bool (bytes-to-bits
                                       (aes::aes-128-encrypt (bits-to-bytes (map-bool-to-bit (list ,@(make-var-names 'in 128))))
                                                             (bits-to-bytes (map-bool-to-bit (list ,@(make-var-names 'key 128)))))))
                   :rules :auto
                   :extra-rules (append (bit-blast-rules)
                                        (introduce-bv-array-rules)) ; turns nth into bv-array-read
                   :remove-rules '(bit-to-bool bool-to-bit) ; todo, these rules interfer with pushing these functions to do conversions
                   )

(def-simplified-basic *aes-128-encrypt-spec-dag-bit-blasted-as-boolean*
  *aes-128-encrypt-spec-dag*
  :rules (append '(bv-array-read-blast-one-step
                   bitor-becomes-bitnot-of-bitand-of-bitnot-and-bitnot
                   bitxor-becomes-bitor-of-bitand-of-bitnot-and-bitand-of-bitnot
                   bytes-to-bits-base
                   bytes-to-bits-unroll
                   binary-append-opener
                   byte-to-bits
                   map-bit-to-bool-base
                   map-bit-to-bool-unroll
                   bit-to-bool-of-bitnot
                   bit-to-bool-of-bitand
                   ;; equal-of-0-and-bitxor-alt
                   ;; equal-of-0-and-bitnot
                   ;; equal-of-1-and-bitnot
                   ;; equal-of-bitnot-and-0
                   ;; equal-of-bitnot-and-1
                   ;; equal-of-1-and-bitand
                   ;; equal-of-0-and-bitand-new
                   ;bvif-becomes-bif
                   unsigned-byte-p-1-of-bool-to-bit
                   ;array-reduction-1-0
                   integerp-of-bool-to-bit
                   natp-of-bool-to-bit
                   ifix-when-integerp ; todo: avoid introducing ifix
                   bit-to-bool-of-bool-to-bit
                   bool-to-bit-of-bit-to-bool)
                 (array-reduction-rules)
                 (core-rules-bv)
                 (type-rules)
                 (list-rules))
  :assumptions (append (boolean-hyps (make-var-names 'in 128))
                       (boolean-hyps (make-var-names 'key 128))))

;; Now, doing (dag-info *AES-128-ENCRYPT-SPEC-DAG-BIT-BLASTED-AS-BOOLEAN*) shows that
;; almost all the functions are BOOLAND and NOT.  The exception is CONS, which is
;; used to assemble the final bits into a list of bytes.
