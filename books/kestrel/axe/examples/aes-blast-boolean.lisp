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

(defund map-bool-to-bit (bools)
  (declare (xargs :guard (boolean-listp bools)))
  (if (endp bools)
      nil
    (cons (bool-to-bit (first bools))
          (map-bool-to-bit (rest bools)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-booleanp-assumptions (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (if (endp vars)
      nil
    (cons `(booleanp ,(first vars))
          (make-booleanp-assumptions (rest vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unroll the spec:
(unroll-spec-basic *aes-128-encrypt-spec-dag*
                   ;; The result here is a list of 128 booleans:
                   ;; Unlike in aes-blast.lisp, the variables here are booleans:
                   `(map-bit-to-bool (bytes-to-bits
                                       (aes::aes-128-encrypt (bits-to-bytes (map-bool-to-bit (list ,@(make-var-names 'in 128))))
                                                             (bits-to-bytes (map-bool-to-bit (list ,@(make-var-names 'key 128)))))))
                   :rules :auto
                   ;; :interpreted-function-alist (make-interpreted-function-alist '(getbit-list) (w state)) ; todo: build in ;; todo why did this take forever unless done separately?
                   :extra-rules (append (bit-blast-rules3)
                                        (introduce-bv-array-rules)) ; turns nth into bv-array-read
                   :remove-rules '(bit-to-bool bool-to-bit) ; todo, these rules interfer with pushing these functions to do conversions
                   )

(def-simplified-dag-basic *aes-128-encrypt-spec-dag-bit-blasted-as-boolean*
  *aes-128-encrypt-spec-dag*
;  :monitored-symbols '(ARRAY-REDUCTION-WHEN-ALL-SAME-IMPROVED2)
  :rules (append '(bv-array-read-blast-one-step-better
                   bif-rewrite ;bif
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
                   UNSIGNED-BYTE-P-1-OF-BOOL-TO-BIT
                   ;ARRAY-REDUCTION-1-0
                   integerp-of-bool-to-bit
                   natp-of-bool-to-bit
                   IFIX-WHEN-INTEGERP ; todo: avoid introducing ifix
                   BIT-TO-BOOL-OF-BOOL-TO-BIT
                   BOOL-TO-BIT-of-BIT-TO-BOOL
                   )
                 (array-reduction-rules)
                 (core-rules-bv)
                 (type-rules)
                 (list-rules))
;  :count-hits t
  :interpreted-function-alist (make-interpreted-function-alist '(getbit-list subrange) (w state))
  :assumptions (append (make-booleanp-assumptions (make-var-names 'in 128))
                       (make-booleanp-assumptions (make-var-names 'key 128))))

;; Now, doing (dag-info *AES-128-ENCRYPT-SPEC-DAG-BIT-BLASTED-AS-BOOLEAN*) shows that
;; almost all the functions are BOOLAND and NOT.  The exception is CONS, which is
;; used to assemble the final bits into a list of bytes.
