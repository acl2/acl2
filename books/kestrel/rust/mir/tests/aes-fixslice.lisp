; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

; Interpreter test on the extracted AES-128 crate: run the imported program's
; encrypt and decrypt on the MIR interpreter, checking the FIPS-197 known-answer
; vectors and differentially against the ACL2 AES-128 specification.
;
; The FIPS-197 AES-128 vectors are reused from the AES spec's own test book
; (@('kestrel/crypto/aes/aes-spec-tests')) rather than duplicated here: the two
; black-box AES-128 vectors are Appendix B and Appendix C.1.  The other FIPS-197
; tests there (key expansion, the round-by-round trace) exercise spec internals
; and do not apply to the whole-cipher interpreter, and the 192/256 vectors do
; not apply to this AES-128-only crate.
;
; The program is the committed fixture @('*aes-fixslice-program*') (see
; aes-fixslice-program.lisp), so this test needs neither the importer nor the
; serialized sample.  That the fixture is what the importer actually produces
; is checked separately by ../../import/aes-import-test.lisp.

(include-book "../interp")
(include-book "aes-fixslice-program")
(include-book "kestrel/crypto/aes/aes-spec-tests" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test-harness helpers (program mode: they are not reasoned about).

(acl2::program)

(defun u8-values (bytes)
  (if (endp bytes)
      nil
    (cons (value-uint (car bytes) (uint-type-u8))
          (u8-values (cdr bytes)))))

(defun u8-array-value (bytes)
  (value-array (u8-values bytes)))

(defun value-array-bytes-list (vs)
  (if (endp vs)
      nil
    (cons (value-uint->val (car vs))
          (value-array-bytes-list (cdr vs)))))

(defun value-array-bytes (v)
  (if (and (valuep v) (value-case v :array))
      (value-array-bytes-list (value-array->elems v))
    :not-an-array))

; Run a two-array-argument function of the fixture program and
; return the result as a byte list.  Argument order matches the crate's
; encrypt/decrypt: the key first, then the input block.
(defun run-aes-fn (name key block)
  (b* ((out (run-fn name
                    (list (u8-array-value key) (u8-array-value block))
                    *aes-fixslice-program*
                    10000000))
       ((unless (runout-case out :done)) (list :failed out)))
    (value-array-bytes (runout-done->value out))))

(acl2::logic)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A single leaf function: ror is u32::rotate_right.
(acl2::assert-event
 (equal (run-fn "ror"
                (list (value-uint #x12345678 (uint-type-u32))
                      (value-uint 8 (uint-type-u32)))
                *aes-fixslice-program*
                100000)
        (runout-done (value-uint #x78123456 (uint-type-u32)))))

; FIPS-197 Appendix C.1 (AES-128), vectors shared with aes-spec-tests.
(acl2::assert-equal
 (run-aes-fn "encrypt" aes::*aes-test-key-128* aes::*aes-test-plaintext*)
 aes::*aes-test-ciphertext-128*)

(acl2::assert-equal
 (run-aes-fn "decrypt" aes::*aes-test-key-128* aes::*aes-test-ciphertext-128*)
 aes::*aes-test-plaintext*)

; FIPS-197 Appendix B (AES-128), vectors shared with aes-spec-tests.
(acl2::assert-equal
 (run-aes-fn "encrypt" aes::*aes-128-example-key* aes::*aes-128-example-plaintext*)
 aes::*aes-128-example-ciphertext*)

(acl2::assert-equal
 (run-aes-fn "decrypt" aes::*aes-128-example-key* aes::*aes-128-example-ciphertext*)
 aes::*aes-128-example-plaintext*)

; Extra input coverage beyond the FIPS-197 vectors: differential against the
; ACL2 AES-128 spec (note the spec takes the plaintext first, then the key).
(acl2::assert-equal
 (run-aes-fn "encrypt" (acl2::repeat 16 0) (acl2::repeat 16 0))
 (aes::aes-128-encrypt (acl2::repeat 16 0) (acl2::repeat 16 0)))

(acl2::assert-equal
 (run-aes-fn "encrypt" (acl2::repeat 16 #xff) (acl2::repeat 16 #xff))
 (aes::aes-128-encrypt (acl2::repeat 16 #xff) (acl2::repeat 16 #xff)))
