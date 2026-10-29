; FIPS-197 Appendix C.1 known-answer test for the extracted fixsliced AES-128
; (aes_fixslice_encrypt.lisp, vendored from the SHIPPED RustCrypto crate). The
; WHOLE cipher -- key schedule AND encrypt -- runs in the prover and reproduces
; the standard's ciphertext bit-for-bit, straight from the raw 16-byte key.
(in-package "ACL2")
(include-book "aes_fixslice_encrypt")

(defconst *fips-key*
  (list #x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f))
(defconst *fips-pt*
  (list #x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff))
(defconst *fips-ct*
  (list #x69 #xc4 #xe0 #xd8 #x6a #x7b #x04 #x30 #xd8 #xcd #xb7 #x80 #x70 #xb4 #xc5 #x5a))

;; Whole cipher (key schedule + encrypt) reproduces the FIPS-197 C.1 vector.
;; (fuel 100 covers every add_round_key / write8 / memshift / xor_columns loop.)
(assert-event
 (equal (aes-fixslice-encrypt-encrypt 100 *fips-key* *fips-pt*)
        (ok *fips-ct*)))

;; ------------------------------------------------------------------------
;; Decryption: FIPS-197 C.1 known-answer test and the round-trip identity,
;; both executed in the prover on the WHOLE cipher (key schedule + decrypt).
(assert-event
 (equal (aes-fixslice-encrypt-decrypt 100 *fips-key* *fips-ct*)
        (ok *fips-pt*)))

;; decrypt . encrypt = id (and encrypt . decrypt = id), for the FIPS vector.
(assert-event
 (equal (aes-fixslice-encrypt-decrypt 100 *fips-key*
          (result-ok->val (aes-fixslice-encrypt-encrypt 100 *fips-key* *fips-pt*)))
        (ok *fips-pt*)))
(assert-event
 (equal (aes-fixslice-encrypt-encrypt 100 *fips-key*
          (result-ok->val (aes-fixslice-encrypt-decrypt 100 *fips-key* *fips-ct*)))
        (ok *fips-ct*)))
