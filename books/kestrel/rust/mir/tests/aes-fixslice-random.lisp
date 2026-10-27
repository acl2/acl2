; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

; Randomized differential test on the extracted AES-128 crate: run the
; imported program's encrypt on the MIR interpreter against the ACL2 AES-128
; specification on pseudorandom key/block pairs, and check that the imported
; decrypt inverts each resulting ciphertext.
;
; The pairs are deterministic: a fixed-seed splitmix64 generator expands
; *seed* into *pair-count* key/block pairs, so the test is reproducible
; everywhere and needs no I/O or random state.  One interpreted run is
; 83,602 machine steps (about a quarter second), so the default 64 pairs
; (128 interpreted runs: encrypt and decrypt per pair) add roughly a minute
; on top of this book's includes.  *pair-count* scales that linearly.
;
; To certify, in this directory:  cert.pl aes-fixslice-random.lisp
;
; The fixture and the harness conventions follow aes-fixslice.lisp; the
; harness helpers are duplicated verbatim so this book certifies
; independently of that one.

(include-book "../interp")
(include-book "aes-fixslice-program")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test-harness helpers (program mode: they are not reasoned about).
; Duplicated from aes-fixslice.lisp.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; splitmix64 (Steele, Lea & Flood; the Java SplittableRandom mixer):
; a tiny deterministic pseudorandom generator over 64-bit state.

(defconst *sm64-modulus* (expt 2 64))

(defun sm64-mix (z)
  (b* ((z (mod (* (logxor z (ash z -30)) #xBF58476D1CE4E5B9) *sm64-modulus*))
       (z (mod (* (logxor z (ash z -27)) #x94D049BB133111EB) *sm64-modulus*)))
    (logxor z (ash z -31))))

(defun sm64-next (s)
  ;; Returns (mv out new-state).
  (b* ((s (mod (+ s #x9E3779B97F4A7C15) *sm64-modulus*)))
    (mv (sm64-mix s) s)))

(defun u64-le-bytes (x)
  (list (logand x #xff)
        (logand (ash x -8) #xff)
        (logand (ash x -16) #xff)
        (logand (ash x -24) #xff)
        (logand (ash x -32) #xff)
        (logand (ash x -40) #xff)
        (logand (ash x -48) #xff)
        (logand (ash x -56) #xff)))

(defun sm64-16-bytes (s)
  ;; Returns (mv bytes new-state): 16 pseudorandom bytes.
  (b* (((mv a s) (sm64-next s))
       ((mv b s) (sm64-next s)))
    (mv (append (u64-le-bytes a) (u64-le-bytes b)) s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun differential-pair-ok (key block)
  ;; The interpreted encrypt agrees with the specification (whose argument
  ;; order is block, then key), and the interpreted decrypt inverts the
  ;; ciphertext.
  (b* ((ct (run-aes-fn "encrypt" key block)))
    (and (equal ct (aes::aes-128-encrypt block key))
         (equal (run-aes-fn "decrypt" key ct) block))))

(defun differential-pairs-ok (n s)
  ;; T, or a diagnostic for the first failing pair.
  (if (zp n)
      t
    (b* (((mv key s) (sm64-16-bytes s))
         ((mv block s) (sm64-16-bytes s)))
      (if (differential-pair-ok key block)
          (differential-pairs-ok (1- n) s)
        (list :counterexample
              :key key
              :block block
              :interpreter (run-aes-fn "encrypt" key block)
              :spec (aes::aes-128-encrypt block key))))))

(acl2::logic)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *seed* 0)
(defconst *pair-count* 64)

; 64 pairs, 128 interpreted runs.  On failure the assert prints the
; diagnostic with the offending pair.
(acl2::assert-event
 (equal (differential-pairs-ok *pair-count* *seed*) t))
