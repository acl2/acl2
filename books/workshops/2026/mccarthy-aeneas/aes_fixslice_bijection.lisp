;; Phase 2 of the fixslice-AES experiment: the representation bijection.
;;
;; Goal (plan Phase 2, the fail-fast step): the fixsliced state packing is a
;; bijection -- inv_bitslice . bitslice = identity -- so the bit-order model
;; used by the extracted code is self-consistent. Proved for ALL 2^256
;; (block0, block1) byte inputs by bit-blasting with centaur/gl. The engine
;; is GL's built-in BDD solver (no external SAT/SMT solver needed): the
;; obligation is a pure bit-permutation composed with byte pack/unpack, so
;; the BDDs stay linear and the proof closes in ~10s.
;;
;; These are the REAL extracted functions from aes_fixslice_encrypt.rs,
;; loaded directly from the generated book: the backend emits `result-fail`
;; (never a `fail` macro), so the extracted world coexists with centaur/gl
;; (whose books transitively define a FUNCTION named `fail`) with no
;; variant files needed.
;;
;; Non-vacuity was checked with a negative control: asserting the round-trip
;; returns the two blocks SWAPPED makes GL report and verify a concrete
;; counterexample (rather than certifying), confirming the proof has teeth.
(in-package "ACL2")
(include-book "aes_fixslice_encrypt")
(include-book "centaur/gl/gl" :dir :system)

;; Lemma: delta_swap_2 -- the bit-exchange primitive the packing is built
;; from -- is its own inverse for the AES masks (a 64-bit obligation).
(gl::def-gl-thm delta-swap-2-involutive
  :hyp (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
  :concl
  (b* ((p1 (result-ok->val (aes-fixslice-encrypt-delta-swap-2 a b 1 1431655765)))
       (p2 (result-ok->val (aes-fixslice-encrypt-delta-swap-2 (car p1) (cdr p1)
                                                              1 1431655765))))
    (and (equal (car p2) a) (equal (cdr p2) b)))
  :g-bindings (gl::auto-bindings (:nat a 32) (:nat b 32)))

;; Main theorem: unbitslicing a freshly bitsliced pair of 16-byte blocks
;; returns exactly those blocks -- the fixslice packing is a bijection.
(gl::def-gl-thm inv-bitslice-of-bitslice-is-identity
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7)
            (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15)
            (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7)
            (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
        (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (aes-fixslice-encrypt-inv-bitslice
             (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1)))
           (ok (list blk0 blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8)
                            (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)
                            (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8)
                            (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
