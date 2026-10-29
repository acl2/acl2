; Phase 3 (per-op equivalence) -- SubBytes.
;
; Fixslice splits the AES S-box: `sub_bytes` is the 113-gate Boyar-Peralta
; circuit WITHOUT the affine NOTs, which the crate removes and folds into the
; round keys (aes_fixslice_encrypt.rs: "Account for NOTs removed from
; sub_bytes"). So the full byte-wise S-box on the state is
; `sub_bytes_nots . sub_bytes`. Proved for ALL 2^256 two-block inputs by
; bit-blasting the REAL extracted 113-gate circuit with centaur/gl: composed
; with the packing it is exactly the FIPS-197 table S-box on each byte --
; validating the shipped bitsliced S-box against the standard table.
(in-package "ACL2")
(include-book "aes_fixslice_correspondence")

(defconst *sbox*
  (list
        #x63 #x7c #x77 #x7b #xf2 #x6b #x6f #xc5 #x30 #x01 #x67 #x2b #xfe #xd7 #xab #x76
        #xca #x82 #xc9 #x7d #xfa #x59 #x47 #xf0 #xad #xd4 #xa2 #xaf #x9c #xa4 #x72 #xc0
        #xb7 #xfd #x93 #x26 #x36 #x3f #xf7 #xcc #x34 #xa5 #xe5 #xf1 #x71 #xd8 #x31 #x15
        #x04 #xc7 #x23 #xc3 #x18 #x96 #x05 #x9a #x07 #x12 #x80 #xe2 #xeb #x27 #xb2 #x75
        #x09 #x83 #x2c #x1a #x1b #x6e #x5a #xa0 #x52 #x3b #xd6 #xb3 #x29 #xe3 #x2f #x84
        #x53 #xd1 #x00 #xed #x20 #xfc #xb1 #x5b #x6a #xcb #xbe #x39 #x4a #x4c #x58 #xcf
        #xd0 #xef #xaa #xfb #x43 #x4d #x33 #x85 #x45 #xf9 #x02 #x7f #x50 #x3c #x9f #xa8
        #x51 #xa3 #x40 #x8f #x92 #x9d #x38 #xf5 #xbc #xb6 #xda #x21 #x10 #xff #xf3 #xd2
        #xcd #x0c #x13 #xec #x5f #x97 #x44 #x17 #xc4 #xa7 #x7e #x3d #x64 #x5d #x19 #x73
        #x60 #x81 #x4f #xdc #x22 #x2a #x90 #x88 #x46 #xee #xb8 #x14 #xde #x5e #x0b #xdb
        #xe0 #x32 #x3a #x0a #x49 #x06 #x24 #x5c #xc2 #xd3 #xac #x62 #x91 #x95 #xe4 #x79
        #xe7 #xc8 #x37 #x6d #x8d #xd5 #x4e #xa9 #x6c #x56 #xf4 #xea #x65 #x7a #xae #x08
        #xba #x78 #x25 #x2e #x1c #xa6 #xb4 #xc6 #xe8 #xdd #x74 #x1f #x4b #xbd #x8b #x8a
        #x70 #x3e #xb5 #x66 #x48 #x03 #xf6 #x0e #x61 #x35 #x57 #xb9 #x86 #xc1 #x1d #x9e
        #xe1 #xf8 #x98 #x11 #x69 #xd9 #x8e #x94 #x9b #x1e #x87 #xe9 #xce #x55 #x28 #xdf
        #x8c #xa1 #x89 #x0d #xbf #xe6 #x42 #x68 #x41 #x99 #x2d #x0f #xb0 #x54 #xbb #x16))

(defthm sbox-const-correct
  (equal (aes::sbox) *sbox*)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable (:e aes::sbox)))))

;; Byte-wise AES S-box over a 16-byte block (table lookup per byte).
(defund map-sbox16 (b)
  (list (nth (nth 0 b) *sbox*)  (nth (nth 1 b) *sbox*)
        (nth (nth 2 b) *sbox*)  (nth (nth 3 b) *sbox*)
        (nth (nth 4 b) *sbox*)  (nth (nth 5 b) *sbox*)
        (nth (nth 6 b) *sbox*)  (nth (nth 7 b) *sbox*)
        (nth (nth 8 b) *sbox*)  (nth (nth 9 b) *sbox*)
        (nth (nth 10 b) *sbox*) (nth (nth 11 b) *sbox*)
        (nth (nth 12 b) *sbox*) (nth (nth 13 b) *sbox*)
        (nth (nth 14 b) *sbox*) (nth (nth 15 b) *sbox*)))

(gl::def-gl-thm subbytes-is-aes-sbox-through-packing
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val
                 (aes-fixslice-encrypt-sub-bytes-nots
                   (result-ok->val
                     (aes-fixslice-encrypt-sub-bytes
                       (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))))
           (list (map-sbox16 blk0) (map-sbox16 blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

;; ---------------------------------------------------------------------------
;; Lift the GL crux to a general 16-byte-LIST form (same expand-len-16 bridge
;; as the Phase-2 bijection), keeping every heavy function closed.
(defthm subbytes-through-packing-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val
                        (aes-fixslice-encrypt-sub-bytes-nots
                          (result-ok->val
                            (aes-fixslice-encrypt-sub-bytes
                              (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))))
                  (list (map-sbox16 b0) (map-sbox16 b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (subbytes-is-aes-sbox-through-packing
                            aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-sub-bytes
                            aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-inv-bitslice
                            aes::inp map-sbox16 nth))
           :use (:instance subbytes-is-aes-sbox-through-packing
                  (a0 (nth 0 b0))
                  (a1 (nth 1 b0))
                  (a2 (nth 2 b0))
                  (a3 (nth 3 b0))
                  (a4 (nth 4 b0))
                  (a5 (nth 5 b0))
                  (a6 (nth 6 b0))
                  (a7 (nth 7 b0))
                  (a8 (nth 8 b0))
                  (a9 (nth 9 b0))
                  (a10 (nth 10 b0))
                  (a11 (nth 11 b0))
                  (a12 (nth 12 b0))
                  (a13 (nth 13 b0))
                  (a14 (nth 14 b0))
                  (a15 (nth 15 b0))
                  (b0 (nth 0 b1))
                  (b1 (nth 1 b1))
                  (b2 (nth 2 b1))
                  (b3 (nth 3 b1))
                  (b4 (nth 4 b1))
                  (b5 (nth 5 b1))
                  (b6 (nth 6 b1))
                  (b7 (nth 7 b1))
                  (b8 (nth 8 b1))
                  (b9 (nth 9 b1))
                  (b10 (nth 10 b1))
                  (b11 (nth 11 b1))
                  (b12 (nth 12 b1))
                  (b13 (nth 13 b1))
                  (b14 (nth 14 b1))
                  (b15 (nth 15 b1))))))

;; Kestrel-side commute: the table S-box commutes with the column-major load,
;; so subbytes . copyarraytostate = copyarraytostate . (byte-wise sbox).
(defthm subbytes-copyarraytostate-commute
  (implies (aes::inp b)
           (equal (aes::subbytes (aes::copyarraytostate b))
                  (aes::copyarraytostate (map-sbox16 b))))
  :hints (("Goal" :in-theory (enable aes::subbytes aes::copyarraytostate
                                     aes::array-elem-2d map-sbox16)
           :use sbox-const-correct)))

;; ---------------------------------------------------------------------------
;; Phase-3 result: the fixslice full SubBytes (sub_bytes then sub_bytes_nots),
;; viewed through the Phase-2 map phi, computes Kestrel's subbytes on the AES
;; state. (Stated on freshly-bitsliced input; phi(bitslice b)=copyarraytostate
;; b from Phase 2, and bitslice is onto, so this covers every state.)
(defthm subbytes-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val
                      (aes-fixslice-encrypt-sub-bytes-nots
                        (result-ok->val
                          (aes-fixslice-encrypt-sub-bytes
                            (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                    0)
                  (aes::subbytes (aes::copyarraytostate b0))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-sub-bytes
                            aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-inv-bitslice map-sbox16 aes::copyarraytostate))
           :use ((:instance subbytes-copyarraytostate-commute (b b0))))))
