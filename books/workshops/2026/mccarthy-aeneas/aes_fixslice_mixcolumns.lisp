; Phase 3 (per-op equivalence) -- MixColumns.
;
; Fixslice ships four MixColumns variants (mix_columns_0..3): the state
; representation rotates each round to fold ShiftRows in for free, and each
; variant is MixColumns in one rotation phase. mix_columns_0 is the phase-0
; (un-rotated) one, which is exactly the standard AES MixColumns; the 1/2/3
; variants and the last-round shift_rows_2 are the rotated frame-variants,
; meaningful only in the round pipeline (a Phase-4 composition matter -- the
; whole-cipher FIPS KAT already validates that composition end to end).
;
; Here we prove the clean per-op fact for the phase-0 variant, for ALL 2^256
; two-block inputs, by bit-blasting the REAL extracted circuit (GF(2^8) mults
; and all) against Kestrel's table/field spec:
;
;   inv_bitslice(mix_columns_0(bitslice(b0,b1))) = (mixcolumns b0, mixcolumns b1)
(in-package "ACL2")
(include-book "aes_fixslice_correspondence")

;; Kestrel MixColumns as a byte-list -> byte-list op (load, mix, store).
(defund kmix-bytes (b)
  (aes::copy-state-to-array (aes::mixcolumns (aes::copyarraytostate b))))

(gl::def-gl-thm mix-columns-0-is-mixcolumns-through-packing
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val
                 (aes-fixslice-encrypt-mix-columns-0
                   (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (kmix-bytes blk0) (kmix-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

;; ---------------------------------------------------------------------------
;; Length-4 list decomposition (the statep 4x4, like expand-len-16 for blocks).
(defthmd expand-len-4
  (implies (and (true-listp x) (equal (len x) 4))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)) x))
  :hints (("Goal" :in-theory (enable nth)
           :expand ((len x) (len (cdr x)) (len (cdr (cdr x)))
                    (len (cdr (cdr (cdr x))))))))

;; Kestrel's two state<->bytes conversions are mutually inverse on a statep.
(defthm copyarraytostate-of-copy-state-to-array
  (implies (aes::statep s)
           (equal (aes::copyarraytostate (aes::copy-state-to-array s)) s))
  :hints (("Goal" :in-theory (e/d (aes::copyarraytostate aes::copy-state-to-array
                                   aes::array-elem-2d expand-len-4
                                   acl2::2d-bv-arrayp acl2::bv-arrayp)
                                  (nth)))))

;; ---------------------------------------------------------------------------
;; Lift the GL crux to general 16-byte-LIST form (expand-len-16 bridge).
(defthm mix-columns-0-through-packing-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val
                        (aes-fixslice-encrypt-mix-columns-0
                          (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (kmix-bytes b0) (kmix-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (mix-columns-0-is-mixcolumns-through-packing
                            aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-0
                            aes-fixslice-encrypt-inv-bitslice
                            aes::inp kmix-bytes nth))
           :use (:instance mix-columns-0-is-mixcolumns-through-packing
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

;; ---------------------------------------------------------------------------
;; Phase-3 result: the fixslice phase-0 MixColumns, through the map phi,
;; computes Kestrel's mixcolumns on the AES state.
(defthm mixcolumns-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val
                      (aes-fixslice-encrypt-mix-columns-0
                        (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
                    0)
                  (aes::mixcolumns (aes::copyarraytostate b0))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block kmix-bytes)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-0
                            aes-fixslice-encrypt-inv-bitslice aes::copy-state-to-array
                            aes::mixcolumns aes::copyarraytostate))
           :use ((:instance copyarraytostate-of-copy-state-to-array
                  (s (aes::mixcolumns (aes::copyarraytostate b0))))))))
