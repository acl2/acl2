; Phase 4 -- the ShiftRows-fold rotation, characterised against the spec.
;
; Fixslice folds ShiftRows into the round by rotating the state representation:
; mix_columns_i, through the packing, is MixColumns CONJUGATED into the
; ShiftRows^i frame -- invshiftrows^i . mixcolumns . shiftrows^i -- all Kestrel
; spec ops. The last round's shift_rows_2 is shiftrows^2. These are exactly the
; pieces that telescope: with y_r = shiftrows^r(phi(state_r)), the sr^r change of
; variable cancels each conjugation (SubBytes commutes with ShiftRows), so the
; fixslice recurrence collapses onto the spec's mc.sr.SB recurrence.
;
; Each op is bit-blasted through the packing (the irreducible per-op fact) then
; lifted through phi to the spec ops; the round composition on top is rewriting.
(in-package "ACL2")
(include-book "aes_fixslice_mixcolumns")

;; ---- mix-columns-1 ----
(defund mix-columns-1-bytes (b) (aes::copy-state-to-array (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::copyarraytostate b))))))
(gl::def-gl-thm mix-columns-1-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (mix-columns-1-bytes blk0) (mix-columns-1-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm mix-columns-1-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (mix-columns-1-bytes b0) (mix-columns-1-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (mix-columns-1-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-1
                            aes-fixslice-encrypt-inv-bitslice aes::inp mix-columns-1-bytes nth))
           :use (:instance mix-columns-1-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
(defthm mix-columns-1-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)
                  (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::copyarraytostate b0))))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block mix-columns-1-bytes)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-1
                            aes-fixslice-encrypt-inv-bitslice aes::copy-state-to-array
                            aes::copyarraytostate aes::shiftrows aes::invshiftrows aes::mixcolumns))
           :use ((:instance copyarraytostate-of-copy-state-to-array (s (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::copyarraytostate b0))))))))))

;; ---- mix-columns-2 ----
(defund mix-columns-2-bytes (b) (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b))))))))
(gl::def-gl-thm mix-columns-2-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (mix-columns-2-bytes blk0) (mix-columns-2-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm mix-columns-2-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (mix-columns-2-bytes b0) (mix-columns-2-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (mix-columns-2-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-2
                            aes-fixslice-encrypt-inv-bitslice aes::inp mix-columns-2-bytes nth))
           :use (:instance mix-columns-2-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
(defthm mix-columns-2-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)
                  (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0))))))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block mix-columns-2-bytes)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-2
                            aes-fixslice-encrypt-inv-bitslice aes::copy-state-to-array
                            aes::copyarraytostate aes::shiftrows aes::invshiftrows aes::mixcolumns))
           :use ((:instance copyarraytostate-of-copy-state-to-array (s (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0))))))))))))

;; ---- mix-columns-3 ----
(defund mix-columns-3-bytes (b) (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b))))))))))
(gl::def-gl-thm mix-columns-3-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (mix-columns-3-bytes blk0) (mix-columns-3-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm mix-columns-3-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (mix-columns-3-bytes b0) (mix-columns-3-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (mix-columns-3-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-3
                            aes-fixslice-encrypt-inv-bitslice aes::inp mix-columns-3-bytes nth))
           :use (:instance mix-columns-3-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
(defthm mix-columns-3-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)
                  (aes::invshiftrows (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0))))))))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block mix-columns-3-bytes)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-mix-columns-3
                            aes-fixslice-encrypt-inv-bitslice aes::copy-state-to-array
                            aes::copyarraytostate aes::shiftrows aes::invshiftrows aes::mixcolumns))
           :use ((:instance copyarraytostate-of-copy-state-to-array (s (aes::invshiftrows (aes::invshiftrows (aes::invshiftrows (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0))))))))))))))

;; ---- shift-rows-2 ----
(defund shift-rows-2-bytes (b) (aes::copy-state-to-array (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b)))))
(gl::def-gl-thm shift-rows-2-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (shift-rows-2-bytes blk0) (shift-rows-2-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm shift-rows-2-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (shift-rows-2-bytes b0) (shift-rows-2-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (shift-rows-2-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-shift-rows-2
                            aes-fixslice-encrypt-inv-bitslice aes::inp shift-rows-2-bytes nth))
           :use (:instance shift-rows-2-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
(defthm shift-rows-2-correspondence
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (fixslice->statep
                    (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)
                  (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0)))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block shift-rows-2-bytes)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-shift-rows-2
                            aes-fixslice-encrypt-inv-bitslice aes::copy-state-to-array
                            aes::copyarraytostate aes::shiftrows aes::invshiftrows aes::mixcolumns))
           :use ((:instance copyarraytostate-of-copy-state-to-array (s (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0)))))))))

