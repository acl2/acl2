; Phase 5 -- cipher side, part 5: the mask/frame algebra of the round ladder.
;
; The fixslice cipher tracks the spec through two byte-level distortions:
;   MASK : bare sub_bytes leaves every byte xor'd with 0x63 (the S-box affine
;          constant); the key-schedule fold bakes the SAME mask into every
;          round-key window, so the two cancel in add_round_key.  The one
;          nontrivial fact is that MixColumns FIXES the uniform mask
;          (2m ^ 3m ^ m ^ m = m in GF(2^8)) -- so the mask commutes out of
;          mix_columns too.  That single fact is the book's one GL bit-blast
;          (kmix-of-sbn); everything else about the mask is rewriting.
;   FRAME: mix_columns_c is MixColumns conjugated into the ShiftRows^c frame,
;          and the schedule windows carry invshiftrows^{r mod 4}; with the
;          state in frame r, mix_columns_{(r+1) mod 4} contributes exactly ONE
;          ShiftRows -- the telescoping change of variable.  The frame facts
;          are byte-position shuffles: both sides COMPUTE to the same nth
;          shuffle, so they are pure rewriting (no GL).
;
; Everything is stated over 16-byte blocks, matching the push-in rules
; (aes_fixslice_cipherops) on one side and the keymain window folds on the
; other.
(in-package "ACL2")
(include-book "aes_fixslice_cipherops")
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

;; single ShiftRows as a byte op (the spec-side round uses exactly one).
(defund sr1-bytes (b)
  (aes::copy-state-to-array (aes::shiftrows (aes::copyarraytostate b))))

;; inp preservation for the byte ops (explicit lists of u8 entries).
(defthm inp-of-copy-state-to-array
  (implies (aes::statep s) (aes::inp (aes::copy-state-to-array s)))
  :hints (("Goal"
           :use ((:instance expand-len-4 (x s))
                 (:instance expand-len-4 (x (nth 0 s))) (:instance expand-len-4 (x (nth 1 s)))
                 (:instance expand-len-4 (x (nth 2 s))) (:instance expand-len-4 (x (nth 3 s))))
           :in-theory (e/d (aes::copy-state-to-array aes::array-elem-2d
                            acl2::2d-bv-arrayp acl2::bv-arrayp acl2::bv-arrayp-list
                            acl2::all-unsigned-byte-p)
                           (nth)))))
(defthm inp-of-sr1-bytes
  (implies (aes::inp b) (aes::inp (sr1-bytes b)))
  :hints (("Goal" :in-theory (e/d (sr1-bytes) (aes::inp)))))
(defthm inp-of-kmix-bytes
  (implies (aes::inp b) (aes::inp (kmix-bytes b)))
  :hints (("Goal" :in-theory (e/d (kmix-bytes) (aes::inp)))))
(defthm inp-of-isr1-bytes
  (implies (aes::inp b) (aes::inp (inv-shift-rows-1-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes) (aes::inp)))))
(defthm inp-of-isr2-bytes
  (implies (aes::inp b) (aes::inp (inv-shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-2-bytes) (aes::inp)))))
(defthm inp-of-isr3-bytes
  (implies (aes::inp b) (aes::inp (inv-shift-rows-3-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-3-bytes) (aes::inp)))))
(defthm inp-of-sbn-bytes
  (implies (aes::inp b) (aes::inp (sub-bytes-nots-bytes b)))
  :hints (("Goal" :in-theory (e/d (sub-bytes-nots-bytes aes::inp acl2::bv-arrayp
                                   expand-len-16 unsigned-byte-p-of-logxor) (nth logxor)))))
(local (defthm usb8-of-nth-sbox
  (implies (unsigned-byte-p 8 i) (unsigned-byte-p 8 (nth i *sbox*)))
  :hints (("Goal" :use (sbox-const-correct
                        (:instance aes::unsigned-byte-p-of-nth-of-sbox-gen
                          (aes::n i) (aes::size 8)))
           :in-theory (e/d (unsigned-byte-p) (nth aes::sbox))))))
(defthm inp-of-map-sbox16
  (implies (aes::inp b) (aes::inp (map-sbox16 b)))
  :hints (("Goal" :in-theory (e/d (map-sbox16 aes::inp acl2::bv-arrayp expand-len-16) (nth usb8-of-nth-sbox))
           :use (
                 (:instance usb8-of-nth-sbox (i (nth 0 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0))
                 (:instance usb8-of-nth-sbox (i (nth 1 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1))
                 (:instance usb8-of-nth-sbox (i (nth 2 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2))
                 (:instance usb8-of-nth-sbox (i (nth 3 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3))
                 (:instance usb8-of-nth-sbox (i (nth 4 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4))
                 (:instance usb8-of-nth-sbox (i (nth 5 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5))
                 (:instance usb8-of-nth-sbox (i (nth 6 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6))
                 (:instance usb8-of-nth-sbox (i (nth 7 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7))
                 (:instance usb8-of-nth-sbox (i (nth 8 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8))
                 (:instance usb8-of-nth-sbox (i (nth 9 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9))
                 (:instance usb8-of-nth-sbox (i (nth 10 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10))
                 (:instance usb8-of-nth-sbox (i (nth 11 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11))
                 (:instance usb8-of-nth-sbox (i (nth 12 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12))
                 (:instance usb8-of-nth-sbox (i (nth 13 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13))
                 (:instance usb8-of-nth-sbox (i (nth 14 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14))
                 (:instance usb8-of-nth-sbox (i (nth 15 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15))))))
(defthm inp-of-xorbytes
  (implies (and (aes::inp x) (aes::inp y)) (aes::inp (xorbytes x y)))
  :hints (("Goal" :in-theory (e/d (xorbytes aes::inp acl2::bv-arrayp expand-len-16
                                   aes::binary-gf256add) (nth)))))
(defthm inp-of-mix-columns-1-bytes
  (implies (aes::inp b) (aes::inp (mix-columns-1-bytes b)))
  :hints (("Goal" :in-theory (e/d (mix-columns-1-bytes) (aes::inp)))))
(defthm inp-of-mix-columns-2-bytes
  (implies (aes::inp b) (aes::inp (mix-columns-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (mix-columns-2-bytes) (aes::inp)))))
(defthm inp-of-mix-columns-3-bytes
  (implies (aes::inp b) (aes::inp (mix-columns-3-bytes b)))
  :hints (("Goal" :in-theory (e/d (mix-columns-3-bytes) (aes::inp)))))
(defthm inp-of-shift-rows-2-bytes
  (implies (aes::inp b) (aes::inp (shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (shift-rows-2-bytes) (aes::inp)))))

;; ===========================================================================
;; FRAME facts: byte-position shuffles; both sides compute (no GL).
;; The composed byte ops need the copyarraytostate round-trip collapsed.
(local (in-theory (enable copyarraytostate-of-copy-state-to-array)))

(defthm frame-mc1
  (implies (aes::inp b)
           (equal (mix-columns-1-bytes b)
                  (inv-shift-rows-1-bytes (kmix-bytes (sr1-bytes b)))))
  :hints (("Goal" :in-theory (enable mix-columns-1-bytes inv-shift-rows-1-bytes
                                     kmix-bytes sr1-bytes))))
(defthm frame-mc2
  (implies (aes::inp b)
           (equal (mix-columns-2-bytes (inv-shift-rows-1-bytes b))
                  (inv-shift-rows-2-bytes (kmix-bytes (sr1-bytes b)))))
  :hints (("Goal" :in-theory (enable mix-columns-2-bytes inv-shift-rows-1-bytes
                                     inv-shift-rows-2-bytes kmix-bytes sr1-bytes))))
(defthm frame-mc3
  (implies (aes::inp b)
           (equal (mix-columns-3-bytes (inv-shift-rows-2-bytes b))
                  (inv-shift-rows-3-bytes (kmix-bytes (sr1-bytes b)))))
  :hints (("Goal" :in-theory (enable mix-columns-3-bytes inv-shift-rows-2-bytes
                                     inv-shift-rows-3-bytes kmix-bytes sr1-bytes))))
(defthm frame-mc0
  (implies (aes::inp b)
           (equal (kmix-bytes (inv-shift-rows-3-bytes b))
                  (kmix-bytes (sr1-bytes b))))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-3-bytes kmix-bytes sr1-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows aes::mixcolumns
                                   aes::array-elem-2d) (nth)))))
(defthm frame-sr2-isr1
  (implies (aes::inp b)
           (equal (shift-rows-2-bytes (inv-shift-rows-1-bytes b))
                  (sr1-bytes b)))
  :hints (("Goal" :in-theory (e/d (shift-rows-2-bytes inv-shift-rows-1-bytes sr1-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows
                                   aes::array-elem-2d) (nth)))))

;; sbox commutes with the byte permutations (position shuffle vs bytewise map).
;; Keep the table lookups opaque (a symbolic index would unroll the 256-entry
;; table): rewrite (nth i *sbox*) to a closed wrapper first.
(local (defund sbx (x) (nth x *sbox*)))
(local (defthm nth-sbox-is-sbx (equal (nth x *sbox*) (sbx x))
  :hints (("Goal" :in-theory (enable sbx)))))
(defthm sbox16-of-isr1
  (implies (aes::inp b)
           (equal (map-sbox16 (inv-shift-rows-1-bytes b))
                  (inv-shift-rows-1-bytes (map-sbox16 b))))
  :hints (("Goal" :in-theory (enable map-sbox16 inv-shift-rows-1-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm sbox16-of-isr2
  (implies (aes::inp b)
           (equal (map-sbox16 (inv-shift-rows-2-bytes b))
                  (inv-shift-rows-2-bytes (map-sbox16 b))))
  :hints (("Goal" :in-theory (enable map-sbox16 inv-shift-rows-2-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm sbox16-of-isr3
  (implies (aes::inp b)
           (equal (map-sbox16 (inv-shift-rows-3-bytes b))
                  (inv-shift-rows-3-bytes (map-sbox16 b))))
  :hints (("Goal" :in-theory (enable map-sbox16 inv-shift-rows-3-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm sbox16-of-sr1
  (implies (aes::inp b)
           (equal (map-sbox16 (sr1-bytes b))
                  (sr1-bytes (map-sbox16 b))))
  :hints (("Goal" :in-theory (enable map-sbox16 sr1-bytes
                                   aes::copyarraytostate aes::copy-state-to-array
                                   aes::invshiftrows aes::shiftrows aes::array-elem-2d))))

;; permutations distribute over the byte xor.
(defthm isr1-of-xorbytes
  (equal (inv-shift-rows-1-bytes (xorbytes x y))
         (xorbytes (inv-shift-rows-1-bytes x) (inv-shift-rows-1-bytes y)))
  :hints (("Goal" :in-theory (enable inv-shift-rows-1-bytes xorbytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm isr2-of-xorbytes
  (equal (inv-shift-rows-2-bytes (xorbytes x y))
         (xorbytes (inv-shift-rows-2-bytes x) (inv-shift-rows-2-bytes y)))
  :hints (("Goal" :in-theory (enable inv-shift-rows-2-bytes xorbytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm isr3-of-xorbytes
  (equal (inv-shift-rows-3-bytes (xorbytes x y))
         (xorbytes (inv-shift-rows-3-bytes x) (inv-shift-rows-3-bytes y)))
  :hints (("Goal" :in-theory (enable inv-shift-rows-3-bytes xorbytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))

;; the mask commutes with the byte permutations.
(defthm isr1-of-sbn
  (equal (inv-shift-rows-1-bytes (sub-bytes-nots-bytes b))
         (sub-bytes-nots-bytes (inv-shift-rows-1-bytes b)))
  :hints (("Goal" :in-theory (enable sub-bytes-nots-bytes inv-shift-rows-1-bytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm isr2-of-sbn
  (equal (inv-shift-rows-2-bytes (sub-bytes-nots-bytes b))
         (sub-bytes-nots-bytes (inv-shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (enable sub-bytes-nots-bytes inv-shift-rows-2-bytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm isr3-of-sbn
  (equal (inv-shift-rows-3-bytes (sub-bytes-nots-bytes b))
         (sub-bytes-nots-bytes (inv-shift-rows-3-bytes b)))
  :hints (("Goal" :in-theory (enable sub-bytes-nots-bytes inv-shift-rows-3-bytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm sr1-of-sbn
  (equal (sr1-bytes (sub-bytes-nots-bytes b))
         (sub-bytes-nots-bytes (sr1-bytes b)))
  :hints (("Goal" :in-theory (enable sub-bytes-nots-bytes sr1-bytes
                                     aes::copyarraytostate aes::copy-state-to-array
                                     aes::invshiftrows aes::shiftrows aes::array-elem-2d))))

;; ===========================================================================
;; MASK facts.  The one GL bit-blast: MixColumns fixes the uniform 0x63 mask
;; (per column: 2m ^ 3m ^ m ^ m = m).  Stated through kmix-bytes.
(gl::def-gl-thm kmix-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (kmix-bytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
                (sub-bytes-nots-bytes (kmix-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))
(defthm kmix-of-sbn
  (implies (aes::inp b)
           (equal (kmix-bytes (sub-bytes-nots-bytes b))
                  (sub-bytes-nots-bytes (kmix-bytes b))))
  :hints (("Goal" :in-theory (e/d (expand-len-16)
                                  (kmix-of-sbn-gl kmix-bytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance kmix-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))

;; masks cancel across the round-key xor: (x^63)+(y^63) = x+y bytewise.
(gl::def-gl-thm xorbytes-sbn-cancel-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl (equal (xorbytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (sub-bytes-nots-bytes (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
                (xorbytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm xorbytes-sbn-cancel
  (implies (and (aes::inp x) (aes::inp y))
           (equal (xorbytes (sub-bytes-nots-bytes x) (sub-bytes-nots-bytes y))
                  (xorbytes x y)))
  :hints (("Goal" :in-theory (e/d (expand-len-16)
                                  (xorbytes-sbn-cancel-gl xorbytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance xorbytes-sbn-cancel-gl (a0 (nth 0 x)) (a1 (nth 1 x)) (a2 (nth 2 x)) (a3 (nth 3 x)) (a4 (nth 4 x)) (a5 (nth 5 x)) (a6 (nth 6 x)) (a7 (nth 7 x)) (a8 (nth 8 x)) (a9 (nth 9 x)) (a10 (nth 10 x)) (a11 (nth 11 x)) (a12 (nth 12 x)) (a13 (nth 13 x)) (a14 (nth 14 x)) (a15 (nth 15 x)) (b0 (nth 0 y)) (b1 (nth 1 y)) (b2 (nth 2 y)) (b3 (nth 3 y)) (b4 (nth 4 y)) (b5 (nth 5 y)) (b6 (nth 6 y)) (b7 (nth 7 y)) (b8 (nth 8 y)) (b9 (nth 9 y)) (b10 (nth 10 y)) (b11 (nth 11 y)) (b12 (nth 12 y)) (b13 (nth 13 y)) (b14 (nth 14 y)) (b15 (nth 15 y))))))

;; the mask commutes out of the rotated mix_columns (rewriting from the
;; frame decomposition + kmix-of-sbn + the perm commutations).
(defthm inp-of-sbn-then  ;; helper: sbn preserves inp (restated for chaining)
  (implies (aes::inp b) (aes::inp (sub-bytes-nots-bytes b)))
  :rule-classes nil
  :hints (("Goal" :use inp-of-sbn-bytes)))
(defthm mc1-of-sbn
  (implies (aes::inp b)
           (equal (mix-columns-1-bytes (sub-bytes-nots-bytes b))
                  (sub-bytes-nots-bytes (mix-columns-1-bytes b))))
  :hints (("Goal" :in-theory (e/d (frame-mc1 sr1-of-sbn kmix-of-sbn isr1-of-sbn)
                                  (mix-columns-1-bytes inv-shift-rows-1-bytes
                                   kmix-bytes sr1-bytes sub-bytes-nots-bytes aes::inp)))))
(defthm mc2-of-sbn
  (implies (aes::inp b)
           (equal (mix-columns-2-bytes (sub-bytes-nots-bytes (inv-shift-rows-1-bytes b)))
                  (sub-bytes-nots-bytes (mix-columns-2-bytes (inv-shift-rows-1-bytes b)))))
  :hints (("Goal"
           :use ((:instance isr1-of-sbn)
                 (:instance frame-mc2 (b (sub-bytes-nots-bytes b))))
           :in-theory (e/d (frame-mc2 sr1-of-sbn kmix-of-sbn isr2-of-sbn)
                           (mix-columns-2-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes
                            kmix-bytes sr1-bytes sub-bytes-nots-bytes aes::inp isr1-of-sbn)))))
(defthm mc3-of-sbn
  (implies (aes::inp b)
           (equal (mix-columns-3-bytes (sub-bytes-nots-bytes (inv-shift-rows-2-bytes b)))
                  (sub-bytes-nots-bytes (mix-columns-3-bytes (inv-shift-rows-2-bytes b)))))
  :hints (("Goal"
           :use ((:instance isr2-of-sbn)
                 (:instance frame-mc3 (b (sub-bytes-nots-bytes b))))
           :in-theory (e/d (frame-mc3 sr1-of-sbn kmix-of-sbn isr3-of-sbn)
                           (mix-columns-3-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes
                            kmix-bytes sr1-bytes sub-bytes-nots-bytes aes::inp isr2-of-sbn)))))
(defthm mc0-of-sbn
  (implies (aes::inp b)
           (equal (kmix-bytes (sub-bytes-nots-bytes (inv-shift-rows-3-bytes b)))
                  (sub-bytes-nots-bytes (kmix-bytes (inv-shift-rows-3-bytes b)))))
  :hints (("Goal"
           :use ((:instance isr3-of-sbn)
                 (:instance frame-mc0 (b (sub-bytes-nots-bytes b))))
           :in-theory (e/d (frame-mc0 sr1-of-sbn kmix-of-sbn)
                           (kmix-bytes inv-shift-rows-3-bytes sr1-bytes
                            sub-bytes-nots-bytes aes::inp isr3-of-sbn)))))
