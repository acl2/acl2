; Phase 6 -- DECRYPT SIDE, part 4: the mask/frame algebra of the decrypt
; ladder (mirror of aes_fixslice_maskalg).
;
; The decrypt chain tracks the spec through the SAME two distortions as
; encrypt, but consumed the other way around:
;   MASK : the schedule windows 1..10 carry the uniform 0x63 mask
;          (sub-bytes-nots-bytes); on the decrypt side the state does NOT
;          carry it -- each round's add_round_key deposits the mask and the
;          following inv_sub_bytes consumes it, because the extracted
;          inv_sub_bytes computes invsbox[x ^ 0x63] (the affine constant
;          sits on the INPUT of the inverse circuit).  So instead of the
;          encrypt side's xorbytes-sbn-cancel we ASSOCIATE the mask outward
;          across the xor (xorbytes-sbn-assoc), commute it through the
;          conjugated inverse MixColumns (imcN-of-sbn -- the same
;          "MixColumns fixes the uniform mask" fact: the inverse
;          coefficients also sum to 1), and cancel it at the S-box
;          (misb-of-sbn: map-invsbox16 o sbn = invsbox16, the TRUE map).
;   FRAME: inv_mix_columns_c is InvMixColumns conjugated into the
;          ShiftRows^c frame; with the state in frame isr^{c+1} the round's
;          window (frame isr^c) regroups and inv_mix_columns_c acts as
;          plain InvMixColumns INSIDE the frame, telescoping one
;          InvShiftRows per round (frame-imcN-dec).  The frame facts are
;          byte-position shuffles -- both sides compute -- plus the isr
;          power table for regrouping.
;
; Discovered empirically (probe: FIPS-197 vectors through both chains,
; matching each extracted state against framed/masked spec stages), then
; certified: shuffle facts by rewriting, xor/mask/table facts by GL.
(in-package "ACL2")
(include-book "aes_fixslice_maskalg")
(include-book "aes_fixslice_invops_defs")
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))
(local (in-theory (enable copyarraytostate-of-copy-state-to-array)))

;; the TRUE bytewise inverse S-box map (no mask): the decrypt chain state
(defund invsbox16 (b)
  (list (nth (nth 0 b) (aes::invsbox))
        (nth (nth 1 b) (aes::invsbox))
        (nth (nth 2 b) (aes::invsbox))
        (nth (nth 3 b) (aes::invsbox))
        (nth (nth 4 b) (aes::invsbox))
        (nth (nth 5 b) (aes::invsbox))
        (nth (nth 6 b) (aes::invsbox))
        (nth (nth 7 b) (aes::invsbox))
        (nth (nth 8 b) (aes::invsbox))
        (nth (nth 9 b) (aes::invsbox))
        (nth (nth 10 b) (aes::invsbox))
        (nth (nth 11 b) (aes::invsbox))
        (nth (nth 12 b) (aes::invsbox))
        (nth (nth 13 b) (aes::invsbox))
        (nth (nth 14 b) (aes::invsbox))
        (nth (nth 15 b) (aes::invsbox))))

(local (defthm usb8-of-nth-invsbox
  (implies (unsigned-byte-p 8 i) (unsigned-byte-p 8 (nth i (aes::invsbox))))
  :hints (("Goal" :use ((:instance aes::unsigned-byte-p-of-nth-of-invsbox-gen (aes::n i) (aes::size 8)))
           :in-theory (e/d (unsigned-byte-p) (nth))))))

(defthm inp-of-invsbox16
  (implies (aes::inp b) (aes::inp (invsbox16 b)))
  :hints (("Goal" :in-theory (e/d (invsbox16 aes::inp acl2::bv-arrayp expand-len-16) (nth usb8-of-nth-invsbox))
           :use ((:instance usb8-of-nth-invsbox (i (nth 0 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance usb8-of-nth-invsbox (i (nth 1 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance usb8-of-nth-invsbox (i (nth 2 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance usb8-of-nth-invsbox (i (nth 3 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance usb8-of-nth-invsbox (i (nth 4 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance usb8-of-nth-invsbox (i (nth 5 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance usb8-of-nth-invsbox (i (nth 6 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance usb8-of-nth-invsbox (i (nth 7 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance usb8-of-nth-invsbox (i (nth 8 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance usb8-of-nth-invsbox (i (nth 9 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance usb8-of-nth-invsbox (i (nth 10 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance usb8-of-nth-invsbox (i (nth 11 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance usb8-of-nth-invsbox (i (nth 12 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance usb8-of-nth-invsbox (i (nth 13 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance usb8-of-nth-invsbox (i (nth 14 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance usb8-of-nth-invsbox (i (nth 15 b))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15))))))

(defthm inp-of-map-invsbox16
  (implies (aes::inp b) (aes::inp (map-invsbox16 b)))
  :hints (("Goal" :in-theory (e/d (map-invsbox16 aes::inp acl2::bv-arrayp expand-len-16 unsigned-byte-p-of-logxor) (nth usb8-of-nth-invsbox logxor))
           :use ((:instance usb8-of-nth-invsbox (i (logxor (nth 0 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance usb8-of-nth-invsbox (i (logxor (nth 1 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance usb8-of-nth-invsbox (i (logxor (nth 2 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance usb8-of-nth-invsbox (i (logxor (nth 3 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance usb8-of-nth-invsbox (i (logxor (nth 4 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance usb8-of-nth-invsbox (i (logxor (nth 5 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance usb8-of-nth-invsbox (i (logxor (nth 6 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance usb8-of-nth-invsbox (i (logxor (nth 7 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance usb8-of-nth-invsbox (i (logxor (nth 8 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance usb8-of-nth-invsbox (i (logxor (nth 9 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance usb8-of-nth-invsbox (i (logxor (nth 10 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance usb8-of-nth-invsbox (i (logxor (nth 11 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance usb8-of-nth-invsbox (i (logxor (nth 12 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance usb8-of-nth-invsbox (i (logxor (nth 13 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance usb8-of-nth-invsbox (i (logxor (nth 14 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance usb8-of-nth-invsbox (i (logxor (nth 15 b) 99))) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15))))))

(defthm inp-of-imc0-bytes
  (implies (aes::inp b) (aes::inp (imc0-bytes b)))
  :hints (("Goal" :in-theory (e/d (imc0-bytes) (aes::inp)))))
(defthm inp-of-imc1-bytes
  (implies (aes::inp b) (aes::inp (imc1-bytes b)))
  :hints (("Goal" :in-theory (e/d (imc1-bytes) (aes::inp)))))
(defthm inp-of-imc2-bytes
  (implies (aes::inp b) (aes::inp (imc2-bytes b)))
  :hints (("Goal" :in-theory (e/d (imc2-bytes) (aes::inp)))))
(defthm inp-of-imc3-bytes
  (implies (aes::inp b) (aes::inp (imc3-bytes b)))
  :hints (("Goal" :in-theory (e/d (imc3-bytes) (aes::inp)))))

;; vocabulary: the extracted isr2 alias emits shift-rows-2-bytes; the frames use isr powers
(defthm sr2-is-isr2
  (implies (aes::inp b) (equal (shift-rows-2-bytes b) (inv-shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (shift-rows-2-bytes inv-shift-rows-2-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::array-elem-2d) (nth)))))

;; isr power table
(defthm isr1-of-isr1
  (implies (aes::inp b) (equal (inv-shift-rows-1-bytes (inv-shift-rows-1-bytes b)) (inv-shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))
(defthm isr1-of-isr2
  (implies (aes::inp b) (equal (inv-shift-rows-1-bytes (inv-shift-rows-2-bytes b)) (inv-shift-rows-3-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))
(defthm isr2-of-isr1
  (implies (aes::inp b) (equal (inv-shift-rows-2-bytes (inv-shift-rows-1-bytes b)) (inv-shift-rows-3-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))
(defthm isr1-of-isr3
  (implies (aes::inp b) (equal (inv-shift-rows-1-bytes (inv-shift-rows-3-bytes b)) b))
  :hints (("Goal" :use ((:instance expand-len-16 (x b)))
           :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (aes::inp)))))
(defthm isr3-of-isr1
  (implies (aes::inp b) (equal (inv-shift-rows-3-bytes (inv-shift-rows-1-bytes b)) b))
  :hints (("Goal" :use ((:instance expand-len-16 (x b)))
           :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (aes::inp)))))
(defthm isr2-of-isr2
  (implies (aes::inp b) (equal (inv-shift-rows-2-bytes (inv-shift-rows-2-bytes b)) b))
  :hints (("Goal" :use ((:instance expand-len-16 (x b)))
           :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (aes::inp)))))
(defthm isr2-of-isr3
  (implies (aes::inp b) (equal (inv-shift-rows-2-bytes (inv-shift-rows-3-bytes b)) (inv-shift-rows-1-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))
(defthm isr3-of-isr2
  (implies (aes::inp b) (equal (inv-shift-rows-3-bytes (inv-shift-rows-2-bytes b)) (inv-shift-rows-1-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))
(defthm isr3-of-isr3
  (implies (aes::inp b) (equal (inv-shift-rows-3-bytes (inv-shift-rows-3-bytes b)) (inv-shift-rows-2-bytes b)))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::array-elem-2d) (nth)))))

;; invsbox16 commutes with the frames (table kept opaque)
(local (defund isbx (x) (nth x (aes::invsbox))))
(local (defthm nth-invsbox-is-isbx (equal (nth x (aes::invsbox)) (isbx x))
  :hints (("Goal" :in-theory (enable isbx)))))
(defthm invsbox16-of-isr1
  (implies (aes::inp b) (equal (invsbox16 (inv-shift-rows-1-bytes b)) (inv-shift-rows-1-bytes (invsbox16 b))))
  :hints (("Goal" :in-theory (enable invsbox16 inv-shift-rows-1-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm invsbox16-of-isr2
  (implies (aes::inp b) (equal (invsbox16 (inv-shift-rows-2-bytes b)) (inv-shift-rows-2-bytes (invsbox16 b))))
  :hints (("Goal" :in-theory (enable invsbox16 inv-shift-rows-2-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::array-elem-2d))))
(defthm invsbox16-of-isr3
  (implies (aes::inp b) (equal (invsbox16 (inv-shift-rows-3-bytes b)) (inv-shift-rows-3-bytes (invsbox16 b))))
  :hints (("Goal" :in-theory (enable invsbox16 inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::array-elem-2d))))

;; frame telescoping: conjugated inverse MixColumns in its matched frame
(defthm frame-imc1-dec
  (implies (aes::inp b) (equal (imc1-bytes (inv-shift-rows-2-bytes b)) (inv-shift-rows-1-bytes (imc0-bytes (inv-shift-rows-1-bytes b)))))
  :hints (("Goal" :in-theory (e/d (imc1-bytes imc0-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))
(defthm frame-imc2-dec
  (implies (aes::inp b) (equal (imc2-bytes (inv-shift-rows-3-bytes b)) (inv-shift-rows-2-bytes (imc0-bytes (inv-shift-rows-1-bytes b)))))
  :hints (("Goal" :in-theory (e/d (imc2-bytes imc0-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))
(defthm frame-imc3-dec
  (implies (aes::inp b) (equal (imc3-bytes b) (inv-shift-rows-3-bytes (imc0-bytes (inv-shift-rows-1-bytes b)))))
  :hints (("Goal" :in-theory (e/d (imc3-bytes imc0-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))

;; round-core frame bridges: exactly the terms the decrypt ladder reaches
;; after the mask is associated out and cancelled -- state in frame
;; isr^{N+1}, window in frame isr^N; the conjugated inverse MixColumns
;; re-emits frame isr^N around the plain InvMixColumns of the spec's round
;; xor, telescoping one InvShiftRows.
(defthm dec-round-frame-1
  (implies (and (aes::inp v) (aes::inp k))
           (equal (imc1-bytes (xorbytes (inv-shift-rows-2-bytes v) (inv-shift-rows-1-bytes k)))
                  (inv-shift-rows-1-bytes (imc0-bytes (xorbytes (inv-shift-rows-1-bytes v) k)))))
  :hints (("Goal" :in-theory (e/d (imc1-bytes imc0-bytes xorbytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))
(defthm dec-round-frame-2
  (implies (and (aes::inp v) (aes::inp k))
           (equal (imc2-bytes (xorbytes (inv-shift-rows-3-bytes v) (inv-shift-rows-2-bytes k)))
                  (inv-shift-rows-2-bytes (imc0-bytes (xorbytes (inv-shift-rows-1-bytes v) k)))))
  :hints (("Goal" :in-theory (e/d (imc2-bytes imc0-bytes xorbytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))
(defthm dec-round-frame-3
  (implies (and (aes::inp v) (aes::inp k))
           (equal (imc3-bytes (xorbytes v (inv-shift-rows-3-bytes k)))
                  (inv-shift-rows-3-bytes (imc0-bytes (xorbytes (inv-shift-rows-1-bytes v) k)))))
  :hints (("Goal" :in-theory (e/d (imc3-bytes imc0-bytes xorbytes inv-shift-rows-1-bytes inv-shift-rows-3-bytes aes::copyarraytostate aes::copy-state-to-array aes::invshiftrows aes::shiftrows aes::invmixcolumns aes::array-elem-2d) (nth)))))

;; ---- GL section ----
;; mask associates out of the round-key xor
(gl::def-gl-thm xorbytes-sbn-assoc-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl (equal (xorbytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) (sub-bytes-nots-bytes (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
                (sub-bytes-nots-bytes (xorbytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm xorbytes-sbn-assoc
  (implies (and (aes::inp x) (aes::inp y))
           (equal (xorbytes x (sub-bytes-nots-bytes y)) (sub-bytes-nots-bytes (xorbytes x y))))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (xorbytes-sbn-assoc-gl xorbytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance xorbytes-sbn-assoc-gl (a0 (nth 0 x)) (a1 (nth 1 x)) (a2 (nth 2 x)) (a3 (nth 3 x)) (a4 (nth 4 x)) (a5 (nth 5 x)) (a6 (nth 6 x)) (a7 (nth 7 x)) (a8 (nth 8 x)) (a9 (nth 9 x)) (a10 (nth 10 x)) (a11 (nth 11 x)) (a12 (nth 12 x)) (a13 (nth 13 x)) (a14 (nth 14 x)) (a15 (nth 15 x)) (b0 (nth 0 y)) (b1 (nth 1 y)) (b2 (nth 2 y)) (b3 (nth 3 y)) (b4 (nth 4 y)) (b5 (nth 5 y)) (b6 (nth 6 y)) (b7 (nth 7 y)) (b8 (nth 8 y)) (b9 (nth 9 y)) (b10 (nth 10 y)) (b11 (nth 11 y)) (b12 (nth 12 y)) (b13 (nth 13 y)) (b14 (nth 14 y)) (b15 (nth 15 y))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

;; the schedule mask cancels into the inverse S-box input compensation
(gl::def-gl-thm misb-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (map-invsbox16 (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))) (invsbox16 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))
(defthm misb-of-sbn
  (implies (aes::inp b)
           (equal (map-invsbox16 (sub-bytes-nots-bytes b)) (invsbox16 b)))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (misb-of-sbn-gl map-invsbox16 invsbox16 sub-bytes-nots-bytes aes::inp nth))
           :use (:instance misb-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

;; the uniform mask is fixed by (conjugated) inverse MixColumns
(gl::def-gl-thm imc0-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (imc0-bytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
                (sub-bytes-nots-bytes (imc0-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))
(defthm imc0-of-sbn
  (implies (aes::inp b)
           (equal (imc0-bytes (sub-bytes-nots-bytes b)) (sub-bytes-nots-bytes (imc0-bytes b))))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (imc0-of-sbn-gl imc0-bytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance imc0-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

(gl::def-gl-thm imc1-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (imc1-bytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
                (sub-bytes-nots-bytes (imc1-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a5 8) (:nat a10 8) (:nat a15 8) (:nat a4 8) (:nat a9 8) (:nat a14 8) (:nat a3 8) (:nat a8 8) (:nat a13 8) (:nat a2 8) (:nat a7 8) (:nat a12 8) (:nat a1 8) (:nat a6 8) (:nat a11 8)))
(defthm imc1-of-sbn
  (implies (aes::inp b)
           (equal (imc1-bytes (sub-bytes-nots-bytes b)) (sub-bytes-nots-bytes (imc1-bytes b))))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (imc1-of-sbn-gl imc1-bytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance imc1-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

(gl::def-gl-thm imc2-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (imc2-bytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
                (sub-bytes-nots-bytes (imc2-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a9 8) (:nat a2 8) (:nat a11 8) (:nat a4 8) (:nat a13 8) (:nat a6 8) (:nat a15 8) (:nat a8 8) (:nat a1 8) (:nat a10 8) (:nat a3 8) (:nat a12 8) (:nat a5 8) (:nat a14 8) (:nat a7 8)))
(defthm imc2-of-sbn
  (implies (aes::inp b)
           (equal (imc2-bytes (sub-bytes-nots-bytes b)) (sub-bytes-nots-bytes (imc2-bytes b))))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (imc2-of-sbn-gl imc2-bytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance imc2-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))

(gl::def-gl-thm imc3-of-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl (equal (imc3-bytes (sub-bytes-nots-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
                (sub-bytes-nots-bytes (imc3-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a13 8) (:nat a10 8) (:nat a7 8) (:nat a4 8) (:nat a1 8) (:nat a14 8) (:nat a11 8) (:nat a8 8) (:nat a5 8) (:nat a2 8) (:nat a15 8) (:nat a12 8) (:nat a9 8) (:nat a6 8) (:nat a3 8)))
(defthm imc3-of-sbn
  (implies (aes::inp b)
           (equal (imc3-bytes (sub-bytes-nots-bytes b)) (sub-bytes-nots-bytes (imc3-bytes b))))
  :hints (("Goal" :in-theory (e/d (expand-len-16) (imc3-of-sbn-gl imc3-bytes sub-bytes-nots-bytes aes::inp nth))
           :use (:instance imc3-of-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))))
(value-triple (clear-memoize-tables))
(value-triple (hons-clear t))
