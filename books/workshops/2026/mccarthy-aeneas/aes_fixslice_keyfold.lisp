; Phase 4 -- key-schedule FOLD layer: the per-op "preserves symmetric bitslice"
; facts, for ALL inputs.  Each fold op, applied to a both-lanes-equal window
; bitslice(b,b), stays a both-lanes-equal window with the byte-level transform
; applied to each lane:
;
;   op*(op = inv_shift_rows_{1,2,3} / sub_bytes_nots):  (aes::inp b) =>
;     op(bitslice(b,b)) = bitslice(op-bytes(b), op-bytes(b))
;
; where op-bytes is invshiftrows^i / xor63 (bytewise ^0x63).  So threading the
; extracted fold's inv_shift_rows/sub_bytes_nots ops over the core windows
; (= bitslice(kk_r,kk_r), from keyexpand) keeps them symmetric bitslices, and
; the final window r reads back as fk(r) = xor63(invshiftrows^{r mod 4}(kk_r)).
; GL fact per op, lifted to (aes::inp b) with the standard -general idiom.
;
; And the per-window READBACK facts fk-read-{isr1,isr2,isr3,sbn}: for a symmetric
; window bitslice(b,b), applying the fold ops that hit that window and reading
; lane 0 back through inv_bitslice gives the byte-level fk value directly --
;   isr_i then sub_bytes_nots  ->  xor63(invshiftrows^i(b))
;   sub_bytes_nots only        ->  xor63(b)
;   (no fold op, window 0)     ->  b       [inv_bitslice o bitslice = id]
; This is the full fold math, all inputs.  What remains to reach the extracted
; aes128_key_schedule correspondence is the read-over-write threading of the 17
; concrete at-ops over the 11 windows (each at-op = w8-spec: transform one window,
; frame the rest) -- pure array bookkeeping over these facts + the core windows.
(in-package "ACL2")
(include-book "aes_fixslice_keyexpand")
(include-book "aes_fixslice_keyschedule")

;; inv_shift_rows^2 byte transform (keyschedule has 1 and 3 but not 2).
(defund inv-shift-rows-2-bytes (b)
  (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::copyarraytostate b)))))

;; ---- isr1: op preserves symmetric bitslice ----
(gl::def-gl-thm isr1-star-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-1-bytes b) (inv-shift-rows-1-bytes b)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm isr1-star-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-1-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))) (inv-shift-rows-1-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance isr1-star-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm isr1-star
  (implies (aes::inp b)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-1-bytes b) (inv-shift-rows-1-bytes b)))))
  :hints (("Goal" :do-not-induct t
           :use (isr1-star-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- isr2: op preserves symmetric bitslice ----
(gl::def-gl-thm isr2-star-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-2-bytes b) (inv-shift-rows-2-bytes b)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm isr2-star-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-2-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))) (inv-shift-rows-2-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance isr2-star-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm isr2-star
  (implies (aes::inp b)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-2-bytes b) (inv-shift-rows-2-bytes b)))))
  :hints (("Goal" :do-not-induct t
           :use (isr2-star-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- isr3: op preserves symmetric bitslice ----
(gl::def-gl-thm isr3-star-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-3-bytes b) (inv-shift-rows-3-bytes b)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm isr3-star-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-3-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))) (inv-shift-rows-3-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance isr3-star-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm isr3-star
  (implies (aes::inp b)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (inv-shift-rows-3-bytes b) (inv-shift-rows-3-bytes b)))))
  :hints (("Goal" :do-not-induct t
           :use (isr3-star-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- sbn: op preserves symmetric bitslice ----
(gl::def-gl-thm sbn-star-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes b) (sub-bytes-nots-bytes b)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm sbn-star-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))) (sub-bytes-nots-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance sbn-star-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm sbn-star
  (implies (aes::inp b)
           (equal (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))))
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes b) (sub-bytes-nots-bytes b)))))
  :hints (("Goal" :do-not-induct t
           :use (sbn-star-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ===========================================================================
;; Per-window fold READBACK: for a symmetric window bitslice(b,b), applying the
;; extracted fold ops at that window and reading lane 0 back through inv_bitslice
;; gives the byte-level fk value.  Windows that get inv_shift_rows_i then
;; sub_bytes_nots read to xor63(invshiftrows^i(b)); windows that get only
;; sub_bytes_nots read to xor63(b); window 0 (no fold op) reads to b.
;; ===========================================================================

;; ---- window kind: isr1 ----
(gl::def-gl-thm fk-read-isr1-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
           (sub-bytes-nots-bytes (inv-shift-rows-1-bytes b))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm fk-read-isr1-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fk-read-isr1-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm fk-read-isr1
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes b))))
  :hints (("Goal" :do-not-induct t
           :use (fk-read-isr1-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- window kind: isr2 ----
(gl::def-gl-thm fk-read-isr2-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
           (sub-bytes-nots-bytes (inv-shift-rows-2-bytes b))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm fk-read-isr2-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fk-read-isr2-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm fk-read-isr2
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes b))))
  :hints (("Goal" :do-not-induct t
           :use (fk-read-isr2-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- window kind: isr3 ----
(gl::def-gl-thm fk-read-isr3-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
           (sub-bytes-nots-bytes (inv-shift-rows-3-bytes b))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm fk-read-isr3-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fk-read-isr3-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm fk-read-isr3
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes b))))
  :hints (("Goal" :do-not-induct t
           :use (fk-read-isr3-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- window kind: sbn ----
(gl::def-gl-thm fk-read-sbn-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))
           (sub-bytes-nots-bytes b)))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm fk-read-sbn-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))))))
                  (sub-bytes-nots-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fk-read-sbn-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm fk-read-sbn
  (implies (aes::inp b)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))))))
                  (sub-bytes-nots-bytes b)))
  :hints (("Goal" :do-not-induct t
           :use (fk-read-sbn-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))
