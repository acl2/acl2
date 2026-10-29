; Phase 4 -- key-schedule per-op facts + the key-schedule correspondence.
;
; The fixslice key schedule computes Kestrel's key expansion, then folds in the
; encrypt's ShiftRows rotation and the S-box-affine NOTs. This book proves the
; per-op facts of that fold (each bit-blasted through the packing), and states
; the resulting round-key correspondence (confirmed by execution below):
;
;   fk(0)  = kk(0)                                     (round-0 key = the key)
;   fk(r)  = xor63( invshiftrows^(r mod 4)( kk(r) ) )  for r = 1..9
;   fk(10) = xor63( kk(10) )
;
; where fk(r) = the fixslice round key r un-bitsliced (lane 0), kk(r) = Kestrel
; keyexpansion round key r, xor63 = byte-wise XOR 0x63 (the removed S-box affine),
; invshiftrows the spec op. sub_bytes_nots supplies the xor63; inv_shift_rows_i
; supplies the invshiftrows^i. The core (10 key_rounds == Kestrel keyexpansion,
; bitsliced) is the remaining piece; see the roadmap note at the end.
(in-package "ACL2")
(include-book "aes_fixslice_shiftrows")

;; ---- sub-bytes-nots ----
(defund sub-bytes-nots-bytes (b) (list (logxor (nth 0 b) 99) (logxor (nth 1 b) 99) (logxor (nth 2 b) 99) (logxor (nth 3 b) 99) (logxor (nth 4 b) 99) (logxor (nth 5 b) 99) (logxor (nth 6 b) 99) (logxor (nth 7 b) 99) (logxor (nth 8 b) 99) (logxor (nth 9 b) 99) (logxor (nth 10 b) 99) (logxor (nth 11 b) 99) (logxor (nth 12 b) 99) (logxor (nth 13 b) 99) (logxor (nth 14 b) 99) (logxor (nth 15 b) 99)))
(gl::def-gl-thm sub-bytes-nots-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (sub-bytes-nots-bytes blk0) (sub-bytes-nots-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm sub-bytes-nots-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (sub-bytes-nots-bytes b0) (sub-bytes-nots-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (sub-bytes-nots-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-inv-bitslice aes::inp sub-bytes-nots-bytes nth))
           :use (:instance sub-bytes-nots-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

;; ---- inv-shift-rows-1 ----
(defund inv-shift-rows-1-bytes (b) (aes::copy-state-to-array (aes::invshiftrows (aes::copyarraytostate b))))
(gl::def-gl-thm inv-shift-rows-1-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (inv-shift-rows-1-bytes blk0) (inv-shift-rows-1-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm inv-shift-rows-1-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (inv-shift-rows-1-bytes b0) (inv-shift-rows-1-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-shift-rows-1-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-inv-bitslice aes::inp inv-shift-rows-1-bytes nth))
           :use (:instance inv-shift-rows-1-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

;; ---- inv-shift-rows-3 ----
(defund inv-shift-rows-3-bytes (b) (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::invshiftrows (aes::copyarraytostate b))))))
(gl::def-gl-thm inv-shift-rows-3-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (inv-shift-rows-3-bytes blk0) (inv-shift-rows-3-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm inv-shift-rows-3-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (inv-shift-rows-3-bytes b0) (inv-shift-rows-3-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-shift-rows-3-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-shift-rows-3
                            aes-fixslice-encrypt-inv-bitslice aes::inp inv-shift-rows-3-bytes nth))
           :use (:instance inv-shift-rows-3-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))


;; ---------------------------------------------------------------------------
;; Concrete validation of the round-key correspondence (executable check on the
;; FIPS-197 C.1 key; the all-inputs proof of the core expansion is future work).
(local
 (progn
   (defun ks-fk (rk r)
     (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (take 8 (nthcdr (* 8 r) rk))))))
   (defun ks-kk (w r)
     (append (nth (* 4 r) w) (nth (+ 1 (* 4 r)) w) (nth (+ 2 (* 4 r)) w) (nth (+ 3 (* 4 r)) w)))
   (defun ks-xor63 (b) (if (endp b) nil (cons (logxor (car b) #x63) (ks-xor63 (cdr b)))))
   (defun ks-isr (b) (aes::copy-state-to-array (aes::invshiftrows (aes::copyarraytostate b))))
   (defun ks-isrn (n b) (declare (xargs :measure (nfix n))) (if (zp n) b (ks-isr (ks-isrn (1- n) b))))
   ;; expected fixslice round key r from Kestrel round key r
   (defun ks-expected (w r)
     (cond ((equal r 0)  (ks-kk w 0))
           ((equal r 10) (ks-xor63 (ks-kk w 10)))
           (t            (ks-xor63 (ks-isrn (mod r 4) (ks-kk w r))))))
   (defconst *ks-key* '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))
   (defconst *ks-rk*  (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 *ks-key*)))
   (defconst *ks-w*   (aes::keyexpansion *ks-key* 4))
   (defun ks-all-match (r)
     (declare (xargs :measure (nfix (- 11 r))))
     (if (or (not (natp r)) (> r 10)) t
       (and (equal (ks-fk *ks-rk* r) (ks-expected *ks-w* r)) (ks-all-match (1+ r)))))
   ;; all 11 round keys satisfy  fk(r) = xor63(invshiftrows^(r mod 4)(kk r)):
   (assert-event (ks-all-match 0))))

;; ---------------------------------------------------------------------------
;; ROADMAP -- what remains for aes128_key_schedule == Kestrel keyexpansion:
;;
;; The correspondence above is the SPEC of the key schedule in Kestrel terms.
;; This book proves the FOLD layer's per-op facts (sub_bytes_nots = xor63,
;; inv_shift_rows_i = invshiftrows^i through the packing). What remains is the
;; CORE: that the 10 unrolled key_round steps produce bitslice(kk(r)) for each r
;; -- i.e. the fixslice key expansion computes Kestrel's keyexpansion, bitsliced.
;; Each key_round is memshift (copy prev) ; sub_bytes+nots (= SubWord, a full
;; S-box, already validated) ; add_rcon (= Rcon) ; xor_columns (the bitsliced AES
;; column recurrence w[i] = w[i-4] ^ transform(w[i-1])). The open work is
;; xor_columns == that recurrence and chaining it through the 88-word rkeys
;; array; that's a bit-level + array-threading induction, the largest single
;; remaining piece of the encrypt == AES::aes-128-encrypt proof.
