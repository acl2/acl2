; Phase 4 -- key schedule STEP layer: krw8 preserves the symmetric-bitslice form
; and advances the block by the AES key-expansion recurrence, for ALL inputs.
;
;   step-star-c (c = 0..9):  (aes::inp b) =>
;       krw8(bitslice(b,b), c) = bitslice(kr-spec(b,xpow_c), kr-spec(b,xpow_c))
;   where xpow = [1,2,4,8,16,32,64,128,27,54] and kr-spec(b,rv) = kr-spec-bytes.
;
; This is the both-lanes-equal INVARIANT the 88-word key-schedule array threads:
; window_0 = bitslice(key,key), and each key_round advances window_{r+1} =
; krw8(window_r, r) = bitslice(kk_{r+1}, kk_{r+1}) with kk = kk-iter (the iterated
; recurrence).  krw8-crux-c gave only the lane-0 readback; step-star-c gives the
; whole window, so the chain stays in bitslice(block,block) form.
;
; Each step-star-c is a GL fact over the 16 key bytes lifted to (aes::inp b) with
; the standard -general idiom (restate with bytes explicit, fold with
; expand-len-16 under ground-zero).  inp-of-kr-spec-bytes closes the recurrence:
; kr-spec of an inp block (and a byte rcon) is again an inp block, so the
; invariant reproduces at each round.
(in-package "ACL2")
(include-book "aes_fixslice_keycrux")
(local (include-book "std/lists/append" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

;; xpow column and the iterated key-expansion recurrence (non-local: theorems
;; below and the array chain are stated over these).
(defun kx (c) (nth c '(1 2 4 8 16 32 64 128 27 54)))
(defun kk-iter (key r)
  (declare (xargs :measure (nfix r)))
  (if (zp r) key (kr-spec-bytes (kk-iter key (1- r)) (kx (1- r)))))

;; ---------------------------------------------------------------------------
;; inp-closure: kr-spec of an inp block and a byte rcon is again an inp block.
;; len/true-listp are purely structural (append of four 4-lists); keep nth and
;; the bitwise ops closed so the irrelevant element values are never opened.
(defthm len-of-kr-spec-bytes
  (equal (len (kr-spec-bytes b rv)) 16)
  :hints (("Goal" :in-theory (e/d (kr-spec-bytes xorw)
                                  (nth binary-logxor binary-logand binary-logior
                                   binary-logeqv lognot logorc1)))))
(defthm true-listp-of-kr-spec-bytes
  (true-listp (kr-spec-bytes b rv))
  :hints (("Goal" :in-theory (e/d (kr-spec-bytes xorw)
                                  (nth binary-logxor binary-logand binary-logior
                                   binary-logeqv lognot logorc1)))))

(gl::def-gl-thm all-ubp8-kr-spec-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 rv))
  :concl (all-unsigned-byte-p 8 (kr-spec-bytes (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) rv))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat rv 8)))

;; byte-level restatement (explicit (nth i b)); the fold target for the lift.
(defthm all-ubp8-kr-spec-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)) (unsigned-byte-p 8 rv))
           (all-unsigned-byte-p 8 (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) rv)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance all-ubp8-kr-spec-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm all-ubp8-kr-spec
  (implies (and (aes::inp b) (unsigned-byte-p 8 rv))
           (all-unsigned-byte-p 8 (kr-spec-bytes b rv)))
  :hints (("Goal" :do-not-induct t
           :use (all-ubp8-kr-spec-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

(defthm inp-of-kr-spec-bytes
  (implies (and (aes::inp b) (unsigned-byte-p 8 rv))
           (aes::inp (kr-spec-bytes b rv)))
  :hints (("Goal" :use (all-ubp8-kr-spec)
           :in-theory (e/d (aes::inp acl2::bv-arrayp)
                           (kr-spec-bytes all-unsigned-byte-p)))))

;; also: bitslice of two inp blocks that are equal is a wstate (specialize).

;; ---- step-star c = 0 (xpow 1) ----
(gl::def-gl-thm step-star-0-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 0)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 1) (kr-spec-bytes b 1)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-0-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 0)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 1) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 1)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-0-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-0-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 0)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 1) (kr-spec-bytes b 1)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-0-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 1 (xpow 2) ----
(gl::def-gl-thm step-star-1-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 1)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 2) (kr-spec-bytes b 2)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-1-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 1)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 2) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-1-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-1-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 1)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 2) (kr-spec-bytes b 2)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-1-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 2 (xpow 4) ----
(gl::def-gl-thm step-star-2-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 2)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 4) (kr-spec-bytes b 4)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-2-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 2)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 4) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 4)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-2-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-2-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 2)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 4) (kr-spec-bytes b 4)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-2-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 3 (xpow 8) ----
(gl::def-gl-thm step-star-3-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 3)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 8) (kr-spec-bytes b 8)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-3-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 3)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 8) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 8)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-3-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-3-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 3)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 8) (kr-spec-bytes b 8)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-3-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 4 (xpow 16) ----
(gl::def-gl-thm step-star-4-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 4)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 16) (kr-spec-bytes b 16)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-4-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 4)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 16) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 16)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-4-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-4-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 4)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 16) (kr-spec-bytes b 16)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-4-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 5 (xpow 32) ----
(gl::def-gl-thm step-star-5-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 5)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 32) (kr-spec-bytes b 32)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-5-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 5)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 32) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 32)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-5-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-5-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 5)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 32) (kr-spec-bytes b 32)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-5-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 6 (xpow 64) ----
(gl::def-gl-thm step-star-6-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 6)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 64) (kr-spec-bytes b 64)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-6-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 6)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 64) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 64)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-6-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-6-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 6)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 64) (kr-spec-bytes b 64)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-6-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 7 (xpow 128) ----
(gl::def-gl-thm step-star-7-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 7)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 128) (kr-spec-bytes b 128)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-7-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 7)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 128) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 128)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-7-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-7-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 7)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 128) (kr-spec-bytes b 128)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-7-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 8 (xpow 27) ----
(gl::def-gl-thm step-star-8-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 8)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 27) (kr-spec-bytes b 27)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-8-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 8)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 27) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 27)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-8-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-8-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 8)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 27) (kr-spec-bytes b 27)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-8-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

;; ---- step-star c = 9 (xpow 54) ----
(gl::def-gl-thm step-star-9-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15))
  :concl
  (let* ((b (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)))
    (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 9)
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 54) (kr-spec-bytes b 54)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8)))

(defthm step-star-9-bytes
  (implies (and (unsigned-byte-p 8 (nth 0 b)) (unsigned-byte-p 8 (nth 1 b)) (unsigned-byte-p 8 (nth 2 b)) (unsigned-byte-p 8 (nth 3 b)) (unsigned-byte-p 8 (nth 4 b)) (unsigned-byte-p 8 (nth 5 b)) (unsigned-byte-p 8 (nth 6 b)) (unsigned-byte-p 8 (nth 7 b)) (unsigned-byte-p 8 (nth 8 b)) (unsigned-byte-p 8 (nth 9 b)) (unsigned-byte-p 8 (nth 10 b)) (unsigned-byte-p 8 (nth 11 b)) (unsigned-byte-p 8 (nth 12 b)) (unsigned-byte-p 8 (nth 13 b)) (unsigned-byte-p 8 (nth 14 b)) (unsigned-byte-p 8 (nth 15 b)))
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))) 9)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 54) (kr-spec-bytes (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b) (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b) (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b) (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)) 54)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-star-9-gl (a0 (nth 0 b)) (a1 (nth 1 b)) (a2 (nth 2 b)) (a3 (nth 3 b)) (a4 (nth 4 b)) (a5 (nth 5 b)) (a6 (nth 6 b)) (a7 (nth 7 b)) (a8 (nth 8 b)) (a9 (nth 9 b)) (a10 (nth 10 b)) (a11 (nth 11 b)) (a12 (nth 12 b)) (a13 (nth 13 b)) (a14 (nth 14 b)) (a15 (nth 15 b))))
           :in-theory (union-theories (theory 'ground-zero) '()))))

(defthm step-star-9-general
  (implies (aes::inp b)
           (equal (krw8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) 9)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kr-spec-bytes b 54) (kr-spec-bytes b 54)))))
  :hints (("Goal" :do-not-induct t
           :use (step-star-9-bytes (:instance expand-len-16 (x b)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 0)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 1)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 2)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 3)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 4)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 5)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 6)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 7)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 8)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 9)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 10)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 11)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 12)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 13)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 14)) (:instance unsigned-byte-p-8-of-nth-when-inp (x b) (i 15)))
           :in-theory (union-theories (theory 'ground-zero)
                                      '(true-listp-when-inp len-when-inp)))))

