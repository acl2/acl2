; Phase 5 -- cipher side, part 4: per-op push-in rules for the encrypt chain.
;
; The enc-chain ops differ from the Phase-3/4 set in three ways: the cipher
; applies BARE sub_bytes (the fixslice NOTs live in the round keys, per the
; key-schedule fold), it uses all four mix_columns rotations, and its
; add_round_key appears as the collapsed arkw-spec window xor.  This book
; supplies, for each chain op, the two facts the round ladder threads:
;   push-in :  inv_bitslice(op(S)) = op-bytes(inv_bitslice(S))   (per lane)
;   type    :  wstatep(op(S))
; for ARBITRARY wstatep S -- derived from through-packing GL facts by the
; bitslice-of-inv-bitslice fold, as in aes_fixslice_round.
;
; The one new GL bit-blast: bare sub_bytes through the packing is
; xor63 o sbox per lane (equivalently: sub_bytes_nots is an involution and
; sub_bytes_nots o sub_bytes is SubBytes -- checked as stated instead, so
; the ladder rule is direct).  Everything else is GL type facts (8 u32) or
; pure rewriting.
(in-package "ACL2")
(include-book "aes_fixslice_cipher")
(include-book "aes_fixslice_rounds")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

;; ===========================================================================
;; (A) BARE sub_bytes through the packing: xor63 o sbox per lane.
(gl::def-gl-thm bare-subbytes-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val
             (aes-fixslice-encrypt-inv-bitslice
               (result-ok->val (aes-fixslice-encrypt-sub-bytes (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (sub-bytes-nots-bytes (map-sbox16 blk0))
                 (sub-bytes-nots-bytes (map-sbox16 blk1)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))
(defthm bare-subbytes-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-sub-bytes (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (sub-bytes-nots-bytes (map-sbox16 b0))
                        (sub-bytes-nots-bytes (map-sbox16 b1)))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (bare-subbytes-gl aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-bitslice aes::inp
                            sub-bytes-nots-bytes map-sbox16 nth))
           :use (:instance bare-subbytes-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
(gl::def-gl-thm wstatep-of-bare-subbytes-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-bare-subbytes
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-bare-subbytes-gl aes-fixslice-encrypt-sub-bytes nth))
           :use (:instance wstatep-of-bare-subbytes-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

;; ===========================================================================
;; (B) wstatep preservation for the rotated mix_columns and shift_rows_2.
(gl::def-gl-thm wstatep-of-mixcolumns1-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-mixcolumns1
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-mixcolumns1-gl aes-fixslice-encrypt-mix-columns-1 nth))
           :use (:instance wstatep-of-mixcolumns1-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(gl::def-gl-thm wstatep-of-mixcolumns2-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-mixcolumns2
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-mixcolumns2-gl aes-fixslice-encrypt-mix-columns-2 nth))
           :use (:instance wstatep-of-mixcolumns2-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(gl::def-gl-thm wstatep-of-mixcolumns3-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-mixcolumns3
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-mixcolumns3-gl aes-fixslice-encrypt-mix-columns-3 nth))
           :use (:instance wstatep-of-mixcolumns3-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(gl::def-gl-thm wstatep-of-sr2-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-sr2
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-sr2-gl aes-fixslice-encrypt-shift-rows-2 nth))
           :use (:instance wstatep-of-sr2-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

;; ===========================================================================
;; (C) push-in rules on arbitrary wstatep states (bitslice-of-inv-bitslice
;; fold of the through-packing facts, as in aes_fixslice_round).
(defthm inv-bitslice-of-bare-subbytes
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
                  (list (sub-bytes-nots-bytes (map-sbox16 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))
                        (sub-bytes-nots-bytes (map-sbox16 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (bare-subbytes-general aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            sub-bytes-nots-bytes map-sbox16 nth))
           :use (:instance bare-subbytes-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))
(defthm inv-bitslice-of-mixcolumns1
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s))))
                  (list (mix-columns-1-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (mix-columns-1-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (mix-columns-1-general aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            mix-columns-1-bytes nth))
           :use (:instance mix-columns-1-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))
(defthm inv-bitslice-of-mixcolumns2
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s))))
                  (list (mix-columns-2-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (mix-columns-2-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (mix-columns-2-general aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            mix-columns-2-bytes nth))
           :use (:instance mix-columns-2-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))
(defthm inv-bitslice-of-mixcolumns3
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s))))
                  (list (mix-columns-3-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (mix-columns-3-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (mix-columns-3-general aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            mix-columns-3-bytes nth))
           :use (:instance mix-columns-3-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))
(defthm inv-bitslice-of-sr2
  (implies (wstatep s)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 s))))
                  (list (shift-rows-2-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (shift-rows-2-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (shift-rows-2-general aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice aes::inp
                            shift-rows-2-bytes nth))
           :use (:instance shift-rows-2-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; ===========================================================================
;; (D) the collapsed add_round_key window: shift to a window read, then the
;; Phase-3 xor fact.
(defthm arkw-window-shift-gen
  (implies (and (natp i) (natp e) (<= e 8) (natp off))
           (equal (arkw-spec i e s (rd8 rk off) 0)
                  (arkw-spec i e s rk off)))
  :hints (("Goal" :induct (arkw-spec i e s rk off)
           :in-theory (e/d () (u32-xor nth rd8))))
  :rule-classes nil)
(defthm inv-bitslice-of-arkw-window
  (implies (and (wstatep s) (wstatep (rd8 rk off)) (natp off))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (arkw-spec 0 8 s rk off)))
                  (list (xorbytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))
                                  (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 rk off)))))
                        (xorbytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))
                                  (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 rk off))))))))
  :hints (("Goal"
           :in-theory (e/d () (arkw-spec aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-add-round-key rd8 xorbytes nth wstatep
                               inv-bitslice-of-addroundkey))
           :use ((:instance arkw-window-shift-gen (i 0) (e 8))
                 (:instance ark-form100 (w (rd8 rk off)))
                 (:instance inv-bitslice-of-addroundkey (k (rd8 rk off)))
                 (:instance len-when-wstatep (x (rd8 rk off)))
                 (:instance len-when-wstatep (x s))))))
(defthm wstatep-of-arkw-window
  (implies (and (wstatep s) (wstatep (rd8 rk off)) (natp off))
           (wstatep (arkw-spec 0 8 s rk off)))
  :hints (("Goal"
           :in-theory (e/d () (arkw-spec aes-fixslice-encrypt-add-round-key rd8 nth wstatep
                               wstatep-of-addroundkey))
           :use ((:instance arkw-window-shift-gen (i 0) (e 8))
                 (:instance ark-form100 (w (rd8 rk off)))
                 (:instance wstatep-of-addroundkey (k (rd8 rk off)))
                 (:instance len-when-wstatep (x (rd8 rk off)))
                 (:instance len-when-wstatep (x s))))))
