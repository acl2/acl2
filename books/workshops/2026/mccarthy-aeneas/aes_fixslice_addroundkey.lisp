; Phase 3 (per-op equivalence) -- AddRoundKey.
;
; add_round_key XORs the (bitsliced) round-key words into the state words, and
; inv_bitslice is GF(2)-linear, so through the packing it is byte-wise XOR of
; the state bytes with the unpacked key bytes -- which is exactly AES
; AddRoundKey. Proved for ALL 2^256 states and ANY key-state by centaur/gl.
; (The full doubly-bitsliced composition overran GL's BDDs, so the key is left
; as a symbolic State K here -- more general anyway, matching how the cipher
; feeds arbitrary round-key states -- and inv_bitslice's own linearity carries
; the XOR through.)
(in-package "ACL2")
(include-book "aes_fixslice_correspondence")

(defund xorbytes (x y)   ; byte-wise AES add (bvxor 8), explicit so nth computes
  (list (aes::binary-gf256add (nth 0 x)  (nth 0 y))  (aes::binary-gf256add (nth 1 x)  (nth 1 y))
        (aes::binary-gf256add (nth 2 x)  (nth 2 y))  (aes::binary-gf256add (nth 3 x)  (nth 3 y))
        (aes::binary-gf256add (nth 4 x)  (nth 4 y))  (aes::binary-gf256add (nth 5 x)  (nth 5 y))
        (aes::binary-gf256add (nth 6 x)  (nth 6 y))  (aes::binary-gf256add (nth 7 x)  (nth 7 y))
        (aes::binary-gf256add (nth 8 x)  (nth 8 y))  (aes::binary-gf256add (nth 9 x)  (nth 9 y))
        (aes::binary-gf256add (nth 10 x) (nth 10 y)) (aes::binary-gf256add (nth 11 x) (nth 11 y))
        (aes::binary-gf256add (nth 12 x) (nth 12 y)) (aes::binary-gf256add (nth 13 x) (nth 13 y))
        (aes::binary-gf256add (nth 14 x) (nth 14 y)) (aes::binary-gf256add (nth 15 x) (nth 15 y))))

;; 16 bytes as Kestrel's 4 key COLUMNS (words) -- the roundkey layout addroundkey
;; expects (it indexes the key transposed to the state's rows).
(defund bytes->cols (b)
  (list (list (nth 0 b)  (nth 1 b)  (nth 2 b)  (nth 3 b))
        (list (nth 4 b)  (nth 5 b)  (nth 6 b)  (nth 7 b))
        (list (nth 8 b)  (nth 9 b)  (nth 10 b) (nth 11 b))
        (list (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b))))

;; GL crux: fixslice AddRoundKey through the packing = byte-wise XOR.
(gl::def-gl-thm add-round-key-through-packing
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15) (unsigned-byte-p 32 k0) (unsigned-byte-p 32 k1) (unsigned-byte-p 32 k2) (unsigned-byte-p 32 k3) (unsigned-byte-p 32 k4) (unsigned-byte-p 32 k5) (unsigned-byte-p 32 k6) (unsigned-byte-p 32 k7))
  :concl
  (b* ((s0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (s1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)) (kk (list k0 k1 k2 k3 k4 k5 k6 k7))
       (out (result-ok->val (aes-fixslice-encrypt-inv-bitslice
              (result-ok->val (aes-fixslice-encrypt-add-round-key 100
                (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) s0 s1)) kk)))))
       (ik (result-ok->val (aes-fixslice-encrypt-inv-bitslice kk))))
    (equal out (list (xorbytes s0 (car ik)) (xorbytes s1 (cadr ik)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8) (:nat k0 32) (:nat k1 32) (:nat k2 32) (:nat k3 32) (:nat k4 32) (:nat k5 32) (:nat k6 32) (:nat k7 32)))

;; Kestrel AddRoundKey (byte-wise XOR) commutes with the column-major load
;; when the key is given as columns.
(defthm addroundkey-of-copyarraytostate
  (implies (and (aes::inp a) (aes::inp b))
           (equal (aes::addroundkey (aes::copyarraytostate a) (bytes->cols b))
                  (aes::copyarraytostate (xorbytes a b))))
  :hints (("Goal" :in-theory (e/d (aes::addroundkey aes::addroundkey-elem
                                   aes::copyarraytostate aes::array-elem-2d
                                   aes::binary-gf256add xorbytes bytes->cols expand-len-16)
                                  (nth)))))

;; Lift the GL crux to general blocks s0,s1 (K an explicit 8-word state).
(defthm add-round-key-through-packing-general
  (implies (and (aes::inp s0) (aes::inp s1) (unsigned-byte-p 32 k0) (unsigned-byte-p 32 k1) (unsigned-byte-p 32 k2) (unsigned-byte-p 32 k3) (unsigned-byte-p 32 k4) (unsigned-byte-p 32 k5) (unsigned-byte-p 32 k6) (unsigned-byte-p 32 k7))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-add-round-key 100
                        (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) s0 s1)) (list k0 k1 k2 k3 k4 k5 k6 k7)))))
                  (list (xorbytes s0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list k0 k1 k2 k3 k4 k5 k6 k7)))))
                        (xorbytes s1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list k0 k1 k2 k3 k4 k5 k6 k7))))))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (add-round-key-through-packing
                            aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-add-round-key
                            aes-fixslice-encrypt-inv-bitslice aes::inp xorbytes nth))
           :use (:instance add-round-key-through-packing
                  (a0 (nth 0 s0))
                  (a1 (nth 1 s0))
                  (a2 (nth 2 s0))
                  (a3 (nth 3 s0))
                  (a4 (nth 4 s0))
                  (a5 (nth 5 s0))
                  (a6 (nth 6 s0))
                  (a7 (nth 7 s0))
                  (a8 (nth 8 s0))
                  (a9 (nth 9 s0))
                  (a10 (nth 10 s0))
                  (a11 (nth 11 s0))
                  (a12 (nth 12 s0))
                  (a13 (nth 13 s0))
                  (a14 (nth 14 s0))
                  (a15 (nth 15 s0))
                  (b0 (nth 0 s1))
                  (b1 (nth 1 s1))
                  (b2 (nth 2 s1))
                  (b3 (nth 3 s1))
                  (b4 (nth 4 s1))
                  (b5 (nth 5 s1))
                  (b6 (nth 6 s1))
                  (b7 (nth 7 s1))
                  (b8 (nth 8 s1))
                  (b9 (nth 9 s1))
                  (b10 (nth 10 s1))
                  (b11 (nth 11 s1))
                  (b12 (nth 12 s1))
                  (b13 (nth 13 s1))
                  (b14 (nth 14 s1))
                  (b15 (nth 15 s1))
                  (k0 k0)
                  (k1 k1)
                  (k2 k2)
                  (k3 k3)
                  (k4 k4)
                  (k5 k5)
                  (k6 k6)
                  (k7 k7)))))

;; inv_bitslice always yields two 16-byte blocks -- needed to discharge the
;; commute's inp hypothesis on the unpacked key.
(gl::def-gl-thm inp-of-inv-bitslice-blocks
  :hyp (and (unsigned-byte-p 32 k0) (unsigned-byte-p 32 k1) (unsigned-byte-p 32 k2) (unsigned-byte-p 32 k3) (unsigned-byte-p 32 k4) (unsigned-byte-p 32 k5) (unsigned-byte-p 32 k6) (unsigned-byte-p 32 k7))
  :concl
  (b* ((ik (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list k0 k1 k2 k3 k4 k5 k6 k7)))))
    (and (aes::inp (car ik)) (aes::inp (cadr ik))))
  :g-bindings (gl::auto-bindings (:nat k0 32) (:nat k1 32) (:nat k2 32) (:nat k3 32) (:nat k4 32) (:nat k5 32) (:nat k6 32) (:nat k7 32)))

;; Phase-3 result: fixslice AddRoundKey, through phi, is Kestrel's addroundkey
;; of the state and the (unpacked, columnized) round key.
(defthm addroundkey-correspondence
  (implies (and (aes::inp s0) (aes::inp s1) (unsigned-byte-p 32 k0) (unsigned-byte-p 32 k1) (unsigned-byte-p 32 k2) (unsigned-byte-p 32 k3) (unsigned-byte-p 32 k4) (unsigned-byte-p 32 k5) (unsigned-byte-p 32 k6) (unsigned-byte-p 32 k7))
           (equal (fixslice->statep
                    (result-ok->val (aes-fixslice-encrypt-add-round-key 100
                      (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) s0 s1)) (list k0 k1 k2 k3 k4 k5 k6 k7)))
                    0)
                  (aes::addroundkey
                    (aes::copyarraytostate s0)
                    (bytes->cols (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list k0 k1 k2 k3 k4 k5 k6 k7))))))))
  :hints (("Goal"
           :in-theory (e/d (fixslice->statep fixslice->block)
                           (aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-add-round-key
                            aes-fixslice-encrypt-inv-bitslice aes::copyarraytostate
                            aes::addroundkey bytes->cols xorbytes))
           :use ((:instance addroundkey-of-copyarraytostate
                  (a s0)
                  (b (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list k0 k1 k2 k3 k4 k5 k6 k7)))))))))) 
