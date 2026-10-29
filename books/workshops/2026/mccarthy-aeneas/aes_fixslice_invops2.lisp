; Phase 6 -- DECRYPT SIDE, part 1b: inv_mix_columns_1/2 through the packing.
; Slim include on purpose: these conjugated-InvMixColumns BDD blasts are the
; heaviest in the development.
(in-package "ACL2")
(include-book "aes_fixslice_invops_defs")

(gl::def-gl-thm inv-mix-columns-1-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (imc1-bytes blk0) (imc1-bytes blk1))))
  :g-bindings (gl::auto-bindings (:mix (:nat a0 8) (:nat b0 8)) (:mix (:nat a5 8) (:nat b5 8)) (:mix (:nat a10 8) (:nat b10 8)) (:mix (:nat a15 8) (:nat b15 8)) (:mix (:nat a4 8) (:nat b4 8)) (:mix (:nat a9 8) (:nat b9 8)) (:mix (:nat a14 8) (:nat b14 8)) (:mix (:nat a3 8) (:nat b3 8)) (:mix (:nat a8 8) (:nat b8 8)) (:mix (:nat a13 8) (:nat b13 8)) (:mix (:nat a2 8) (:nat b2 8)) (:mix (:nat a7 8) (:nat b7 8)) (:mix (:nat a12 8) (:nat b12 8)) (:mix (:nat a1 8) (:nat b1 8)) (:mix (:nat a6 8) (:nat b6 8)) (:mix (:nat a11 8) (:nat b11 8))))

(defthm inv-mix-columns-1-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (imc1-bytes b0) (imc1-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-mix-columns-1-gl aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice aes::inp imc1-bytes nth))
           :use (:instance inv-mix-columns-1-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

(value-triple (hons-clear t))

(gl::def-gl-thm inv-mix-columns-2-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (imc2-bytes blk0) (imc2-bytes blk1))))
  :g-bindings (gl::auto-bindings (:mix (:nat a0 8) (:nat b0 8)) (:mix (:nat a9 8) (:nat b9 8)) (:mix (:nat a2 8) (:nat b2 8)) (:mix (:nat a11 8) (:nat b11 8)) (:mix (:nat a4 8) (:nat b4 8)) (:mix (:nat a13 8) (:nat b13 8)) (:mix (:nat a6 8) (:nat b6 8)) (:mix (:nat a15 8) (:nat b15 8)) (:mix (:nat a8 8) (:nat b8 8)) (:mix (:nat a1 8) (:nat b1 8)) (:mix (:nat a10 8) (:nat b10 8)) (:mix (:nat a3 8) (:nat b3 8)) (:mix (:nat a12 8) (:nat b12 8)) (:mix (:nat a5 8) (:nat b5 8)) (:mix (:nat a14 8) (:nat b14 8)) (:mix (:nat a7 8) (:nat b7 8))))

(defthm inv-mix-columns-2-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (imc2-bytes b0) (imc2-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-mix-columns-2-gl aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice aes::inp imc2-bytes nth))
           :use (:instance inv-mix-columns-2-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))
