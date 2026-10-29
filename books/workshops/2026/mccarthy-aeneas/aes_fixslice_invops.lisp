; Phase 6 -- DECRYPT SIDE, part 1: inverse ops through the packing (GL) and
; their length-only shape facts.  The inv_mix_columns_1/2/3 bit-blasts live
; in aes_fixslice_invops2/3: the InvMixColumns coefficients (9/11/13/14)
; make those BDDs heavy enough to need their own sessions on small machines.
(in-package "ACL2")
(include-book "aes_fixslice_round")  ; expand-len-8 + the forward per-op chain
(include-book "aes_fixslice_invops_defs")

;; ---- inv-sub-bytes: GL + lift ----
(gl::def-gl-thm inv-sub-bytes-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (map-invsbox16 blk0) (map-invsbox16 blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

(defthm inv-sub-bytes-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (map-invsbox16 b0) (map-invsbox16 b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-sub-bytes-gl aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice aes::inp map-invsbox16 nth))
           :use (:instance inv-sub-bytes-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

(value-triple (hons-clear t))  ; release BDD memory between blasts

;; ror wraps u32-rotate-right, whose body is (ok <arith>): :ok unconditionally.
(local (defthm rk-of-ror
  (equal (result-kind (aes-fixslice-encrypt-ror x y)) :ok)
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-ror u32-rotate-right)))))

;; ---- inv-mix-columns-0: GL + lift ----
(gl::def-gl-thm inv-mix-columns-0-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl
  (let ((blk0 (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)) (blk1 (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))
    (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) blk0 blk1))))))
           (list (imc0-bytes blk0) (imc0-bytes blk1))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

(defthm inv-mix-columns-0-general
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
                  (list (imc0-bytes b0) (imc0-bytes b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (inv-mix-columns-0-gl aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice aes::inp imc0-bytes nth))
           :use (:instance inv-mix-columns-0-gl (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0)) (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

;; ---- shape facts (:ok / len / true-listp), all five ops ----
(local (defthm rk-inv-sub-bytes-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-sub-bytes) (u32-xor u32-and u32-or u32-shl u32-shr))))))

(defthm rk-of-inv-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-sub-bytes nth)
           :use ((:instance rk-inv-sub-bytes-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm len-inv-sub-bytes-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-sub-bytes) (u32-xor u32-and u32-or u32-shl u32-shr))))))

(defthm len-of-inv-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-sub-bytes nth)
           :use ((:instance len-inv-sub-bytes-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm tl-inv-sub-bytes-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-sub-bytes) (u32-xor u32-and u32-or u32-shl u32-shr))))))

(defthm tl-of-inv-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-sub-bytes nth)
           :use ((:instance tl-inv-sub-bytes-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-inv-mix-columns-0-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm rk-of-inv-mix-columns-0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-0 nth)
           :use ((:instance rk-inv-mix-columns-0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm len-inv-mix-columns-0-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm len-of-inv-mix-columns-0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-0 nth)
           :use ((:instance len-inv-mix-columns-0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm tl-inv-mix-columns-0-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-0) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm tl-of-inv-mix-columns-0-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-0 nth)
           :use ((:instance tl-inv-mix-columns-0-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-inv-mix-columns-1-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm rk-of-inv-mix-columns-1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-1 nth)
           :use ((:instance rk-inv-mix-columns-1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm len-inv-mix-columns-1-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm len-of-inv-mix-columns-1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-1 nth)
           :use ((:instance len-inv-mix-columns-1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm tl-inv-mix-columns-1-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-1) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm tl-of-inv-mix-columns-1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-1 nth)
           :use ((:instance tl-inv-mix-columns-1-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-inv-mix-columns-2-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm rk-of-inv-mix-columns-2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-2 nth)
           :use ((:instance rk-inv-mix-columns-2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm len-inv-mix-columns-2-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm len-of-inv-mix-columns-2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-2 nth)
           :use ((:instance len-inv-mix-columns-2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm tl-inv-mix-columns-2-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-2) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm tl-of-inv-mix-columns-2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-2 nth)
           :use ((:instance tl-inv-mix-columns-2-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm rk-inv-mix-columns-3-explicit
  (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm rk-of-inv-mix-columns-3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-3 nth)
           :use ((:instance rk-inv-mix-columns-3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm len-inv-mix-columns-3-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm len-of-inv-mix-columns-3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-3 nth)
           :use ((:instance len-inv-mix-columns-3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm tl-inv-mix-columns-3-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-mix-columns-3) (u32-xor u32-and u32-or aes-fixslice-encrypt-ror u32-rotate-right))))))

(defthm tl-of-inv-mix-columns-3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-mix-columns-3 nth)
           :use ((:instance tl-inv-mix-columns-3-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))
