; Phase 4 -- compositional rewriting toward encrypt == AES::aes-128-encrypt.
;
; Strategy: structured rewriting. Push inv_bitslice inward through the round ops
; with rules `inv_bitslice(op(S)) = op'(inv_bitslice(S))`, collapsing the cipher
; to byte-level Kestrel ops on inv_bitslice(bitslice pt) = pt. This file builds
; the foundation: a fixslice-state predicate, the two-way bijection generalised
; to it, and the per-op push-in rules -- derived by REWRITING from the Phase-3
; per-op lemmas + the bijection (the one irreducible bit-blast is the fact
; bitslice o inv_bitslice = id).
(in-package "ACL2")
(include-book "aes_fixslice_subbytes")
(include-book "aes_fixslice_mixcolumns")
(include-book "aes_fixslice_addroundkey")

(defthmd expand-len-8
  (implies (and (true-listp x) (equal (len x) 8))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)
                        (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x)) x))
  :hints (("Goal" :in-theory (enable nth)
           :expand ((len x) (len (cdr x)) (len (cdr (cdr x))) (len (cdr (cdr (cdr x))))
                    (len (cdr (cdr (cdr (cdr x))))) (len (cdr (cdr (cdr (cdr (cdr x))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
                    (len (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))))))

;; A well-formed fixslice State: 8 u32 words.
(defund wstatep (s)
  (and (true-listp s) (equal (len s) 8) (unsigned-byte-p 32 (nth 0 s)) (unsigned-byte-p 32 (nth 1 s)) (unsigned-byte-p 32 (nth 2 s)) (unsigned-byte-p 32 (nth 3 s)) (unsigned-byte-p 32 (nth 4 s)) (unsigned-byte-p 32 (nth 5 s)) (unsigned-byte-p 32 (nth 6 s)) (unsigned-byte-p 32 (nth 7 s))))

;; The bit-level fact (GL): bitslice o inv_bitslice = id, explicit words.
(gl::def-gl-thm bitslice-of-inv-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl
  (b* ((s (list w0 w1 w2 w3 w4 w5 w6 w7)) (ib (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
    (equal (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (car ib) (cadr ib))) s))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))

;; ...generalised to any wstatep by the expand-len-8 bridge.
(defthm bitslice-of-inv-bitslice
  (implies (wstatep s)
           (equal (result-ok->val
                    (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                      (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))
                      (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))
                  s))
  :hints (("Goal"
           :in-theory (e/d (expand-len-8 wstatep)
                           (bitslice-of-inv-gl aes-fixslice-encrypt-bitslice
                            aes-fixslice-encrypt-inv-bitslice nth))
           :use (:instance bitslice-of-inv-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

;; inv_bitslice blocks are 16-byte (inp), generalised to any wstatep.
(defthm inp-of-inv-blocks-general
  (implies (wstatep s)
           (and (aes::inp (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                (aes::inp (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-8 wstatep)
                           (inp-of-inv-bitslice-blocks aes-fixslice-encrypt-inv-bitslice nth))
           :use (:instance inp-of-inv-bitslice-blocks (k0 (nth 0 s)) (k1 (nth 1 s)) (k2 (nth 2 s)) (k3 (nth 3 s)) (k4 (nth 4 s)) (k5 (nth 5 s)) (k6 (nth 6 s)) (k7 (nth 7 s))))))

;; ---------------------------------------------------------------------------
;; PUSH-IN RULES (structured rewriting). Each rewrites inv_bitslice(op(S)) into
;; the byte-level Kestrel op applied to inv_bitslice(S), for an arbitrary state.
;; Derived from the Phase-3 general lemmas by instantiating their fresh-block
;; inputs at inv_bitslice(S) and folding bitslice(inv_bitslice S) = S.

;; SubBytes: inv_bitslice(sub_bytes_nots(sub_bytes(S))) = map-sbox on each lane.
(defthm inv-bitslice-of-subbytes
  (implies (wstatep s)
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val
                        (aes-fixslice-encrypt-sub-bytes-nots
                          (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))))
                  (list (map-sbox16 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (map-sbox16 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (subbytes-through-packing-general
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice
                            aes::inp map-sbox16 nth))
           :use (:instance subbytes-through-packing-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; MixColumns (phase 0).
(defthm inv-bitslice-of-mixcolumns0
  (implies (wstatep s)
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
                  (list (kmix-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                        (kmix-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice)
                           (mix-columns-0-through-packing-general
                            aes-fixslice-encrypt-mix-columns-0
                            aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice
                            aes::inp kmix-bytes nth))
           :use (:instance mix-columns-0-through-packing-general
                  (b0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (b1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))))))

;; AddRoundKey: XOR the state lanes with the key lanes (K any state).
(defthm inv-bitslice-of-addroundkey
  (implies (and (wstatep s) (wstatep k))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-add-round-key 100 s k))))
                  (list (xorbytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))) (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice k))))
                        (xorbytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))) (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice k)))))))
  :hints (("Goal"
           :in-theory (e/d (bitslice-of-inv-bitslice expand-len-8 wstatep)
                           (add-round-key-through-packing-general
                            aes-fixslice-encrypt-add-round-key
                            aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-bitslice
                            aes::inp xorbytes nth))
           :use (:instance add-round-key-through-packing-general
                  (s0 (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s)))) (s1 (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                  (k0 (nth 0 k)) (k1 (nth 1 k)) (k2 (nth 2 k)) (k3 (nth 3 k)) (k4 (nth 4 k)) (k5 (nth 5 k)) (k6 (nth 6 k)) (k7 (nth 7 k))))))

;; ---------------------------------------------------------------------------
;; wstatep is preserved by each op (type facts; GL, then expand-len-8 to any
;; wstatep) -- lets the push-in rules chain across a round.
(gl::def-gl-thm wstatep-of-subbytes-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
           (result-ok->val (aes-fixslice-encrypt-sub-bytes (list w0 w1 w2 w3 w4 w5 w6 w7))))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-subbytes
  (implies (wstatep s)
           (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
                      (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-subbytes-gl aes-fixslice-encrypt-sub-bytes
                                   aes-fixslice-encrypt-sub-bytes-nots nth))
           :use (:instance wstatep-of-subbytes-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(gl::def-gl-thm wstatep-of-mixcolumns0-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-0 (list w0 w1 w2 w3 w4 w5 w6 w7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm wstatep-of-mixcolumns0
  (implies (wstatep s)
           (wstatep (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-mixcolumns0-gl aes-fixslice-encrypt-mix-columns-0 nth))
           :use (:instance wstatep-of-mixcolumns0-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(gl::def-gl-thm wstatep-of-addroundkey-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3) (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7) (unsigned-byte-p 32 v0) (unsigned-byte-p 32 v1) (unsigned-byte-p 32 v2) (unsigned-byte-p 32 v3) (unsigned-byte-p 32 v4) (unsigned-byte-p 32 v5) (unsigned-byte-p 32 v6) (unsigned-byte-p 32 v7))
  :concl (wstatep (result-ok->val (aes-fixslice-encrypt-add-round-key 100 (list w0 w1 w2 w3 w4 w5 w6 w7) (list v0 v1 v2 v3 v4 v5 v6 v7))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32) (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32) (:nat v0 32) (:nat v1 32) (:nat v2 32) (:nat v3 32) (:nat v4 32) (:nat v5 32) (:nat v6 32) (:nat v7 32)))
(defthm wstatep-of-addroundkey
  (implies (and (wstatep s) (wstatep k))
           (wstatep (result-ok->val (aes-fixslice-encrypt-add-round-key 100 s k))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (wstatep-of-addroundkey-gl aes-fixslice-encrypt-add-round-key nth))
           :use (:instance wstatep-of-addroundkey-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s)) (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s)) (v0 (nth 0 k)) (v1 (nth 1 k)) (v2 (nth 2 k)) (v3 (nth 3 k)) (v4 (nth 4 k)) (v5 (nth 5 k)) (v6 (nth 6 k)) (v7 (nth 7 k))))))

;; ---------------------------------------------------------------------------
;; Demonstration that the push-in rules CHAIN by rewriting alone: a two-op
;; fragment (MixColumns then AddRoundKey) collapses to byte-level Kestrel ops
;; on inv_bitslice(S) with no :use hints -- pure rewriting.
(defthm compose-demo-mixcolumns-then-addroundkey
  (implies (and (wstatep s) (wstatep k))
           (equal (result-ok->val
                    (aes-fixslice-encrypt-inv-bitslice
                      (result-ok->val (aes-fixslice-encrypt-add-round-key 100
                        (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s)) k))))
                  (list (xorbytes (kmix-bytes (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                                  (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice k))))
                        (xorbytes (kmix-bytes (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
                                  (cadr (result-ok->val (aes-fixslice-encrypt-inv-bitslice k)))))))
  ;; Keep the extracted ops closed so the push-in REWRITE rules fire (they are
  ;; the whole point); the chain then runs by rewriting alone.
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes
                                      aes-fixslice-encrypt-sub-bytes-nots
                                      aes-fixslice-encrypt-mix-columns-0
                                      aes-fixslice-encrypt-add-round-key
                                      aes-fixslice-encrypt-inv-bitslice
                                      aes-fixslice-encrypt-bitslice
                                      kmix-bytes xorbytes))))
