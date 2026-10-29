; Phase 6 -- DECRYPT SIDE, part 2: the extracted aes128_decrypt collapses
; onto a clean value-chain model.
;
; Mirror of the encrypt collapse (aes_fixslice_cipher): the extracted body
; is bitslice ; ark@80 ; inv_sub_bytes ; inv_shift_rows_2 ;
; 9x[ark@(72..8 descending) ; inv_mix_columns_c ; inv_sub_bytes] ; ark@0 ;
; inv_bitslice.  The upstream decrypt loop (bare loop{...break}, counter
; rk_off DESCENDING 72 -> 8) contributes the nine middle rounds via
; dec-loop-collapse: three explicit expansions of the loop body (fuel 100
; at rk_off 72, 99 at 40, 98 at 8 -- the break fires after the first
; quarter of the third body).  The ark windows and shape machinery are the
; encrypt side's own exports (arkw-spec, ark-of-window-*, st8p); the
; inverse ops' shape facts come from aes_fixslice_invops.
(in-package "ACL2")
(include-book "aes_fixslice_cipher")
(include-book "aes_fixslice_invops")

;; ---------------------------------------------------------------------------
;; st8p closure rules for the inverse ops (one rule per op per fact, so the
;; 33-op collapse relieves hypotheses linearly -- same discipline as the
;; forward side).
(defthm st8p-of-isb
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-sub-bytes)))))
(defthm rk-of-isb-st
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-sub-bytes)))))
(defthm st8p-of-imc0
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-0)))))
(defthm rk-of-imc0-st
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-0 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-0)))))
(defthm st8p-of-imc1
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-1)))))
(defthm rk-of-imc1-st
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-1 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-1)))))
(defthm st8p-of-imc2
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-2)))))
(defthm rk-of-imc2-st
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-2 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-2)))))
(defthm st8p-of-imc3
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s))))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm rk-of-imc3-st
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-mix-columns-3 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p) (aes-fixslice-encrypt-inv-mix-columns-3)))))
;; inv_shift_rows_2 at the wrapper's literal fuel 100 (the prelude call).
(defthm st8p-of-isr2-100
  (implies (st8p s)
           (st8p (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
  :hints (("Goal" :in-theory (e/d (st8p)
                                  (aes-fixslice-encrypt-inv-shift-rows-2)))))
(defthm rk-of-isr2-st-100
  (implies (st8p s)
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :in-theory (e/d (st8p)
                                  (aes-fixslice-encrypt-inv-shift-rows-2)))))

;; ---------------------------------------------------------------------------
;; the decrypt value chain (bitslice and inv_bitslice stay outside).
;; Middle-round pattern: s := isb(imc_c(arkw(s, off))) at
;; (72,c=1) (64,0) (56,3) (48,2) (40,1) (32,0) (24,3) (16,2) (8,1).
(defund dec-chain (rk s)
  (b* ((s (arkw-spec 0 8 s rk 80))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes s)))
       (s (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s)))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 72))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (arkw-spec 0 8 s rk 64))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (arkw-spec 0 8 s rk 56))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (arkw-spec 0 8 s rk 48))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 40))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (arkw-spec 0 8 s rk 32))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (arkw-spec 0 8 s rk 24))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (arkw-spec 0 8 s rk 16))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 8))))))
       (s (arkw-spec 0 8 s rk 0)))
    s))

;; ---------------------------------------------------------------------------
;; the restored upstream decrypt loop at fuel 100, rk_off 72, IS the nine
;; middle rounds.  Same pinned-theory discipline as enc-loop-collapse.
(defthm dec-loop-collapse
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88))
           (equal (aes-fixslice-encrypt-aes128-decrypt-loop0 100 rk s 72)
                  (ok (b* (
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 72))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (arkw-spec 0 8 s rk 64))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (arkw-spec 0 8 s rk 56))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (arkw-spec 0 8 s rk 48))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 40))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 (arkw-spec 0 8 s rk 32))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 (arkw-spec 0 8 s rk 24))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 (arkw-spec 0 8 s rk 16))))))
       (s (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 (arkw-spec 0 8 s rk 8)))))))
                        s))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (sv) (aes-fixslice-encrypt-aes128-decrypt-loop0 100 rk sv 72))
                    (:free (sv) (aes-fixslice-encrypt-aes128-decrypt-loop0 99 rk sv 40))
                    (:free (sv) (aes-fixslice-encrypt-aes128-decrypt-loop0 98 rk sv 8)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite st8p-of-arkw-spec) (:rewrite st8p-of-isb)
                          (:rewrite st8p-of-imc0) (:rewrite st8p-of-imc1)
                          (:rewrite st8p-of-imc2) (:rewrite st8p-of-imc3)
                          (:rewrite rk-of-isb-st)
                          (:rewrite rk-of-imc0-st) (:rewrite rk-of-imc1-st)
                          (:rewrite rk-of-imc2-st) (:rewrite rk-of-imc3-st)
                          (:rewrite ark-of-window-range) (:rewrite rk-of-window-range)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart usize-add)
                          (:executable-counterpart usize-sub)
                          (:executable-counterpart result-kind$inline)
                          (:executable-counterpart result-ok->val$inline)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm dec-collapse
  (implies (and (aes::inp b0) (aes::inp b1)
                (true-listp rk) (equal (len rk) 88))
           (equal (aes-fixslice-encrypt-aes128-decrypt 100 rk b0 b1)
                  (aes-fixslice-encrypt-inv-bitslice
                    (dec-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-decrypt)
                          (:definition dec-chain)
                          (:definition not)
                          (:rewrite bitslice-ok) (:rewrite st8p-of-bitslice)
                          (:executable-counterpart array-repeat)
                          (:rewrite st8p-of-arkw-spec) (:rewrite st8p-of-isb)
                          (:rewrite st8p-of-imc0) (:rewrite st8p-of-imc1)
                          (:rewrite st8p-of-imc2) (:rewrite st8p-of-imc3)
                          (:rewrite st8p-of-isr2-100)
                          (:rewrite rk-of-isb-st)
                          (:rewrite rk-of-imc0-st) (:rewrite rk-of-imc1-st)
                          (:rewrite rk-of-imc2-st) (:rewrite rk-of-imc3-st)
                          (:rewrite rk-of-isr2-st-100)
                          (:rewrite ark-of-window-to) (:rewrite rk-of-window-to)
                          (:rewrite ark-of-window-from80) (:rewrite rk-of-window-from80)
                          (:rewrite dec-loop-collapse)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq))))))

(defthm st8p-of-dec-chain
  (implies (and (st8p s) (true-listp rk) (equal (len rk) 88))
           (st8p (dec-chain rk s)))
  :hints (("Goal" :in-theory (e/d (dec-chain)
                    (arkw-spec u32-xor nth st8p
                     aes-fixslice-encrypt-inv-sub-bytes
                     aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1
                     aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3
                     aes-fixslice-encrypt-inv-shift-rows-2)))))
(local (defthm st8p-open
  (implies (st8p s) (and (true-listp s) (equal (len s) 8)))
  :hints (("Goal" :in-theory (enable st8p)))))
(defthm result-kind-of-decrypt128
  (implies (and (aes::inp b0) (aes::inp b1) (true-listp rk) (equal (len rk) 88))
           (equal (result-kind (aes-fixslice-encrypt-aes128-decrypt 100 rk b0 b1)) :ok))
  :hints (("Goal" :in-theory (e/d () (aes-fixslice-encrypt-aes128-decrypt
                                      aes-fixslice-encrypt-inv-bitslice dec-chain
                                      aes-fixslice-encrypt-bitslice st8p))
           :use (dec-collapse
                 (:instance st8p-of-dec-chain (s (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
                 (:instance st8p-open (s (dec-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))))
                 (:instance result-kind-of-inv-bitslice-len
                   (s (dec-chain rk (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))))))))
