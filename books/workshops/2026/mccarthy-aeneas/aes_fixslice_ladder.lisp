; Phase 5 -- cipher side, part 7: THE ROUND LADDER.
;
; The invariant: after round r the un-bitsliced fixslice state is the spec
; state in the invshiftrows^{r mod 4} frame,
;
;   inv_bitslice(s_r)[0] = isr^{r mod 4}( y_r ),
;
; where s_r is the extracted chain state (schedule windows and all) and y_r
; is the byte-level spec recurrence y_r = kmix(sr1(sbox16(y_{r-1}))) + kk_r.
; Each step is pure rewriting: the cipherops push-ins turn the extracted ops
; into byte ops, the windows book supplies the round key (with its xor63 /
; invshiftrows^c fold), and the maskalg facts cancel the mask against the
; key's and telescope the frame (mix_columns_{r mod 4} in frame r-1 emits
; exactly one ShiftRows).  The last round's shift_rows_2 lands the state
; back in frame 0, so lane 0 of the output is y_final on the nose.
;
; End of book: the extracted encrypt_block on the extracted schedule IS
; (ok (y-final key block)).  The companion book aes_fixslice_final hops
; y-final onto aes::aes-128-encrypt.
(in-package "ACL2")
(include-book "aes_fixslice_windows")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))
;; the maskalg xor-distribution rules run the other way here (we PULL the
;; frame out of the xor); keep them off globally and use local pull rules.
(local (in-theory (disable isr1-of-xorbytes isr2-of-xorbytes isr3-of-xorbytes)))
;; keep the schedule and encrypt collapses from firing ambiently: the ladder
;; matches on the un-decomposed schedule call and the window corollaries.
(local (in-theory (disable ks-decomp enc-collapse
                           window-bitslice-0 window-bitslice-1 window-bitslice-2
                           window-bitslice-3 window-bitslice-4 window-bitslice-5
                           window-bitslice-6 window-bitslice-7 window-bitslice-8
                           window-bitslice-9 window-bitslice-10)))

;; ---------------------------------------------------------------------------
;; the schedule value is a well-formed 88-word array.  (Pinned composition of
;; the keydecomp/keyasm shape facts through ks-fold2's op nest.)
(local (defthm tl-of-sbn-chain
  (implies (and (true-listp rk) (equal (len rk) 88) (natp i) (<= 1 i) (equal off (* 8 i)))
           (true-listp (sbn-chain rk off i)))
  :hints (("Goal" :induct (sbn-chain rk off i)
           :in-theory (e/d (sbn-chain mul-8-distrib mul-8-le-80)
                           (aes-fixslice-encrypt-sub-bytes-nots w8-spec rd8 nth))))))
(defthm len-of-schedule-val
  (implies (aes::inp key) (equal (len (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key))) 88))
  :hints (("Goal" :do-not-induct t
           :use (ks-decomp)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-isr-step) (:rewrite true-listp-of-isr-step-88)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite len-of-sbn-chain) (:rewrite tl-of-sbn-chain)
                          (:rewrite result-ok->val-of-result-ok) (:rewrite rk-of-ok2)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart nfix)
                          (:executable-counterpart zp) (:executable-counterpart unary--))))))
(defthm true-listp-of-schedule-val
  (implies (aes::inp key) (true-listp (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key))))
  :hints (("Goal" :do-not-induct t
           :use (ks-decomp)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-isr-step) (:rewrite true-listp-of-isr-step-88)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite len-of-sbn-chain) (:rewrite tl-of-sbn-chain)
                          (:rewrite result-ok->val-of-result-ok) (:rewrite rk-of-ok2)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart nfix)
                          (:executable-counterpart zp) (:executable-counterpart unary--))))))

;; local pull rules (reverse of the maskalg distribution).
(local (defthm xorbytes-isr1-pull
  (equal (xorbytes (inv-shift-rows-1-bytes x) (inv-shift-rows-1-bytes y))
         (inv-shift-rows-1-bytes (xorbytes x y)))
  :hints (("Goal" :use isr1-of-xorbytes))))
(local (defthm xorbytes-isr2-pull
  (equal (xorbytes (inv-shift-rows-2-bytes x) (inv-shift-rows-2-bytes y))
         (inv-shift-rows-2-bytes (xorbytes x y)))
  :hints (("Goal" :use isr2-of-xorbytes))))
(local (defthm xorbytes-isr3-pull
  (equal (xorbytes (inv-shift-rows-3-bytes x) (inv-shift-rows-3-bytes y))
         (inv-shift-rows-3-bytes (xorbytes x y)))
  :hints (("Goal" :use isr3-of-xorbytes))))

;; ---------------------------------------------------------------------------
;; the two chains.
(defun mcv (c s)
  (cond ((equal c 1) (result-ok->val (aes-fixslice-encrypt-mix-columns-1 s)))
        ((equal c 2) (result-ok->val (aes-fixslice-encrypt-mix-columns-2 s)))
        ((equal c 3) (result-ok->val (aes-fixslice-encrypt-mix-columns-3 s)))
        (t (result-ok->val (aes-fixslice-encrypt-mix-columns-0 s)))))
(defund s-chain (key b r)
  (if (zp r)
      (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)) (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0)
    (arkw-spec 0 8 (mcv (mod r 4) (result-ok->val (aes-fixslice-encrypt-sub-bytes (s-chain key b (1- r)))))
               (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) (* 8 r))))
(defund s-final (key b)
  (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-sub-bytes (result-ok->val (aes-fixslice-encrypt-shift-rows-2 100 (s-chain key b 9)))))
             (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80))
(defund y-chain (key b r)
  (if (zp r) (xorbytes b (kk-iter key 0))
    (xorbytes (kmix-bytes (sr1-bytes (map-sbox16 (y-chain key b (1- r)))))
              (kk-iter key r))))
(defund y-final (key b)
  (xorbytes (sr1-bytes (map-sbox16 (y-chain key b 9))) (kk-iter key 10)))

(defthm inp-of-y-chain
  (implies (and (aes::inp key) (aes::inp b) (natp r) (<= r 10))
           (aes::inp (y-chain key b r)))
  :hints (("Goal" :induct (y-chain key b r)
           :in-theory (e/d (y-chain) (xorbytes kmix-bytes sr1-bytes map-sbox16
                                      kk-iter aes::inp nth)))))
(defthm inp-of-y-final
  (implies (and (aes::inp key) (aes::inp b)) (aes::inp (y-final key b)))
  :hints (("Goal" :in-theory (e/d (y-final) (xorbytes kmix-bytes sr1-bytes map-sbox16
                                             kk-iter aes::inp nth)))))
(defthm wstatep-s-chain-0
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 0)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 0))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-0 wstatep-of-bitslice)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-0
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 0))))
                  (y-chain key b 0)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 0) (y-chain key b 0))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-0 wstatep-window-0 wstatep-of-bitslice inv-bitslice-of-bitslice-general xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-1
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 1)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 1))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-1 wstatep-s-chain-0 wstatep-of-bare-subbytes wstatep-of-mixcolumns1)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-1
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 1))))
                  (inv-shift-rows-1-bytes (y-chain key b 1))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 1) (y-chain key b 1))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-1 wstatep-window-1 wstatep-s-chain-0 wstatep-of-bare-subbytes wstatep-of-mixcolumns1 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns1 ladder-0 mc1-of-sbn frame-mc1 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-2
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 2)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 2))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-2 wstatep-s-chain-1 wstatep-of-bare-subbytes wstatep-of-mixcolumns2)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-2
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 2))))
                  (inv-shift-rows-2-bytes (y-chain key b 2))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 2) (y-chain key b 2))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-2 wstatep-window-2 wstatep-s-chain-1 wstatep-of-bare-subbytes wstatep-of-mixcolumns2 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns2 ladder-1 sbox16-of-isr1 mc2-of-sbn frame-mc2 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-3
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 3)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 3))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-3 wstatep-s-chain-2 wstatep-of-bare-subbytes wstatep-of-mixcolumns3)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-3
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 3))))
                  (inv-shift-rows-3-bytes (y-chain key b 3))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 3) (y-chain key b 3))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-3 wstatep-window-3 wstatep-s-chain-2 wstatep-of-bare-subbytes wstatep-of-mixcolumns3 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns3 ladder-2 sbox16-of-isr2 mc3-of-sbn frame-mc3 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-4
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 4)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 4))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-4 wstatep-s-chain-3 wstatep-of-bare-subbytes wstatep-of-mixcolumns0)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-4
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 4))))
                  (y-chain key b 4)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 4) (y-chain key b 4))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-4 wstatep-window-4 wstatep-s-chain-3 wstatep-of-bare-subbytes wstatep-of-mixcolumns0 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns0 ladder-3 sbox16-of-isr3 mc0-of-sbn frame-mc0 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-5
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 5)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 5))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-5 wstatep-s-chain-4 wstatep-of-bare-subbytes wstatep-of-mixcolumns1)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-5
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 5))))
                  (inv-shift-rows-1-bytes (y-chain key b 5))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 5) (y-chain key b 5))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-5 wstatep-window-5 wstatep-s-chain-4 wstatep-of-bare-subbytes wstatep-of-mixcolumns1 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns1 ladder-4 mc1-of-sbn frame-mc1 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-6
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 6)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 6))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-6 wstatep-s-chain-5 wstatep-of-bare-subbytes wstatep-of-mixcolumns2)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-6
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 6))))
                  (inv-shift-rows-2-bytes (y-chain key b 6))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 6) (y-chain key b 6))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-6 wstatep-window-6 wstatep-s-chain-5 wstatep-of-bare-subbytes wstatep-of-mixcolumns2 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns2 ladder-5 sbox16-of-isr1 mc2-of-sbn frame-mc2 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-7
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 7)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 7))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-7 wstatep-s-chain-6 wstatep-of-bare-subbytes wstatep-of-mixcolumns3)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-7
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 7))))
                  (inv-shift-rows-3-bytes (y-chain key b 7))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 7) (y-chain key b 7))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-7 wstatep-window-7 wstatep-s-chain-6 wstatep-of-bare-subbytes wstatep-of-mixcolumns3 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns3 ladder-6 sbox16-of-isr2 mc3-of-sbn frame-mc3 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-8
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 8)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 8))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-8 wstatep-s-chain-7 wstatep-of-bare-subbytes wstatep-of-mixcolumns0)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-8
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 8))))
                  (y-chain key b 8)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 8) (y-chain key b 8))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-8 wstatep-window-8 wstatep-s-chain-7 wstatep-of-bare-subbytes wstatep-of-mixcolumns0 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns0 ladder-7 sbox16-of-isr3 mc0-of-sbn frame-mc0 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-chain-9
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-chain key b 9)))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 9))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-9 wstatep-s-chain-8 wstatep-of-bare-subbytes wstatep-of-mixcolumns1)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-9
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-chain key b 9))))
                  (inv-shift-rows-1-bytes (y-chain key b 9))))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 9) (y-chain key b 9))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-9 wstatep-window-9 wstatep-s-chain-8 wstatep-of-bare-subbytes wstatep-of-mixcolumns1 inv-bitslice-of-bare-subbytes inv-bitslice-of-mixcolumns1 ladder-8 mc1-of-sbn frame-mc1 xorbytes-sbn-cancel) (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm wstatep-s-final
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (s-final key b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (s-final wstatep-of-arkw-window wstatep-window-10
                            wstatep-s-chain-9 wstatep-of-bare-subbytes wstatep-of-sr2)
                           (s-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
(defthm ladder-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (s-final key b))))
                  (y-final key b)))
  :hints (("Goal" :do-not-induct t
           :expand ((y-final key b))
           :in-theory (e/d (s-final y-final
                            inv-bitslice-of-arkw-window ib-window-10 wstatep-window-10
                            wstatep-s-chain-9 wstatep-of-bare-subbytes wstatep-of-sr2
                            inv-bitslice-of-bare-subbytes inv-bitslice-of-sr2 ladder-9
                            frame-sr2-isr1 sbox16-of-sr1 xorbytes-sbn-cancel)
                           (s-chain y-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))
;; ---------------------------------------------------------------------------
;; the extracted chain IS the ladder chain (pure structure).
(defthm enc-chain-is-s-final
  (equal (enc-chain (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key))
                    (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))
         (s-final key b))
  :hints (("Goal" :do-not-induct t
           :expand ((s-chain key b 9) (s-chain key b 8) (s-chain key b 7)
                    (s-chain key b 6) (s-chain key b 5) (s-chain key b 4)
                    (s-chain key b 3) (s-chain key b 2) (s-chain key b 1)
                    (s-chain key b 0))
           :in-theory (e/d (enc-chain s-final)
                           (s-chain arkw-spec arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3)))))

;; inv_bitslice yields a 2-list (explicit-8, as in the cipher book).
(local (include-book "kestrel/bv/logand" :dir :system))
(local (defthm rk-of-ds2
  (implies (< (nfix shift) 32)
           (equal (result-kind (aes-fixslice-encrypt-delta-swap-2 a b shift mask)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-2)))))
(local (defthm rk-of-u32-shr-lt
  (implies (< (nfix n) 32)
           (equal (result-kind (u32-shr x n)) :ok))))
(local (defthm len-ib-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-inv-bitslice (list a0 a1 a2 a3 a4 a5 a6 a7)))) 2)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-inv-bitslice)
                                  (u32-xor u32-and u32-or u32-shl u32-shr
                                   aes-fixslice-encrypt-delta-swap-2
                                   vec-index-range vec-update-range
                                   slice-copy-from-slice u32-to-le-bytes
                                   take nthcdr append update-nth))))))
(defthm len-of-ib-val
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))) 2))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-inv-bitslice nth)
           :use ((:instance len-ib-explicit (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s)) (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s))) (:instance expand-len-8 (x s))))))

(local (defthm consp-of-ib-val
  (implies (and (true-listp s) (equal (len s) 8))
           (consp (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
  :hints (("Goal" :use len-of-ib-val
           :in-theory (e/d () (aes-fixslice-encrypt-inv-bitslice len-of-ib-val nth))))))

;; THE EXTRACTED ENCRYPT-BLOCK COMPUTES y-final.
(defthm encrypt-block-is-y-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes-fixslice-encrypt-encrypt-block 100
                    (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) b)
                  (ok (y-final key b))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (enc-collapse enc-chain-is-s-final
                            result-kind-of-inv-bitslice-len len-of-ib-val ladder-final)
                           (s-final enc-chain aes-fixslice-encrypt-aes128-encrypt arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes kk-iter aes::inp aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3))
           :use ((:instance len-when-wstatep (x (s-final key b)))
                 (:instance true-listp-when-wstatep (x (s-final key b)))
                 wstatep-s-final))))
