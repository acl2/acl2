; Phase 6 -- DECRYPT SIDE, part 5: THE REVERSE ROUND LADDER.
;
; The invariant: after the prelude (k=0) and after each of the nine loop
; rounds (k=1..9), the un-bitsliced fixslice state is the byte-level spec
; recurrence in the invshiftrows^{(10-k) mod 4} frame,
;
;   inv_bitslice(dec_s_k)[0] = isr^{(10-k) mod 4}( invsbox16( z_k ) ),
;
; where z_k is the spec InvCipher read forward along the decrypt chain:
;   z_0 = b + kk_10,   z_k = InvMixColumns( invsbox16(isr(z_{k-1})) + kk_{10-k} ),
; and invsbox16 is the TRUE bytewise inverse S-box.  Discovered empirically
; (FIPS-197 vectors through both chains, matching each state against
; framed/masked spec stages), then proved by pure rewriting: the
; decipherops push-ins turn the extracted ops into byte ops, the windows
; book supplies each round key (with its xor63 / invshiftrows^c fold), and
; the decmask facts associate the mask out of the key xor, cancel it into
; the inverse S-box's input compensation, and telescope the frame (the
; conjugated InvMixColumns re-emits its own frame around the plain spec
; InvMixColumns -- dec-round-frame-N).  The final add_round_key uses the
; UNADJUSTED window 0 in frame 0, so lane 0 of the output is z-final on
; the nose.
;
; End of book: the extracted decrypt_block on the extracted schedule IS
; (ok (z-final key block)).  The companion book aes_fixslice_decfinal hops
; z-final onto aes::aes-128-decrypt.
(in-package "ACL2")
(include-book "aes_fixslice_ladder")
(include-book "aes_fixslice_decipherops")
(include-book "aes_fixslice_decmask")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))
(local (in-theory (disable isr1-of-xorbytes isr2-of-xorbytes isr3-of-xorbytes)))
(local (in-theory (disable frame-imc1-dec frame-imc2-dec frame-imc3-dec)))
(local (in-theory (disable ks-decomp enc-collapse dec-collapse
                           window-bitslice-0 window-bitslice-1 window-bitslice-2
                           window-bitslice-3 window-bitslice-4 window-bitslice-5
                           window-bitslice-6 window-bitslice-7 window-bitslice-8
                           window-bitslice-9 window-bitslice-10)))

;; the two chains.
(defun imcv (c s)
  (cond ((equal c 1) (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-1 s)))
        ((equal c 2) (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-2 s)))
        ((equal c 3) (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-3 s)))
        (t (result-ok->val (aes-fixslice-encrypt-inv-mix-columns-0 s)))))
(defund dec-s-chain (key b k)
  (if (zp k)
      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100
        (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes
          (arkw-spec 0 8 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b))
                     (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80)))))
    (result-ok->val (aes-fixslice-encrypt-inv-sub-bytes
      (imcv (mod (- 10 k) 4)
            (arkw-spec 0 8 (dec-s-chain key b (1- k))
                       (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) (* 8 (- 10 k))))))))
(defund dec-s-final (key b)
  (arkw-spec 0 8 (dec-s-chain key b 9)
             (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0))
(defund z-chain (key b k)
  (if (zp k) (xorbytes b (kk-iter key 10))
    (imc0-bytes (xorbytes (invsbox16 (inv-shift-rows-1-bytes (z-chain key b (1- k))))
                          (kk-iter key (- 10 k))))))
(defund z-final (key b)
  (xorbytes (invsbox16 (inv-shift-rows-1-bytes (z-chain key b 9))) (kk-iter key 0)))

(defthm inp-of-z-chain
  (implies (and (aes::inp key) (aes::inp b) (natp k) (<= k 9))
           (aes::inp (z-chain key b k)))
  :hints (("Goal" :induct (z-chain key b k)
           :in-theory (e/d (z-chain) (xorbytes imc0-bytes invsbox16 inv-shift-rows-1-bytes
                                      kk-iter aes::inp nth)))))
(defthm inp-of-z-final
  (implies (and (aes::inp key) (aes::inp b)) (aes::inp (z-final key b)))
  :hints (("Goal" :in-theory (e/d (z-final) (xorbytes imc0-bytes invsbox16 inv-shift-rows-1-bytes
                                             kk-iter aes::inp nth)))))

(defthm wstatep-dec-s-chain-0
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 0)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 0))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-10 wstatep-of-bitslice wstatep-of-isb wstatep-of-isr2-w)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-0
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 0))))
                  (inv-shift-rows-2-bytes (invsbox16 (z-chain key b 0)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 0) (z-chain key b 0))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-10 wstatep-window-10 wstatep-of-bitslice inv-bitslice-of-bitslice-general wstatep-of-isb wstatep-of-isr2-w inv-bitslice-of-isb inv-bitslice-of-isr2-w xorbytes-sbn-assoc misb-of-sbn sr2-is-isr2)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-1
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 1)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 1))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-9 wstatep-dec-s-chain-0 wstatep-of-isb wstatep-of-imc1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-1
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 1))))
                  (inv-shift-rows-1-bytes (invsbox16 (z-chain key b 1)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 1) (z-chain key b 1))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-9 wstatep-window-9 wstatep-dec-s-chain-0 wstatep-of-isb wstatep-of-imc1 inv-bitslice-of-isb inv-bitslice-of-imc1 dec-ladder-0 xorbytes-sbn-assoc imc1-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-2
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 2)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 2))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-8 wstatep-dec-s-chain-1 wstatep-of-isb wstatep-of-imc0)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-2
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 2))))
                  (invsbox16 (z-chain key b 2))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 2) (z-chain key b 2))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-8 wstatep-window-8 wstatep-dec-s-chain-1 wstatep-of-isb wstatep-of-imc0 inv-bitslice-of-isb inv-bitslice-of-imc0 dec-ladder-1 xorbytes-sbn-assoc imc0-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-3
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 3)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 3))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-7 wstatep-dec-s-chain-2 wstatep-of-isb wstatep-of-imc3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-3
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 3))))
                  (inv-shift-rows-3-bytes (invsbox16 (z-chain key b 3)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 3) (z-chain key b 3))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-7 wstatep-window-7 wstatep-dec-s-chain-2 wstatep-of-isb wstatep-of-imc3 inv-bitslice-of-isb inv-bitslice-of-imc3 dec-ladder-2 xorbytes-sbn-assoc imc3-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-4
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 4)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 4))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-6 wstatep-dec-s-chain-3 wstatep-of-isb wstatep-of-imc2)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-4
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 4))))
                  (inv-shift-rows-2-bytes (invsbox16 (z-chain key b 4)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 4) (z-chain key b 4))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-6 wstatep-window-6 wstatep-dec-s-chain-3 wstatep-of-isb wstatep-of-imc2 inv-bitslice-of-isb inv-bitslice-of-imc2 dec-ladder-3 xorbytes-sbn-assoc imc2-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-2)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-5
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 5)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 5))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-5 wstatep-dec-s-chain-4 wstatep-of-isb wstatep-of-imc1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-5
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 5))))
                  (inv-shift-rows-1-bytes (invsbox16 (z-chain key b 5)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 5) (z-chain key b 5))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-5 wstatep-window-5 wstatep-dec-s-chain-4 wstatep-of-isb wstatep-of-imc1 inv-bitslice-of-isb inv-bitslice-of-imc1 dec-ladder-4 xorbytes-sbn-assoc imc1-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-6
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 6)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 6))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-4 wstatep-dec-s-chain-5 wstatep-of-isb wstatep-of-imc0)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-6
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 6))))
                  (invsbox16 (z-chain key b 6))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 6) (z-chain key b 6))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-4 wstatep-window-4 wstatep-dec-s-chain-5 wstatep-of-isb wstatep-of-imc0 inv-bitslice-of-isb inv-bitslice-of-imc0 dec-ladder-5 xorbytes-sbn-assoc imc0-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-7
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 7)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 7))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-3 wstatep-dec-s-chain-6 wstatep-of-isb wstatep-of-imc3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-7
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 7))))
                  (inv-shift-rows-3-bytes (invsbox16 (z-chain key b 7)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 7) (z-chain key b 7))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-3 wstatep-window-3 wstatep-dec-s-chain-6 wstatep-of-isb wstatep-of-imc3 inv-bitslice-of-isb inv-bitslice-of-imc3 dec-ladder-6 xorbytes-sbn-assoc imc3-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-3)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-8
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 8)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 8))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-2 wstatep-dec-s-chain-7 wstatep-of-isb wstatep-of-imc2)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-8
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 8))))
                  (inv-shift-rows-2-bytes (invsbox16 (z-chain key b 8)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 8) (z-chain key b 8))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-2 wstatep-window-2 wstatep-dec-s-chain-7 wstatep-of-isb wstatep-of-imc2 inv-bitslice-of-isb inv-bitslice-of-imc2 dec-ladder-7 xorbytes-sbn-assoc imc2-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-2)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-chain-9
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-chain key b 9)))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 9))
           :in-theory (e/d (wstatep-of-arkw-window wstatep-window-1 wstatep-dec-s-chain-8 wstatep-of-isb wstatep-of-imc1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-9
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-chain key b 9))))
                  (inv-shift-rows-1-bytes (invsbox16 (z-chain key b 9)))))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 9) (z-chain key b 9))
           :in-theory (e/d (inv-bitslice-of-arkw-window ib-window-1 wstatep-window-1 wstatep-dec-s-chain-8 wstatep-of-isb wstatep-of-imc1 inv-bitslice-of-isb inv-bitslice-of-imc1 dec-ladder-8 xorbytes-sbn-assoc imc1-of-sbn misb-of-sbn invsbox16-of-isr1 invsbox16-of-isr2 invsbox16-of-isr3 dec-round-frame-1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm wstatep-dec-s-final
  (implies (and (aes::inp key) (aes::inp b)) (wstatep (dec-s-final key b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (dec-s-final wstatep-of-arkw-window wstatep-window-0 wstatep-dec-s-chain-9)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))
(defthm dec-ladder-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice (dec-s-final key b))))
                  (z-final key b)))
  :hints (("Goal" :do-not-induct t
           :expand ((z-final key b))
           :in-theory (e/d (dec-s-final z-final inv-bitslice-of-arkw-window ib-window-0 wstatep-window-0 wstatep-dec-s-chain-9 dec-ladder-9 invsbox16-of-isr1)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))

;; the extracted chain IS the ladder chain (pure structure).
(defthm dec-chain-is-dec-s-final
  (equal (dec-chain (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key))
                    (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b b)))
         (dec-s-final key b))
  :hints (("Goal" :do-not-induct t
           :expand ((dec-s-chain key b 9) (dec-s-chain key b 8) (dec-s-chain key b 7)
                    (dec-s-chain key b 6) (dec-s-chain key b 5) (dec-s-chain key b 4)
                    (dec-s-chain key b 3) (dec-s-chain key b 2) (dec-s-chain key b 1)
                    (dec-s-chain key b 0))
           :in-theory (e/d (dec-chain dec-s-final)
                           (dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp nth aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3)))))

;; inv_bitslice of an 8-word state is a consp (mirror of the ladder's
;; local helper; needed for the array-index-at-0 step below).
(local (defthm consp-of-ib-val-dec
  (implies (and (true-listp s) (equal (len s) 8))
           (consp (result-ok->val (aes-fixslice-encrypt-inv-bitslice s))))
  :hints (("Goal" :use len-of-ib-val
           :in-theory (e/d () (aes-fixslice-encrypt-inv-bitslice len-of-ib-val nth))))))

;; THE EXTRACTED DECRYPT-BLOCK COMPUTES z-final.
(defthm decrypt-block-is-z-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes-fixslice-encrypt-decrypt-block 100
                    (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) b)
                  (ok (z-final key b))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (dec-collapse dec-chain-is-dec-s-final
                            result-kind-of-inv-bitslice-len len-of-ib-val dec-ladder-final)
                           (dec-s-final dec-chain aes-fixslice-encrypt-aes128-decrypt dec-s-chain z-chain arkw-spec rd8 wstatep xorbytes kmix-bytes sr1-bytes map-sbox16 sub-bytes-nots-bytes inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes mix-columns-1-bytes mix-columns-2-bytes mix-columns-3-bytes invsbox16 map-invsbox16 imc0-bytes imc1-bytes imc2-bytes imc3-bytes kk-iter aes::inp  aes-fixslice-encrypt-aes128-key-schedule aes-fixslice-encrypt-bitslice aes-fixslice-encrypt-inv-bitslice aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-inv-sub-bytes aes-fixslice-encrypt-shift-rows-2 aes-fixslice-encrypt-inv-shift-rows-2 aes-fixslice-encrypt-mix-columns-0 aes-fixslice-encrypt-mix-columns-1 aes-fixslice-encrypt-mix-columns-2 aes-fixslice-encrypt-mix-columns-3 aes-fixslice-encrypt-inv-mix-columns-0 aes-fixslice-encrypt-inv-mix-columns-1 aes-fixslice-encrypt-inv-mix-columns-2 aes-fixslice-encrypt-inv-mix-columns-3))
           :use ((:instance len-when-wstatep (x (dec-s-final key b)))
                 (:instance true-listp-when-wstatep (x (dec-s-final key b)))
                 wstatep-dec-s-final))))
