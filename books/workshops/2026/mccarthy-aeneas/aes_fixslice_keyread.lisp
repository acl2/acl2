; Phase 4 -- WINDOW READBACK: each of the 11 windows of the decomposed
; schedule value  ks-fold2(kr-chain(seed key))  reads back, through
; inv_bitslice lane 0, as the byte-level folded round key:
;
;   window 0            :  kk_0  (= key)
;   windows 1,5,9       :  xor63(invshiftrows^1(kk_r))
;   windows 2,6         :  xor63(invshiftrows^2(kk_r))
;   windows 3,7         :  xor63(invshiftrows^3(kk_r))
;   windows 4,8,10      :  xor63(kk_r)
;
; where kk_r = kk-iter(key, r) is the iterated key-expansion recurrence.
; Layering: (A) pure array bookkeeping -- what each fold op leaves at each
; 8-aligned window (rd8-of-w8spec same/frame threading over the isr-step /
; sbn-chain window forms; all length-only); (B) per-window composition over
; ks-fold2; (C) the core windows from wok; then the keyfold fk-read facts
; finish each window in byte terms.
(in-package "ACL2")
(include-book "aes_fixslice_keyasm")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ===========================================================================
;; (A) reading isr-step: the three written windows and the frame.  Pinned
;; theory: exactly the w8-spec same/frame algebra plus the length facts that
;; discharge their hypotheses (the default theory's arithmetic diverges on the
;; nested window threading).
(defthm rd8-of-isr-step-w1
  (implies (and (natp base) (<= (+ base 24) (len rk)))
           (equal (rd8 (isr-step rk base) base)
                  (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 rk base)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition isr-step)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite len-of-isr2-len) (:rewrite len-of-isr3-len)
                          (:rewrite true-listp-of-isr1-100) (:rewrite true-listp-of-isr2-100) (:rewrite true-listp-of-isr3-100)
                          (:executable-counterpart binary-+) (:executable-counterpart <)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart unary--))))))
(defthm rd8-of-isr-step-w2
  (implies (and (natp base) (<= (+ base 24) (len rk)))
           (equal (rd8 (isr-step rk base) (+ base 8))
                  (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 rk (+ base 8))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition isr-step)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite len-of-isr2-len) (:rewrite len-of-isr3-len)
                          (:rewrite true-listp-of-isr1-100) (:rewrite true-listp-of-isr2-100) (:rewrite true-listp-of-isr3-100)
                          (:executable-counterpart binary-+) (:executable-counterpart <)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart unary--))))))
(defthm rd8-of-isr-step-w3
  (implies (and (natp base) (<= (+ base 24) (len rk)))
           (equal (rd8 (isr-step rk base) (+ base 16))
                  (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 rk (+ base 16))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition isr-step)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite len-of-isr2-len) (:rewrite len-of-isr3-len)
                          (:rewrite true-listp-of-isr1-100) (:rewrite true-listp-of-isr2-100) (:rewrite true-listp-of-isr3-100)
                          (:executable-counterpart binary-+) (:executable-counterpart <)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart unary--))))))
(defthm rd8-of-isr-step-frame
  (implies (and (natp base) (<= (+ base 24) (len rk))
                (natp j8) (or (<= (+ j8 8) base) (<= (+ base 24) j8)))
           (equal (rd8 (isr-step rk base) j8) (rd8 rk j8)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition isr-step)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite len-of-isr2-len) (:rewrite len-of-isr3-len)
                          (:rewrite true-listp-of-isr1-100) (:rewrite true-listp-of-isr2-100) (:rewrite true-listp-of-isr3-100)
                          (:executable-counterpart binary-+) (:executable-counterpart <)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart unary--))))))

;; ===========================================================================
;; (A3) reading through the sbn chain: window 8r gets one sub_bytes_nots if
;; the chain has reached it (r >= i), else it is untouched.  Lockstep offsets.
(defthm rd8-of-sbn-chain
  (implies (and (natp i) (<= 1 i) (<= i 11) (equal off (* 8 i))
                (equal (len rk) 88) (true-listp rk)
                (natp r) (<= r 10))
           (equal (rd8 (sbn-chain rk off i) (* 8 r))
                  (if (< r i) (rd8 rk (* 8 r))
                    (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 rk (* 8 r)))))))
  :hints (("Goal" :induct (sbn-chain rk off i)
           :in-theory (e/d (sbn-chain)
                           (aes-fixslice-encrypt-sub-bytes-nots
                            w8-spec rd8 nth wstatep)))))

;; ===========================================================================
;; (B) per-window reads over the whole fold ks-fold2.

(defthm rd8-of-ks-fold2-w0
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 0) (rd8 w 0)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 0)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w1
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 8) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 w 8)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 1)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w2
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 16) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 w 16)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 2)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w3
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 24) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 w 24)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 3)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w4
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 32) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 w 32)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 4)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w5
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 40) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 w 40)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 5)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w6
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 48) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 w 48)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 6)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w7
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 56) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 w 56)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 7)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w8
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 64) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 w 64)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 8)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w9
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 72) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 w 72)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 9)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))

(defthm rd8-of-ks-fold2-w10
  (implies (and (equal (len w) 88) (true-listp w))
           (equal (rd8 (ks-fold2 w) 80) (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 w 80)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance rd8-of-sbn-chain (rk (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72 (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 (isr-step (isr-step w 8) 40) 72))))) (off 8) (i 1) (r 10)))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition ks-fold2)
                          (:rewrite rd8-of-isr-step-w1) (:rewrite rd8-of-isr-step-w2) (:rewrite rd8-of-isr-step-w3)
                          (:rewrite rd8-of-isr-step-frame)
                          (:rewrite rd8-of-w8spec-same) (:rewrite rd8-of-w8spec-frame)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite len-of-w8-spec) (:rewrite true-listp-of-w8-spec) (:rewrite len-of-isr-step)
                          (:rewrite len-of-rd8-8) (:rewrite true-listp-of-rd8)
                          (:rewrite len-of-isr1-len) (:rewrite true-listp-of-isr1-100)
                          (:rewrite true-listp-of-isr-step-88)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart natp)
                          (:executable-counterpart equal) (:executable-counterpart unary--)
                          (:executable-counterpart true-listp) (:executable-counterpart len))))))
;; ===========================================================================
;; (C) the 11 core windows, explicitly, from the wok invariant.
(defthm core-windows-explicit
  (implies (wok rk key 80 10)
           (and (equal (rd8 rk 80) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 10) (kk-iter key 10)))) (equal (rd8 rk 72) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 9) (kk-iter key 9)))) (equal (rd8 rk 64) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 8) (kk-iter key 8)))) (equal (rd8 rk 56) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 7) (kk-iter key 7)))) (equal (rd8 rk 48) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 6) (kk-iter key 6)))) (equal (rd8 rk 40) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 5) (kk-iter key 5)))) (equal (rd8 rk 32) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 4) (kk-iter key 4)))) (equal (rd8 rk 24) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 3) (kk-iter key 3)))) (equal (rd8 rk 16) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 2) (kk-iter key 2)))) (equal (rd8 rk 8) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 1) (kk-iter key 1)))) (equal (rd8 rk 0) (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 0) (kk-iter key 0))))))
  :hints (("Goal" :do-not-induct t
           :expand ((wok rk key 80 10) (wok rk key 72 9) (wok rk key 64 8) (wok rk key 56 7) (wok rk key 48 6) (wok rk key 40 5) (wok rk key 32 4) (wok rk key 24 3) (wok rk key 16 2) (wok rk key 8 1) (wok rk key 0 0))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:executable-counterpart nfix) (:executable-counterpart binary-+)
                          (:executable-counterpart unary--) (:executable-counterpart zp)
                          (:executable-counterpart natp) (:executable-counterpart equal))))))

;; ===========================================================================
;; (FINAL) per-window byte-level readback of the decomposed schedule value:
;; MILESTONE B.  Everything fires as rewrites in a pinned theory; the only
;; :use supplies the wok invariant (Milestone A) for the free-var hyp of the
;; core-windows-explicit rules.

(defthm window-0-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 0))))
                  (kk-iter key 0)))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w0)
                          (:rewrite core-windows-explicit)
                          (:rewrite inv-bitslice-of-bitslice-general)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-1-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 8))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w1)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr1)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-2-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 16))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w2)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr2)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-3-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 24))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w3)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr3)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-4-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 32))))
                  (sub-bytes-nots-bytes (kk-iter key 4))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w4)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-sbn)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-5-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 40))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w5)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr1)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-6-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 48))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w6)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr2)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-7-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 56))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w7)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr3)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-8-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 64))))
                  (sub-bytes-nots-bytes (kk-iter key 8))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w8)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-sbn)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-9-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 72))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w9)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-isr1)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))

(defthm window-10-readback
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (ks-fold2 (kr-chain (seed key) 0 0)) 80))))
                  (sub-bytes-nots-bytes (kk-iter key 10))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite rd8-of-ks-fold2-w10)
                          (:rewrite core-windows-explicit)
                          (:rewrite fk-read-sbn)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
