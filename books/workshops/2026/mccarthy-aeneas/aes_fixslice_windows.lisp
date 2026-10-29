; Phase 5 -- cipher side, part 6: the schedule windows as symmetric bitslices.
;
; Strengthens the keymain window theorems: window r of the extracted
; aes128_key_schedule is not merely readable as fold_r(KK_r) on lane 0 --
; it IS the symmetric bitslice of that byte value:
;
;   rd8(schedule(key), 8r) = bitslice(fk_r, fk_r),   fk_r = fold_r(kk-iter key r)
;
; (Same pinned recipe as keyread's window readbacks -- ks-decomp +
; rd8-of-ks-fold2-w{r} + core-windows-explicit -- but rewriting the fold ops
; with the keyfold op* facts instead of collapsing lane 0, so the window's
; STRUCTURE is retained.)  Corollaries per window: wstatep (the add_round_key
; push-in's hypothesis) and both inv_bitslice lanes (its xor operands).
; Stated over kk-iter; the ladder bridges to aes::keyexpansion at the end
; via kk-iter-is-keyexpansion.
(in-package "ACL2")
(include-book "aes_fixslice_maskalg")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

(defthm window-bitslice-0
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (kk-iter key 0) (kk-iter key 0)))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w0)
                          (:rewrite core-windows-explicit)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-0
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-0
                 (:instance wstatep-of-bitslice (b0 (kk-iter key 0)) (b1 (kk-iter key 0))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-0
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0)))
                  (list (kk-iter key 0) (kk-iter key 0))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-0
                 (:instance inv-bitslice-of-bitslice-general (blk0 (kk-iter key 0)) (blk1 (kk-iter key 0))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-1
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 8)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w1)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr1-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-1
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 8)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-1
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-1
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 8)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-1
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 1))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-2
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 16)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2))) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w2)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr2-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-2
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 16)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-2
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-2
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 16)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2))) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-2
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 2))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-3
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 24)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3))) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w3)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr3-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr3-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-3
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 24)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-3
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-3
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 24)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3))) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-3
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 3))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-4
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 32)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (kk-iter key 4)) (sub-bytes-nots-bytes (kk-iter key 4))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w4)
                          (:rewrite core-windows-explicit)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-4
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 32)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-4
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (kk-iter key 4))) (b1 (sub-bytes-nots-bytes (kk-iter key 4)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-4
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 32)))
                  (list (sub-bytes-nots-bytes (kk-iter key 4)) (sub-bytes-nots-bytes (kk-iter key 4)))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-4
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (kk-iter key 4))) (blk1 (sub-bytes-nots-bytes (kk-iter key 4)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-5
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 40)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w5)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr1-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-5
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 40)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-5
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-5
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 40)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-5
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 5))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-6
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 48)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6))) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w6)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr2-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-6
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 48)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-6
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-6
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 48)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6))) (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-6
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-iter key 6))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-7
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 56)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7))) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w7)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr3-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr3-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-7
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 56)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-7
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-7
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 56)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7))) (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-7
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-iter key 7))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-8
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 64)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (kk-iter key 8)) (sub-bytes-nots-bytes (kk-iter key 8))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w8)
                          (:rewrite core-windows-explicit)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-8
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 64)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-8
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (kk-iter key 8))) (b1 (sub-bytes-nots-bytes (kk-iter key 8)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-8
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 64)))
                  (list (sub-bytes-nots-bytes (kk-iter key 8)) (sub-bytes-nots-bytes (kk-iter key 8)))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-8
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (kk-iter key 8))) (blk1 (sub-bytes-nots-bytes (kk-iter key 8)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-9
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 72)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9)))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w9)
                          (:rewrite core-windows-explicit)
                          (:rewrite isr1-star)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-9
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 72)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-9
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9)))) (b1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-9
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 72)))
                  (list (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9))) (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9))))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-9
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9)))) (blk1 (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-iter key 9))))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

(defthm window-bitslice-10
  (implies (aes::inp key)
           (equal (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80)
                  (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) (sub-bytes-nots-bytes (kk-iter key 10)) (sub-bytes-nots-bytes (kk-iter key 10))))))
  :hints (("Goal" :do-not-induct t
           :use (core-windows-are-bitslice-of-keyexpansion)
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite rd8-of-ks-fold2-w10)
                          (:rewrite core-windows-explicit)
                          (:rewrite sbn-star)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart binary-*) (:executable-counterpart <)
                          (:executable-counterpart zp))))))
(defthm wstatep-window-10
  (implies (aes::inp key)
           (wstatep (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80)))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-10
                 (:instance wstatep-of-bitslice (b0 (sub-bytes-nots-bytes (kk-iter key 10))) (b1 (sub-bytes-nots-bytes (kk-iter key 10)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))
(defthm ib-window-10
  (implies (aes::inp key)
           (equal (result-ok->val (aes-fixslice-encrypt-inv-bitslice (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80)))
                  (list (sub-bytes-nots-bytes (kk-iter key 10)) (sub-bytes-nots-bytes (kk-iter key 10)))))
  :hints (("Goal" :do-not-induct t
           :use (window-bitslice-10
                 (:instance inv-bitslice-of-bitslice-general (blk0 (sub-bytes-nots-bytes (kk-iter key 10))) (blk1 (sub-bytes-nots-bytes (kk-iter key 10)))))
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite result-ok->val-of-result-ok)
                          (:rewrite inp-of-kk-iter)
                          (:rewrite inp-of-sbn-bytes)
                          (:rewrite inp-of-isr1-bytes)
                          (:rewrite inp-of-isr2-bytes)
                          (:rewrite inp-of-isr3-bytes))))))

