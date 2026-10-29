; Phase 4 -- THE KEY-EXPANSION THEOREM.
;
; For ALL 16-byte keys (aes::inp key), the extracted RustCrypto fixslice
; aes128_key_schedule succeeds, and every one of its 11 round-key windows,
; un-bitsliced (lane 0), is exactly the audited Kestrel AES key expansion's
; round key with the fixslice fold applied:
;
;   window 0        :  KK(0)                          (= the key itself)
;   windows 1,5,9   :  xor63(invshiftrows^1(KK(r)))
;   windows 2,6     :  xor63(invshiftrows^2(KK(r)))
;   windows 3,7     :  xor63(invshiftrows^3(KK(r)))
;   windows 4,8,10  :  xor63(KK(r))
;
; where KK(r) = round key r of (aes::keyexpansion key 4) -- Kestrel's spec --
; xor63 = sub-bytes-nots-bytes, and invshiftrows^i = inv-shift-rows-i-bytes
; (both defined directly over aes::invshiftrows / the removed S-box affine).
; Composition of ks-decomp (the schedule decomposes), window-r-readback
; (each window in kk-iter terms), and kk-iter-is-keyexpansion (the bridge).
(in-package "ACL2")
(include-book "aes_fixslice_keybridge")
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

(defthm aes128-key-schedule-ok
  (implies (aes::inp key)
           (equal (result-kind (aes-fixslice-encrypt-aes128-key-schedule 100 key)) :ok))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp) (:rewrite rk-of-ok2))))))

(defthm aes128-key-schedule-window-0
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 0))))
                  (kk-of-w (aes::keyexpansion key 4) 0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-0-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-1
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 8))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-of-w (aes::keyexpansion key 4) 1)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-1-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-2
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 16))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-of-w (aes::keyexpansion key 4) 2)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-2-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-3
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 24))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-of-w (aes::keyexpansion key 4) 3)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-3-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-4
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 32))))
                  (sub-bytes-nots-bytes (kk-of-w (aes::keyexpansion key 4) 4))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-4-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-5
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 40))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-of-w (aes::keyexpansion key 4) 5)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-5-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-6
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 48))))
                  (sub-bytes-nots-bytes (inv-shift-rows-2-bytes (kk-of-w (aes::keyexpansion key 4) 6)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-6-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-7
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 56))))
                  (sub-bytes-nots-bytes (inv-shift-rows-3-bytes (kk-of-w (aes::keyexpansion key 4) 7)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-7-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-8
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 64))))
                  (sub-bytes-nots-bytes (kk-of-w (aes::keyexpansion key 4) 8))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-8-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-9
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 72))))
                  (sub-bytes-nots-bytes (inv-shift-rows-1-bytes (kk-of-w (aes::keyexpansion key 4) 9)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-9-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))

(defthm aes128-key-schedule-window-10
  (implies (aes::inp key)
           (equal (car (result-ok->val (aes-fixslice-encrypt-inv-bitslice
                          (rd8 (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) 80))))
                  (sub-bytes-nots-bytes (kk-of-w (aes::keyexpansion key 4) 10))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:rewrite ks-decomp)
                          (:rewrite window-10-readback)
                          (:rewrite kk-iter-is-keyexpansion)
                          (:rewrite result-ok->val-of-result-ok)
                          (:executable-counterpart natp) (:executable-counterpart equal)
                          (:executable-counterpart <))))))
