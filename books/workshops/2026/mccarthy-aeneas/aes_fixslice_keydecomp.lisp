; Phase 4 -- key-schedule decomposition support: length-only :ok / len /
; true-listp for the fold's shift-rows loops, and length/true-listp of the
; kround chain from the seed.
;
; The fold ops are pure gate/rotation networks (no data-dependent indexing),
; so their :ok needs only that the window is a len-8 true-list -- NOT a wstate.
; (The straight-line window ops' length-only facts -- sub_bytes, sub_bytes_nots,
; add_round_constant_bit -- live upstream in aes_fixslice_keyround, where the
; rcon-loop step equation needs them.)
(in-package "ACL2")
(include-book "aes_fixslice_keysched")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ===========================================================================
;; Length-only :ok and len for the four fold ops (values irrelevant to :ok).
;; ===========================================================================

;; primitives: fixed-shift shr never fails; delta-swap-1 (two fixed shifts) is ok.
(defthm result-kind-u32-shr-small
  (implies (and (natp n) (< n 32)) (equal (result-kind (u32-shr x n)) :ok)))
(defthm result-kind-of-delta-swap-1
  (implies (and (natp shift) (< shift 32))
           (equal (result-kind (aes-fixslice-encrypt-delta-swap-1 a shift mask)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-1))))
(defthm val-of-delta-swap-1-when-ok
  (implies (and (natp shift) (< shift 32))
           (equal (result-ok->val (aes-fixslice-encrypt-delta-swap-1 a shift mask))
                  (u32-xor a (u32-xor (u32-and (u32-xor a (result-ok->val (u32-shr a shift))) mask)
                                      (result-ok->val (u32-shl (u32-and (u32-xor a (result-ok->val (u32-shr a shift))) mask) shift))))))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-delta-swap-1))))

;; ---- the shift_rows loops (upstream iter_mut form; roadmap #8) ----
;; The extracted loops iterate the {lst, pos} IterMut model: next reads the
;; ORIGINAL list (writes are pending in the defunctionalized back list) and
;; -apply-back walks the cursor back down over them.  At len 8 the whole
;; loop unrolls by rewriting -- the (:free ...) :expand hint re-fires at
;; each exposed fuel literal -- so :ok / len / true-listp of the wrappers
;; come out directly, with the delta-swap values held opaque; no loop
;; lemmas or inductions are needed.
(local (include-book "std/lists/update-nth" :dir :system))

;; inv_shift_rows_1 = shift_rows_3 (loop body: swaps at masks 51317760, 855651072)
(defthm result-kind-of-isr1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-1 100 s)) :ok))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-3-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-shift-rows-3)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm len-of-isr1-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 s))) 8))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-3-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-shift-rows-3)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm true-listp-of-isr1-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 s))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-3-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-shift-rows-3)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))

;; inv_shift_rows_2 = shift_rows_2 (single swap at mask 251662080)
(defthm result-kind-of-isr2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-2 100 s)) :ok))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-2-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-shift-rows-2)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm len-of-isr2-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))) 8))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-2-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-shift-rows-2)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm true-listp-of-isr2-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 s))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-2-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-shift-rows-2)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))

;; inv_shift_rows_3 = shift_rows_1 (swaps at masks 202310400, 855651072)
(defthm result-kind-of-isr3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-inv-shift-rows-3 100 s)) :ok))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-1-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3
                            aes-fixslice-encrypt-shift-rows-1)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm len-of-isr3-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 s))) 8))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-1-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3
                            aes-fixslice-encrypt-shift-rows-1)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm true-listp-of-isr3-100
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 s))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-1-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3
                            aes-fixslice-encrypt-shift-rows-1)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))


;; ===========================================================================
;; kr-chain preserves length 88 and true-listp (needed so the fold ops apply).
;; Pure kround facts -- no invariant needed (kround-len / true-listp-of-kround
;; are length-only).
;; ===========================================================================
(defthm len-of-kr-chain
  (implies (and (natp i) (<= i 10) (equal off (* 8 i)) (equal (len rk) 88))
           (equal (len (kr-chain rk off i)) 88))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain) (kround rd8 nth wstatep)))))

(defthm true-listp-of-kr-chain
  (implies (true-listp rk) (true-listp (kr-chain rk off i)))
  :hints (("Goal" :induct (kr-chain rk off i)
           :in-theory (e/d (kr-chain) (kround rd8 nth wstatep)))))

;; length 88 and true-listp of the concrete core (kr-chain from the seed).
(defthm len-of-core
  (implies (aes::inp key)
           (equal (len (kr-chain (seed key) 0 0)) 88))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain seed)
           :use (len-of-seed
                 (:instance len-of-kr-chain (rk (seed key)) (off 0) (i 0))))))
(defthm true-listp-of-core
  (implies (aes::inp key)
           (true-listp (kr-chain (seed key) 0 0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable kr-chain seed)
           :use (true-listp-of-seed
                 (:instance true-listp-of-kr-chain (rk (seed key)))))))
