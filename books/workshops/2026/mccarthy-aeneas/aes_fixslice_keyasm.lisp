; Phase 4 -- key-schedule ASSEMBLY: the extracted schedule decomposes.
;
;   ks-decomp:  (aes::inp key) =>
;     aes128-key-schedule(100, key)  =  (ok (ks-fold2 (kr-chain (seed key) 0 0)))
;
; The upstream schedule body is: seed (bitslice into the rkeys[..8] subslice) ;
; the recursive rcon loop ; a step_by(32) loop of inv_shift_rows triples ;
; one inv_shift_rows_1 window at 72 ; the sub_bytes_nots loop over 1..11.
; Three loop collapses feed the decomposition:
;
; (1) ks-loop0-is-kr-chain : the rcon loop IS kr-chain, by induction on the
;     rounds remaining over keyround's sched-loop0-step (length-only: each
;     round's :ok needs only array bounds, NOT the wok invariant; wok is only
;     needed later to say what the core VALUE is).  off = 8c keeps the offset
;     arithmetic linear.
; (2) ks-loop1-collapse : the (8..72).step_by(32) loop runs exactly twice
;     (i = 8, 40) -- explicit expansion through the synthesized StepBy next --
;     each iteration an isr-step (three w8-spec windows).  The isr ops run at
;     symbolic fuel, canonicalized to 100 by two-fuel inductions on the
;     shift-rows loops.
; (3) ks-loop2-is-sbn-chain : the NOTs loop is sbn-chain, by induction with
;     the byte offset 8i in lockstep.
(in-package "ACL2")
(include-book "aes_fixslice_keydecomp")
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ---------------------------------------------------------------------------
;; (1) the recursive rcon loop IS kr-chain.  Length-only hypotheses.
(defun ks-li (m c rk off)  ; induction scheme mirroring the loop's recursion
  (declare (xargs :measure (nfix (- 10 (nfix c)))))
  (if (or (not (natp c)) (>= c 10)) (list m c rk off)
    (ks-li (1- m) (1+ c) (kround rk off c) (+ off 8))))

(defthm ks-loop0-is-kr-chain
  (implies (and (natp c) (<= c 10) (equal off (* 8 c)) (equal (len rk) 88)
                (true-listp rk) (natp m) (< (+ 11 (- 10 c)) m))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop0 m (rng c 10) rk off)
                  (ok (kr-chain rk off c))))
  :hints (("Goal" :induct (ks-li m c rk off)
           :in-theory (e/d (kr-chain)
                           (kround sched-loop0-step sched-loop0-done
                            aes-fixslice-encrypt-aes128-key-schedule-loop0
                            rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-))))
          ("Subgoal *1/2"
           :expand ((kr-chain rk off c))
           :use ((:instance sched-loop0-step (n m) (rkeys rk) (off off) (c c))
                 (:instance mod-8i (i c))
                 (:instance kround-len (rk rk) (off off) (c c))
                 (:instance true-listp-of-kround (rk rk) (off off) (c c))))
          ("Subgoal *1/1"
           :expand ((kr-chain rk off c))
           :use ((:instance sched-loop0-done (n m) (s c) (e 10) (rkeys rk) (off off))))))

;; ---------------------------------------------------------------------------
;; (2) shift-rows ops are fuel-irrelevant (value-level): at len 8 BOTH fuel
;; spines unroll completely -- nine next steps each; the (:free ...) :expand
;; hint re-fires at every exposed fuel term, with (< 8 (nfix n)) deciding
;; the symbolic side's zp tests -- so the two sides meet syntactically,
;; delta-swap values held opaque.  The isr ops then canonicalize to 100.
(defthm isr1-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-1 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-1 100 s)))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-3-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-shift-rows-3 zp nfix)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm isr2-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-2 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-2 100 s)))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-2-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-shift-rows-2 zp nfix)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))
(defthm isr3-fuel-canon
  (implies (and (syntaxp (not (equal n (quote (quote 100)))))
                (true-listp s) (equal (len s) 8) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-inv-shift-rows-3 n s)
                  (aes-fixslice-encrypt-inv-shift-rows-3 100 s)))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (n it bk) (aes-fixslice-encrypt-shift-rows-1-loop0 n it bk)))
           :in-theory (e/d (aes-fixslice-encrypt-inv-shift-rows-3
                            aes-fixslice-encrypt-shift-rows-1 zp nfix)
                           (aes-fixslice-encrypt-delta-swap-1
                            u32-xor u32-and u32-shl u32-shr nth)))))

;; ---------------------------------------------------------------------------
;; the spec chains (pure w8-spec window forms; the ops at canonical fuel 100).
(defund isr-step (rk base)
  (b* ((rk1 (w8-spec 0 8 rk base
              (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100 (rd8 rk base)))))
       (rk2 (w8-spec 0 8 rk1 (+ base 8)
              (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-2 100 (rd8 rk1 (+ base 8)))))))
    (w8-spec 0 8 rk2 (+ base 16)
      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-3 100 (rd8 rk2 (+ base 16)))))))

;; the NOTs chain, threading the byte offset additively (off = 8i, lockstep).
(defun sbn-chain (rk off i)
  (declare (xargs :measure (nfix (- 11 (nfix i)))))
  (if (or (not (natp i)) (>= i 11)) rk
    (sbn-chain (w8-spec 0 8 rk off
                 (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 rk off))))
               (+ off 8) (1+ i))))

;; length facts for the chains.
(defthm len-of-isr-step
  (implies (and (natp base) (<= (+ base 24) (len rk)))
           (equal (len (isr-step rk base)) (len rk)))
  :hints (("Goal" :in-theory (e/d (isr-step) (w8-spec rd8 nth
                                   aes-fixslice-encrypt-inv-shift-rows-1
                                   aes-fixslice-encrypt-inv-shift-rows-2
                                   aes-fixslice-encrypt-inv-shift-rows-3)))))

(defthm true-listp-of-isr-step-88
  (implies (and (natp base) (<= (+ base 24) 88) (equal (len rk) 88) (true-listp rk))
           (true-listp (isr-step rk base)))
  :hints (("Goal" :in-theory (e/d (isr-step) (w8-spec rd8 nth
                                   aes-fixslice-encrypt-inv-shift-rows-1
                                   aes-fixslice-encrypt-inv-shift-rows-2
                                   aes-fixslice-encrypt-inv-shift-rows-3)))))

(defthm mul-8-le-80 (implies (and (natp i) (< i 11)) (<= (* 8 i) 80)))

(defthm len-of-sbn-chain
  (implies (and (equal (len rk) 88) (natp i) (<= 1 i) (equal off (* 8 i)))
           (equal (len (sbn-chain rk off i)) 88))
  :hints (("Goal" :induct (sbn-chain rk off i)
           :in-theory (e/d (sbn-chain) (w8-spec rd8 nth
                            aes-fixslice-encrypt-sub-bytes-nots)))))

;; ---------------------------------------------------------------------------
;; loop1 (isr triples at i = 8, 40 via step_by(32)) collapses by explicit
;; three-step expansion through the synthesized StepBy next.
(defthm ks-loop1-collapse
  (implies (and (equal (len rk) 88) (true-listp rk) (natp m) (< 12 (nfix m)))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop1 m
                    (core-iter-adapters-step-by-stepby-core-ops-range-range-usize- (rng 8 72) 31 t)
                    rk)
                  (ok (isr-step (isr-step rk 8) 40))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (it) (aes-fixslice-encrypt-aes128-key-schedule-loop1 m it rk))
                    (:free (mm it rr) (aes-fixslice-encrypt-aes128-key-schedule-loop1 mm it rr)))
           :in-theory (e/d (isr-step)
                           (aes-fixslice-encrypt-inv-shift-rows-1
                            aes-fixslice-encrypt-inv-shift-rows-2
                            aes-fixslice-encrypt-inv-shift-rows-3
                            vec-index-range vec-update-range
                            w8-spec rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-)
                            (:executable-counterpart core-iter-adapters-step-by-stepby-core-ops-range-range-usize-))))))

;; result-p facts (the fty equality (equal x (ok v)) decomposes into
;; result-p x + kind + val; the loop needs its own return-type fact).
(local (defthm result-p-of-vec-index-range
  (result-p (vec-index-range v lo hi))
  :hints (("Goal" :in-theory (enable vec-index-range)))))
(local (defthm result-p-of-sub-bytes-nots
  (result-p (aes-fixslice-encrypt-sub-bytes-nots s))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-nots)
                                  (u32-xor nth))))))
(defthm result-p-of-ks-loop2
  (result-p (aes-fixslice-encrypt-aes128-key-schedule-loop2 n iter rk))
  :hints (("Goal" :induct (aes-fixslice-encrypt-aes128-key-schedule-loop2 n iter rk)
           :in-theory (disable aes-fixslice-encrypt-sub-bytes-nots vec-index-range
                               vec-update-range nth))))

;; ---------------------------------------------------------------------------
;; loop2 (the NOTs) IS sbn-chain, by induction (byte offset 8i in lockstep).
(defun sbn-li (m i rk)
  (declare (xargs :measure (nfix (- 11 (nfix i)))))
  (if (or (not (natp i)) (>= i 11)) (list m i rk)
    (sbn-li (1- m) (1+ i)
            (w8-spec 0 8 rk (* 8 i)
              (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (rd8 rk (* 8 i))))))))

(defthm ks-loop2-is-sbn-chain
  (implies (and (natp i) (<= 1 i) (<= i 11) (equal (len rk) 88) (true-listp rk)
                (natp m) (< (+ 1 (- 11 i)) m))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk)
                  (ok (sbn-chain rk (* 8 i) i))))
  :hints (("Goal" :induct (sbn-li m i rk)
           :in-theory (e/d (rnext-on-range mul-8-distrib)
                           (aes-fixslice-encrypt-aes128-key-schedule-loop2
                            aes-fixslice-encrypt-sub-bytes-nots
                            vec-index-range vec-update-range
                            sbn-chain w8-spec rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-))))
          ("Subgoal *1/2"
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk)
                    (sbn-chain rk (* 8 i) i)))
          ("Subgoal *1/1"
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop2 m (rng i 11) rk)
                    (sbn-chain rk (* 8 i) i)))))

;; ---------------------------------------------------------------------------
;; THE DECOMPOSITION.  With all three loops collapsed, the schedule body is
;; the seed binds, the loop calls, and the isr1 window at 72 -- the collapse
;; ends in (ok (sbn-chain ...)) with no constructor residue.
(defund ks-fold2 (w)
  (sbn-chain
    (w8-spec 0 8 (isr-step (isr-step w 8) 40) 72
      (result-ok->val (aes-fixslice-encrypt-inv-shift-rows-1 100
        (rd8 (isr-step (isr-step w 8) 40) 72))))
    8 1))

(defthm rk-of-ok2 (equal (result-kind (result-ok x)) :ok))

;; site bridges for the two literal-window subslice borrows in the schedule
;; body (proved in the full theory, where the range accessors compute; pinned
;; below, where they must stay closed).  Written with the body's exact shapes.
(defthm seed-read-ok
  (equal (result-kind (vec-index-range (array-repeat 88 0) 0
           (core-ops-range-rangeto-usize-->end (core-ops-range-rangeto-usize- 8))))
         :ok))
(defthm seed-read-val
  (equal (result-ok->val (vec-index-range (array-repeat 88 0) 0
           (core-ops-range-rangeto-usize-->end (core-ops-range-rangeto-usize- 8))))
         (list 0 0 0 0 0 0 0 0)))
(defthm seed-write-is-seed
  (equal (vec-update-range (array-repeat 88 0) 0
           (core-ops-range-rangeto-usize-->end (core-ops-range-rangeto-usize- 8))
           (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) key key)))
         (seed key))
  :hints (("Goal" :in-theory (enable seed))))
(defthm w72-read-ok
  (implies (equal (len rk) 88)
           (equal (result-kind (vec-index-range rk
                    (core-ops-range-range-usize-->start (core-ops-range-range-usize- 72 80))
                    (core-ops-range-range-usize-->end (core-ops-range-range-usize- 72 80))))
                  :ok)))
(defthm w72-read-val
  (implies (and (equal (len rk) 88) (true-listp rk))
           (equal (result-ok->val (vec-index-range rk
                    (core-ops-range-range-usize-->start (core-ops-range-range-usize- 72 80))
                    (core-ops-range-range-usize-->end (core-ops-range-range-usize- 72 80))))
                  (rd8 rk 72)))
  :hints (("Goal" :in-theory (disable rd8 nth))))
(defthm w72-write
  (implies (and (equal (len rk) 88) (true-listp rk)
                (true-listp s) (equal (len s) 8))
           (equal (vec-update-range rk
                    (core-ops-range-range-usize-->start (core-ops-range-range-usize- 72 80))
                    (core-ops-range-range-usize-->end (core-ops-range-range-usize- 72 80))
                    s)
                  (w8-spec 0 8 rk 72 s)))
  :hints (("Goal" :in-theory (disable w8-spec nth))))

;; window facts for the isr1-at-72 step, at the abstraction the pinned proof
;; uses (rd8 window of the isr-step composition is a len-8 true-list).
(defthm len-of-rd8-8b (equal (len (rd8 l off)) 8)
  :hints (("Goal" :in-theory (enable rd8))))
(defthm true-listp-of-rd8b (true-listp (rd8 l off))
  :hints (("Goal" :in-theory (enable rd8))))

(defthm ks-decomp
  (implies (aes::inp key)
           (equal (aes-fixslice-encrypt-aes128-key-schedule 100 key)
                  (ok (ks-fold2 (kr-chain (seed key) 0 0)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'ground-zero)
                        '((:definition aes-fixslice-encrypt-aes128-key-schedule)
                          (:definition ks-fold2)
                          (:definition core-iter-traits-collect-impl-core-iter-traits-collect-intoiterator-for-core-ops-range-range-usize-into-iter-core-ops-range-range-usize-)
                          (:definition core-iter-traits-iterator-iterator-step-by-core-ops-range-range-usize-)
                          (:definition core-iter-traits-collect-impl-core-iter-traits-collect-intoiterator-for-core-iter-adapters-step-by-stepby-core-ops-range-range-usize-into-iter-core-iter-adapters-step-by-stepby-core-ops-range-range-usize-)
                          (:definition not)
                          (:rewrite seed-read-ok) (:rewrite seed-read-val)
                          (:rewrite seed-write-is-seed)
                          (:rewrite w72-read-ok) (:rewrite w72-read-val) (:rewrite w72-write)
                          (:rewrite bitslice-ok)
                          (:rewrite result-kind-of-isr1-len) (:rewrite len-of-isr1-len)
                          (:rewrite true-listp-of-isr1-100)
                          (:rewrite len-of-rd8-8b) (:rewrite true-listp-of-rd8b)
                          (:rewrite ks-loop0-is-kr-chain)
                          (:rewrite ks-loop1-collapse)
                          (:rewrite ks-loop2-is-sbn-chain)
                          (:rewrite len-of-seed) (:rewrite true-listp-of-seed)
                          (:rewrite len-of-core) (:rewrite true-listp-of-core)
                          (:rewrite len-of-isr-step) (:rewrite true-listp-of-isr-step-88)
                          (:rewrite len-of-w8spec-88) (:rewrite true-listp-of-w8-spec)
                          (:rewrite result-ok->val-of-result-ok)
                          (:rewrite rk-of-ok2)
                          (:executable-counterpart nfix) (:executable-counterpart zp)
                          (:executable-counterpart binary-+) (:executable-counterpart binary-*)
                          (:executable-counterpart <) (:executable-counterpart unary--)
                          (:executable-counterpart natp) (:executable-counterpart integerp)
                          (:executable-counterpart equal) (:executable-counterpart eq)
                          (:executable-counterpart not))))))
