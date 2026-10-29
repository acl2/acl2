; Phase 4 -- key-schedule: ONE rcon-loop iteration == the pure window model
; kround, and the window transform it applies == krw8, verified for ALL inputs.
;
; The upstream aes128_key_schedule inlines each round in the rcon loop body
; (memshift32 ; sub_bytes ; sub_bytes_nots ; add_round_constant_bit(s) ;
; xor_columns, all through &mut rkeys[off..off+8] subslice windows), so the
; interface here is a LOOP-STEP equation rather than a per-function unfold:
;   * sched-loop0-step : one iteration of the extracted rcon loop at index c
;       steps  loop0(n, rng(c,10), rkeys, off)
;           -> loop0(n-1, rng(c+1,10), kround(rkeys,off,c), off+8)
;     under LENGTH-ONLY hypotheses (upstream's own debug_asserts: off 8-aligned,
;     off+16 <= len; no wstate invariant needed for the step itself)
;   * sched-loop0-done : the loop returns (ok rkeys) once the range is empty
;   * kround(rk,off,c) = xc-spec(w8-spec(ms-spec(rk), arc-list(sbn(sb(rd8 rk
;       off))), c), 14) -- the collapsed pure tower; and its readers:
;     kround-window   : rd8(kround(rk,off,c), off+8) = krw8(rd8(rk,off), c)
;     kround-len / kround-frame-below / true-listp-of-kround
;   * wstatep-of-krw8 : the new window is again a wstate (8 u32) -- the loop
;     invariant the 10-round chain threads (bitslice of the key seeds it)
; krw8 is off-INDEPENDENT: exactly the transform the keystep step-star cruxes
; prove equals the AES key-expansion recurrence, so the chain lifts each of
; the 10 concrete offsets to Kestrel's keyexpansion.  All structured rewriting;
; GL only for the irreducible per-op bit facts (S-box, xc-word, bitslice range).
;
; RULE-SHAPE NOTE: window arithmetic in left-hand sides is bound as free
; variables pinned by (equal dst (+ src 8))-style hypotheses -- embedded
; (+ src 8) patterns never match ACL2's constant-first sum normal form (+ 8 src)
; nor evaluated literals (see the keychain window-bridge note).
(in-package "ACL2")
(include-book "aes_fixslice_keyops")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth-when-zp)))

(defthm true-listp-of-ms-spec
  (implies (true-listp buffer) (true-listp (ms-spec i e buffer src dst))))

;; every schedule call site is 8-aligned; discharge memshift's debug_assert
;; hypothesis automatically at (* 8 i) offsets (and by evaluation at literals).
;; Alignment hypotheses on exported rules are stated in MOD form: arithmetic-5
;; normalizes goal-side (rem off 8) to (mod off 8), and backchain relief of a
;; REM-form rule hypothesis does not cross that normalization (rem-to-mod is
;; restricted during backchaining) -- MOD-form hyps relieve from both.
(defthm rem-8i (implies (natp i) (equal (rem (* 8 i) 8) 0)))
(defthm mod-8i (implies (natp i) (equal (mod (* 8 i) 8) 0)))

;; ---------------------------------------------------------------------------
;; generalized (free-variable) window rules for ms-spec -- the shapes that
;; actually match the normalized goals of the inline loop body.
(defthm rd8-of-msspec-dst-g      ; memshift copies src-window into dst-window
  (implies (and (natp src) (equal dst (+ src 8)))
           (equal (rd8 (ms-spec 0 8 buffer src dst) dst) (rd8 buffer src)))
  :hints (("Goal" :in-theory (e/d (rd8) (ms-spec nth)))))
(defthm rd8-of-msspec-frame-g    ; below the dst-window, unchanged
  (implies (and (natp src) (equal dst (+ src 8)) (natp off) (<= (+ off 8) dst))
           (equal (rd8 (ms-spec 0 8 buffer src dst) off) (rd8 buffer off)))
  :hints (("Goal" :in-theory (e/d (rd8) (ms-spec nth)))))
(defthm len-of-msspec-g
  (implies (and (natp src) (equal dst (+ src 8)) (<= (+ src 16) (len buffer)))
           (equal (len (ms-spec 0 8 buffer src dst)) (len buffer)))
  :hints (("Goal" :use ((:instance len-of-ms-spec (i 0) (e 8)))
           :in-theory (disable len-of-ms-spec ms-spec))))

;; ---------------------------------------------------------------------------
;; generic-fuel op interface for the two loop-based sub-ops (the inline body
;; calls them at fuel n-1, so the fixed-100 forms never apply).
(defthm memshift32-is-msspec-n
  (implies (and (natp src) (equal (mod src 8) 0)
                (<= (+ src 16) (len buffer)) (< (len buffer) 4294967296)
                (true-listp buffer) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-memshift32 n buffer src)
                  (ok (ms-spec 0 8 buffer src (+ src 8)))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-memshift32)
                                  (aes-fixslice-encrypt-memshift32-loop0 ms-spec ms-spec-d
                                   rev-on-range))
                  :use ((:instance ms-loop0-is-msspec-d (s 0) (e 8) (dst (+ src 8)))
                        (:instance ms-spec-d-is-ms-spec (e 8) (dst (+ src 8)))))))

(defthm xor-columns-is-xcspec-n
  (implies (and (natp off) (natp dx) (<= dx off) (<= (+ off 8) (len rkeys))
                (< (len rkeys) 4294967296) (< 8 (nfix n)))
           (equal (aes-fixslice-encrypt-xor-columns n rkeys off dx dror)
                  (ok (xc-spec 0 8 rkeys off dx dror))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-xor-columns)
                                  (aes-fixslice-encrypt-xor-columns-loop0 xc-spec))
                  :use (:instance xc-loop0-is-xcspec (i 0) (e 8)))))

(defthm true-listp-of-xc-spec
  (implies (true-listp rkeys) (true-listp (xc-spec i e rkeys off dx dror)))
  :hints (("Goal" :induct (xc-spec i e rkeys off dx dror)
           :in-theory (disable xc-word))))

;; ---------------------------------------------------------------------------
;; LENGTH-ONLY :ok / len / true-listp for the straight-line window ops, so the
;; loop-step equation needs no wstate invariant (the values are irrelevant to
;; the control flow; upstream's debug_asserts demand exactly len == 8).
;; sub_bytes: proving :ok/len on a symbolic len-8 list makes the 16 array
;; bounds case-split (2^16); prove on an EXPLICIT 8-list (everything computes)
;; and lift via expand-len-8.
(local (defthm rk-sub-bytes-explicit
  (equal (result-kind (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))) :ok)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(local (defthm len-sub-bytes-explicit
  (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7)))) 8)
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(local (defthm tl-sub-bytes-explicit
  (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes (list a0 a1 a2 a3 a4 a5 a6 a7))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes) (u32-xor u32-and))))))
(defthm result-kind-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance rk-sub-bytes-explicit
                  (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s))
                  (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s)))
                 (:instance expand-len-8 (x s))))))
(defthm len-of-sub-bytes-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes s))) 8))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance len-sub-bytes-explicit
                  (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s))
                  (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s)))
                 (:instance expand-len-8 (x s))))))
(defthm true-listp-of-sub-bytes-val
  (implies (and (true-listp s) (equal (len s) 8))
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (disable aes-fixslice-encrypt-sub-bytes nth)
           :use ((:instance tl-sub-bytes-explicit
                  (a0 (nth 0 s)) (a1 (nth 1 s)) (a2 (nth 2 s)) (a3 (nth 3 s))
                  (a4 (nth 4 s)) (a5 (nth 5 s)) (a6 (nth 6 s)) (a7 (nth 7 s)))
                 (:instance expand-len-8 (x s))))))
;; sub_bytes_nots: straight-line (indices 0,1,5,6) -- direct.
(defthm result-kind-of-sub-bytes-nots-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (result-kind (aes-fixslice-encrypt-sub-bytes-nots s)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-sub-bytes-nots))))
(defthm len-of-sub-bytes-nots-len
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (len (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots s))) (len s)))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-sub-bytes-nots))))
(defthm true-listp-of-sub-bytes-nots-val
  (implies (true-listp s)
           (true-listp (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots s))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-sub-bytes-nots) (u32-xor nth)))))
;; add_round_constant_bit (array-index ; xor ; array-update at index bit).
(defthm result-kind-of-arcbit-len
  (implies (and (natp bit) (< bit (len s)))
           (equal (result-kind (aes-fixslice-encrypt-add-round-constant-bit s bit)) :ok))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-add-round-constant-bit))))
(defthm len-of-arcbit-len
  (implies (and (natp bit) (< bit (len s)))
           (equal (len (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s bit))) (len s)))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-add-round-constant-bit))))
(defthm true-listp-of-arcbit-val
  (implies (and (true-listp s) (natp bit) (< bit (len s)))
           (true-listp (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s bit))))
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-add-round-constant-bit))))

;; ror_distance(1,3) = 14, the concrete rotation the schedule uses.
(defthm ror-distance-1-3 (equal (aes-fixslice-encrypt-ror-distance 1 3) (ok 14)))

;; ---------------------------------------------------------------------------
;; The pure model of ONE rcon-loop iteration's effect on rkeys, and the
;; off-independent window transform it applies.
(defund kround (rk off c)
  (xc-spec 0 8
    (w8-spec 0 8 (ms-spec 0 8 rk off (+ off 8)) (+ off 8)
      (arc-list (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
                  (result-ok->val (aes-fixslice-encrypt-sub-bytes (rd8 rk off))))) c))
    (+ off 8) 8 14))

(defund krw8 (s8 c)
  (b* ((sb  (result-ok->val (aes-fixslice-encrypt-sub-bytes s8)))
       (sbn (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots sb)))
       (d   (arc-list sbn c))
       ((ok dror) (aes-fixslice-encrypt-ror-distance 1 3)))
    (list (xc-word (nth 0 s8) (nth 0 d) dror) (xc-word (nth 1 s8) (nth 1 d) dror)
          (xc-word (nth 2 s8) (nth 2 d) dror) (xc-word (nth 3 s8) (nth 3 d) dror)
          (xc-word (nth 4 s8) (nth 4 d) dror) (xc-word (nth 5 s8) (nth 5 d) dror)
          (xc-word (nth 6 s8) (nth 6 d) dror) (xc-word (nth 7 s8) (nth 7 d) dror))))

;; ---------------------------------------------------------------------------
;; THE LOOP-STEP EQUATION: one iteration of the extracted rcon loop is kround.
(defthm sched-loop0-done
  (implies (and (natp s) (natp e) (<= e s) (not (zp n)))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop0 n (rng s e) rkeys off)
                  (ok rkeys)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop0 n (rng s e) rkeys off))
                  :in-theory (enable rnext-on-range))))

(defthm sched-loop0-step
  (implies (and (natp c) (< c 10) (natp off) (equal (mod off 8) 0)
                (<= (+ off 16) (len rkeys)) (< (len rkeys) 4294967296)
                (true-listp rkeys) (< 10 (nfix n)))
           (equal (aes-fixslice-encrypt-aes128-key-schedule-loop0 n (rng c 10) rkeys off)
                  (aes-fixslice-encrypt-aes128-key-schedule-loop0 (1- n) (rng (+ c 1) 10)
                    (kround rkeys off c) (+ off 8))))
  :hints (("Goal" :do-not-induct t
           :expand ((aes-fixslice-encrypt-aes128-key-schedule-loop0 n (rng c 10) rkeys off))
           :in-theory (e/d (kround arc-list rnext-on-range)
                           (aes-fixslice-encrypt-aes128-key-schedule-loop0
                            aes-fixslice-encrypt-memshift32
                            aes-fixslice-encrypt-xor-columns
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-add-round-constant-bit
                            vec-index-range vec-update-range
                            w8-spec ms-spec xc-spec rd8 nth wstatep
                            (:executable-counterpart core-ops-range-range-usize-))))))

;; ---------------------------------------------------------------------------
;; kround's readers (all length-only; the specs stay closed).
(defthm kround-len
  (implies (and (natp off) (<= (+ off 16) (len rk)))
           (equal (len (kround rk off c)) (len rk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (kround)
                           (w8-spec ms-spec xc-spec rd8 nth arc-list
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots)))))

(defthm true-listp-of-kround
  (implies (true-listp rk) (true-listp (kround rk off c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (kround)
                           (w8-spec ms-spec xc-spec rd8 nth arc-list
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots)))))

;; FRAME: positions strictly below the written window are unchanged, so earlier
;; round keys survive each subsequent round.
(defthm kround-frame-below
  (implies (and (natp off) (<= (+ off 16) (len rk))
                (natp k) (< k (+ off 8)))
           (equal (nth k (kround rk off c)) (nth k rk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (kround)
                           (w8-spec ms-spec xc-spec rd8 arc-list
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots)))))

;; The new window rkeys[off+8..off+16) after one round == krw8(prev window).
(defthm kround-window
  (implies (and (natp off) (<= (+ off 16) (len rk)))
           (equal (rd8 (kround rk off c) (+ off 8))
                  (krw8 (rd8 rk off) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (kround krw8 rd8)
                           (w8-spec ms-spec xc-spec nth arc-list
                            aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots
                            aes-fixslice-encrypt-ror-distance)))))

;; xc-word maps u32s to a u32 (all ops mod-2^32); GL at the concrete rotation
;; ror_distance(1,3)=14 that krw8 uses (a symbolic amount blows up the BDDs).
(gl::def-gl-thm u32p-of-xc-word-gl
  :hyp (and (unsigned-byte-p 32 left) (unsigned-byte-p 32 cur))
  :concl (unsigned-byte-p 32 (xc-word left cur 14))
  :g-bindings (gl::auto-bindings (:nat left 32) (:nat cur 32)))
(defthm u32p-of-xc-word
  (implies (and (unsigned-byte-p 32 left) (unsigned-byte-p 32 cur))
           (unsigned-byte-p 32 (xc-word left cur 14)))
  :hints (("Goal" :use u32p-of-xc-word-gl :in-theory (disable u32p-of-xc-word-gl xc-word))))

;; extract a u32 element from a wstate at a literal index (syntaxp: no looping)
(defthm u32-nth-of-wstatep
  (implies (and (syntaxp (quotep k)) (wstatep x) (natp k) (< k 8))
           (unsigned-byte-p 32 (nth k x)))
  :hints (("Goal" :in-theory (enable wstatep)
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3)
                   (equal k 4) (equal k 5) (equal k 6) (equal k 7)))))
;; build a wstate from 8 u32s
(defthm wstatep-of-list8
  (implies (and (unsigned-byte-p 32 e0) (unsigned-byte-p 32 e1) (unsigned-byte-p 32 e2) (unsigned-byte-p 32 e3)
                (unsigned-byte-p 32 e4) (unsigned-byte-p 32 e5) (unsigned-byte-p 32 e6) (unsigned-byte-p 32 e7))
           (wstatep (list e0 e1 e2 e3 e4 e5 e6 e7)))
  :hints (("Goal" :in-theory (enable wstatep))))

;; krw8 maps a wstate to a wstate (ror_distance(1,3) computes to 14).
(defthm wstatep-of-krw8
  (implies (and (wstatep s8) (natp c) (< c 12)) (wstatep (krw8 s8 c)))
  :hints (("Goal" :in-theory (e/d (krw8) (wstatep xc-word arc-list nth
                                   aes-fixslice-encrypt-sub-bytes aes-fixslice-encrypt-sub-bytes-nots))
                  :use ((:instance wstatep-of-arc-list
                          (s8 (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots
                                (result-ok->val (aes-fixslice-encrypt-sub-bytes s8)))))))
                  :do-not-induct t)))

;; bitslice of two 16-byte blocks is a wstate (8 u32) -- GL + expand-len-16 lift.
(gl::def-gl-thm wstatep-of-bitslice-gl
  :hyp (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15)
            (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3) (unsigned-byte-p 8 b4) (unsigned-byte-p 8 b5) (unsigned-byte-p 8 b6) (unsigned-byte-p 8 b7) (unsigned-byte-p 8 b8) (unsigned-byte-p 8 b9) (unsigned-byte-p 8 b10) (unsigned-byte-p 8 b11) (unsigned-byte-p 8 b12) (unsigned-byte-p 8 b13) (unsigned-byte-p 8 b14) (unsigned-byte-p 8 b15))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                       (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
                       (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0)
                       (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
                       (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)))))
  :g-bindings (gl::auto-bindings (:nat a0 8) (:nat a1 8) (:nat a2 8) (:nat a3 8) (:nat a4 8) (:nat a5 8) (:nat a6 8) (:nat a7 8) (:nat a8 8) (:nat a9 8) (:nat a10 8) (:nat a11 8) (:nat a12 8) (:nat a13 8) (:nat a14 8) (:nat a15 8) (:nat b0 8) (:nat b1 8) (:nat b2 8) (:nat b3 8) (:nat b4 8) (:nat b5 8) (:nat b6 8) (:nat b7 8) (:nat b8 8) (:nat b9 8) (:nat b10 8) (:nat b11 8) (:nat b12 8) (:nat b13 8) (:nat b14 8) (:nat b15 8)))

;; ---------------------------------------------------------------------------
;; ROADMAP -- remaining for  key_schedule core == bitslice(keyexpansion):
;; 1. keystep's step-star-c (c=0..9): krw8(bitslice(b,b),c) =
;;    bitslice(kr-spec-bytes(b,xpow c), same), for any 16-byte b -- GL directly
;;    over the pure krw8; kr-spec-bytes iterated = Kestrel keyexpansion is
;;    validated in keycore.
;; 2. The 10-round chain (keyexpand): the seed writes window 0 = bitslice(key,
;;    key); sched-loop0-step advances rkeys by kround per round; kround-window
;;    + step-star extend the invariant while kround-frame-below preserves the
;;    earlier windows and wstatep-of-krw8 keeps the new window a wstate.  So
;;    inv_bitslice(window r) = kk(r) for r=0..10.
;; 3. Combine with aes_fixslice_keyschedule's fold layer (sub_bytes_nots = xor63,
;;    inv_shift_rows_i = invshiftrows^i) for the full aes128_key_schedule
;;    correspondence (keyasm/keyread/keymain).
