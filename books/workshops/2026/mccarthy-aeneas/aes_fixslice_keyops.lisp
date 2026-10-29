; Phase 4 -- key-schedule OP LAYER: every operation the fixslice key schedule
; performs on the 88-word rkeys array is a pure WINDOW TRANSFORM, verified for
; ALL inputs.  Built on aes_fixslice_keychain's loop lemmas (write8/memshift32/
; xor_columns == explicit window specs, with nth read-through).  Here each
; read-modify-write op (read8 ; f ; write8) is shown equal to a single w8-spec
; window update:
;   memshift32  : copies rkeys[off..off+8) into rkeys[off+8..off+16)
;   sub_bytes_at / sub_bytes_nots_at : window := (sub_bytes[_nots]) of window
;   add_rcon    : window := arc-list of window (the bitsliced Rcon bit-flips)
;   xor_columns : window := the parallel-prefix column recurrence (xc-spec)
; The structural/nonlinear obligations (the Boyar-Peralta S-box returns a
; wstate; sub_bytes_nots and add_round_constant_bit likewise) are discharged by
; GL over one 8-word window and lifted to any wstate by expand-len-8 -- GL
; confined to the irreducible bit-level facts, the rest structured rewriting.
; Composing these into one key_round and chaining the 10 rounds is the roadmap
; at the end.
(in-package "ACL2")
(include-book "aes_fixslice_keychain")
(include-book "aes_fixslice_round")   ; wstatep, expand-len-8
(local (include-book "std/lists/nth" :dir :system))        ; equal-by-nths-hint
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
;; std/lists/nth rewrites (nth 0 s) -> (car s), which breaks the :use GL
;; instances below (stated with (nth 0 s)); keep nth indices literal.
(local (in-theory (disable nth-when-zp)))

(gl::def-gl-thm sub-bytes-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3)
            (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-sub-bytes (list w0 w1 w2 w3 w4 w5 w6 w7))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes (list w0 w1 w2 w3 w4 w5 w6 w7)))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32)
                                 (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))

(defthm result-kind-of-sub-bytes-wstate
  (implies (wstatep s) (equal (result-kind (aes-fixslice-encrypt-sub-bytes s)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (sub-bytes-struct-gl aes-fixslice-encrypt-sub-bytes nth))
           :use (:instance sub-bytes-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

(defthm wstatep-of-sub-bytes
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (sub-bytes-struct-gl aes-fixslice-encrypt-sub-bytes nth))
           :use (:instance sub-bytes-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(defthm len-when-wstatep (implies (wstatep x) (equal (len x) 8))
  :hints (("Goal" :in-theory (enable wstatep))))
(defthm true-listp-when-wstatep (implies (wstatep x) (true-listp x))
  :hints (("Goal" :in-theory (enable wstatep))))

;; sub_bytes_nots : wstate -> wstate, never fails
(gl::def-gl-thm sub-bytes-nots-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3)
            (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-sub-bytes-nots (list w0 w1 w2 w3 w4 w5 w6 w7))) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots (list w0 w1 w2 w3 w4 w5 w6 w7)))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32)
                                 (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32)))
(defthm result-kind-of-sub-bytes-nots-wstate
  (implies (wstatep s) (equal (result-kind (aes-fixslice-encrypt-sub-bytes-nots s)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (sub-bytes-nots-struct-gl aes-fixslice-encrypt-sub-bytes-nots nth))
           :use (:instance sub-bytes-nots-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(defthm wstatep-of-sub-bytes-nots
  (implies (wstatep s) (wstatep (result-ok->val (aes-fixslice-encrypt-sub-bytes-nots s))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (sub-bytes-nots-struct-gl aes-fixslice-encrypt-sub-bytes-nots nth))
           :use (:instance sub-bytes-nots-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

;; add_round_constant_bit : wstate x bit(<8) -> wstate, never fails
(gl::def-gl-thm add-rc-bit-struct-gl
  :hyp (and (unsigned-byte-p 32 w0) (unsigned-byte-p 32 w1) (unsigned-byte-p 32 w2) (unsigned-byte-p 32 w3)
            (unsigned-byte-p 32 w4) (unsigned-byte-p 32 w5) (unsigned-byte-p 32 w6) (unsigned-byte-p 32 w7)
            (unsigned-byte-p 3 bit))
  :concl (and (equal (result-kind (aes-fixslice-encrypt-add-round-constant-bit (list w0 w1 w2 w3 w4 w5 w6 w7) bit)) :ok)
              (wstatep (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit (list w0 w1 w2 w3 w4 w5 w6 w7) bit))))
  :g-bindings (gl::auto-bindings (:nat w0 32) (:nat w1 32) (:nat w2 32) (:nat w3 32)
                                 (:nat w4 32) (:nat w5 32) (:nat w6 32) (:nat w7 32) (:nat bit 3)))
(defthm result-kind-of-add-rc-bit-wstate
  (implies (and (wstatep s) (unsigned-byte-p 3 bit))
           (equal (result-kind (aes-fixslice-encrypt-add-round-constant-bit s bit)) :ok))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (add-rc-bit-struct-gl aes-fixslice-encrypt-add-round-constant-bit nth))
           :use (:instance add-rc-bit-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))
(defthm wstatep-of-add-rc-bit
  (implies (and (wstatep s) (unsigned-byte-p 3 bit))
           (wstatep (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s bit))))
  :hints (("Goal" :in-theory (e/d (expand-len-8 wstatep)
                                  (add-rc-bit-struct-gl aes-fixslice-encrypt-add-round-constant-bit nth))
           :use (:instance add-rc-bit-struct-gl (w0 (nth 0 s)) (w1 (nth 1 s)) (w2 (nth 2 s)) (w3 (nth 3 s))
                           (w4 (nth 4 s)) (w5 (nth 5 s)) (w6 (nth 6 s)) (w7 (nth 7 s))))))

;; ===== rd8 read-through helpers for composing the key_round ops =====
(defthm rd8-of-w8spec-same     ; read the just-written window
  (implies (and (natp off) (true-listp s) (equal (len s) 8))
           (equal (rd8 (w8-spec 0 8 rkeys off s) off) s))
  :hints (("Goal" :in-theory (e/d (rd8 expand-len-8) (w8-spec nth)))))
(defthm rd8-of-w8spec-frame    ; a disjoint window is unchanged
  (implies (and (natp off) (natp p) (or (<= (+ off 8) p) (<= (+ p 8) off)))
           (equal (rd8 (w8-spec 0 8 rkeys p s) off) (rd8 rkeys off)))
  :hints (("Goal" :in-theory (e/d (rd8) (w8-spec nth)))))
(defthm rd8-of-msspec-dst      ; memshift copies src-window into dst-window
  (implies (natp src)
           (equal (rd8 (ms-spec 0 8 buffer src (+ src 8)) (+ src 8)) (rd8 buffer src)))
  :hints (("Goal" :in-theory (e/d (rd8) (ms-spec nth)))))
(defthm rd8-of-msspec-frame    ; below the dst-window, unchanged
  (implies (and (natp src) (natp off) (<= (+ off 8) (+ src 8)))
           (equal (rd8 (ms-spec 0 8 buffer src (+ src 8)) off) (rd8 buffer off)))
  :hints (("Goal" :in-theory (e/d (rd8) (ms-spec nth)))))
(defthm len-of-w8spec-88
  (implies (and (natp off) (<= (+ off 8) (len rkeys))) (equal (len (w8-spec 0 8 rkeys off s)) (len rkeys))))
(defthm len-of-msspec-88
  (implies (and (natp src) (<= (+ src 16) (len buffer))) (equal (len (ms-spec 0 8 buffer src (+ src 8))) (len buffer))))

;; ===== add_rcon window transform =====
(defthm true-listp-of-w8-spec
  (implies (true-listp rkeys) (true-listp (w8-spec i e rkeys off s))))
(defthm w8-spec-collapse       ; two writes to the same window: outer wins
  (implies (and (natp off) (<= (+ off 8) (len rkeys)) (true-listp rkeys))
           (equal (w8-spec 0 8 (w8-spec 0 8 rkeys off s1) off s2)
                  (w8-spec 0 8 rkeys off s2)))
  :hints ((equal-by-nths-hint)
          '(:in-theory (disable w8-spec))))

(defund arc-list (s8 c)
  (if (< c 8)
      (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s8 c))
    (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit
      (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit
        (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit
          (result-ok->val (aes-fixslice-encrypt-add-round-constant-bit s8 (- c 8)))
          (- c 7)))
        (- c 5)))
      (- c 4)))))

(defthm wstatep-of-arc-list
  (implies (and (wstatep s8) (natp c) (< c 12)) (wstatep (arc-list s8 c)))
  :hints (("Goal" :in-theory (e/d (arc-list unsigned-byte-p)
                                  (aes-fixslice-encrypt-add-round-constant-bit wstatep)))))

;; ROADMAP (next): compose these window transforms into one key_round --
;;   key_round(rkeys,off,c) writes only rkeys[off+8..off+16) with the
;;   off-independent transform  krw8(s8,c) = xor_columns_word_i(s8_i,
;;     arc(sub_bytes_nots(sub_bytes(s8)),c), ror_distance(1,3))  (i=0..7),
;; via memshift(is-msspec) ; sub_bytes_at ; sub_bytes_nots_at ; add_rcon(is) ;
;; xor_columns(is-xcspec), threading wstatep through rd8-of-*-{same,frame}.
;; Then chain the 10 concrete offsets and lift with the keycore step cruxes.
