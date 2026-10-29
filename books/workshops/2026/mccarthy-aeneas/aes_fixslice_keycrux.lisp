; Phase 4 -- key-schedule bridges: the window-read and bitslice facts the
; step/chain layers build on, lifted to all inputs.
;
;   take-nthcdr-is-rd8 : a (take 8 (nthcdr off .)) window read is rd8
;   wstatep-of-bitslice: bitslice of two inp blocks is a wstate (GL lifted)
;   rd8-of-append-8    : rd8 at 0 of (append s z) reads back a len-8 s
;
; (Historical note: this book once held the per-rcon key_round GL cruxes and
; their krw8 window rephrasings.  The upstream schedule now inlines the round
; in the rcon loop, and keystep's step-star-c GL theorems are stated directly
; over the pure krw8 -- so only the reusable bridges remain here.)
(in-package "ACL2")
(include-book "aes_fixslice_keyround")
(include-book "aes_fixslice_keycore")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable nth-when-zp len-when-wstatep true-listp-when-wstatep)))

(defthm take-nthcdr-is-rd8
  (implies (and (natp off) (<= (+ off 8) (len l)))
           (equal (take 8 (nthcdr off l)) (rd8 l off)))
  :hints ((equal-by-nths-hint)
          '(:in-theory (e/d (nth-of-rd8 nth-of-nthcdr nth-of-take len-of-rd8-8 true-listp-of-rd8) (rd8 nth)))))

;; bitslice of two 16-byte blocks is a wstate (8 u32) -- lift the GL fact to inp.
(defthm wstatep-of-bitslice
  (implies (and (aes::inp b0) (aes::inp b1))
           (wstatep (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1))))
  :hints (("Goal"
           :in-theory (e/d (expand-len-16)
                           (wstatep-of-bitslice-gl aes-fixslice-encrypt-bitslice wstatep nth aes::inp))
           :use (:instance wstatep-of-bitslice-gl
                  (a0 (nth 0 b0)) (a1 (nth 1 b0)) (a2 (nth 2 b0)) (a3 (nth 3 b0)) (a4 (nth 4 b0)) (a5 (nth 5 b0)) (a6 (nth 6 b0)) (a7 (nth 7 b0)) (a8 (nth 8 b0)) (a9 (nth 9 b0)) (a10 (nth 10 b0)) (a11 (nth 11 b0)) (a12 (nth 12 b0)) (a13 (nth 13 b0)) (a14 (nth 14 b0)) (a15 (nth 15 b0))
                  (b0 (nth 0 b1)) (b1 (nth 1 b1)) (b2 (nth 2 b1)) (b3 (nth 3 b1)) (b4 (nth 4 b1)) (b5 (nth 5 b1)) (b6 (nth 6 b1)) (b7 (nth 7 b1)) (b8 (nth 8 b1)) (b9 (nth 9 b1)) (b10 (nth 10 b1)) (b11 (nth 11 b1)) (b12 (nth 12 b1)) (b13 (nth 13 b1)) (b14 (nth 14 b1)) (b15 (nth 15 b1))))))

;; rd8 at 0 of a seeded array reads back the first window.
(defthm rd8-of-append-8
  (implies (and (true-listp s) (equal (len s) 8))
           (equal (rd8 (append s z) 0) s))
  :hints (("Goal" :in-theory (e/d (rd8 expand-len-8) (nth)))))
