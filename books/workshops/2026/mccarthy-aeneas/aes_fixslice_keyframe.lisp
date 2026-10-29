; Phase 4 -- key schedule frame plumbing.
;
; Isolated into its own book so that arithmetic-5 stays LOCAL here: the rd8
; index reasoning below wants arithmetic-5, but arithmetic-5's aggressive
; subtraction/nonlinear case splits explode the wok inductions in keyexpand.
; Keeping it local means keyexpand can run the offset inductions on plain
; ground-zero linear arithmetic.
;
; Proven here:
;   rd8-of-kround-below : an 8-word read at or below off is unchanged by a
;                         kround at off (which writes only [off+8, off+16))
(in-package "ACL2")
(include-book "aes_fixslice_keystep")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep)))

;; An 8-word read at offset k8 <= off is untouched by a kround at off.
;; Proven by nths + kround-frame-below.
(defthm rd8-of-kround-below
  (implies (and (natp off) (<= (+ off 16) (len rkeys))
                (natp k8) (<= k8 off))
           (equal (rd8 (kround rkeys off c) k8) (rd8 rkeys k8)))
  :hints (("Goal" :in-theory (e/d (rd8) (kround nth)))))
