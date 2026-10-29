; Phase 6 -- DECRYPT SIDE, part 6: THE SPEC HOP, and DECRYPT-CORRECT.
;
; aes_fixslice_decladder ended with decrypt_block == (ok (z-final key b)) --
; a statement with no extracted function left in it: z-final is built from
; byte ops DEFINED over the Kestrel spec (imc0-bytes is copy-state-to-array
; o aes::invmixcolumns o copyarraytostate, invsbox16 is the bytewise
; aes::invsbox map, etc.) and the kk-iter round keys, already bridged to
; aes::keyexpansion.  What remains is a fact about the audited spec alone:
; its InvCipher loop, read through the 16-byte flat representation, IS the
; z-chain recurrence.  Same three ingredient families as the encrypt hop,
; all equational (no GL, nothing bit-level):
;   1. copyarraytostate commutes over each inverse spec round op;
;   2. the spec's subrange key windows are bytes->cols of kk-iter
;      (copied local block from aes_fixslice_final);
;   3. one round-by-round alignment of invapply-rounds with z-chain
;      (invapply-round r = isr; invsb; ark(kk_r); imc  --  exactly one
;      z-chain step with r = 10 - k, applied innermost-first).
; Then the extracted decrypt_block -- and the full extracted decrypt
; driver, key schedule included -- equals aes::aes-128-decrypt.
(in-package "ACL2")
(include-book "aes_fixslice_decladder")
(include-book "aes_fixslice_final")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "kestrel/lists-light/subrange" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))
(local (in-theory (disable keyexpansion-open kk-iter-step ks-decomp enc-collapse dec-collapse
                           window-bitslice-0 window-bitslice-1 window-bitslice-2
                           window-bitslice-3 window-bitslice-4 window-bitslice-5
                           window-bitslice-6 window-bitslice-7 window-bitslice-8
                           window-bitslice-9 window-bitslice-10)))

;; ---------------------------------------------------------------------------
;; (1) the three inverse-op commutes over the flat representation.
(defthm invshiftrows-copyarr-commute
  (implies (aes::inp x)
           (equal (aes::invshiftrows (aes::copyarraytostate x))
                  (aes::copyarraytostate (inv-shift-rows-1-bytes x))))
  :hints (("Goal" :in-theory (e/d (inv-shift-rows-1-bytes copyarraytostate-of-copy-state-to-array)
                                  (aes::invshiftrows aes::copyarraytostate
                                   aes::copy-state-to-array aes::inp nth)))))
(defthm invmixcolumns-copyarr-commute
  (implies (aes::inp x)
           (equal (aes::invmixcolumns (aes::copyarraytostate x))
                  (aes::copyarraytostate (imc0-bytes x))))
  :hints (("Goal" :in-theory (e/d (imc0-bytes copyarraytostate-of-copy-state-to-array)
                                  (aes::invmixcolumns aes::copyarraytostate
                                   aes::copy-state-to-array aes::inp nth)))))
(defthm invsubbytes-copyarr-commute
  (implies (aes::inp b)
           (equal (aes::invsubbytes (aes::copyarraytostate b))
                  (aes::copyarraytostate (invsbox16 b))))
  :hints (("Goal" :in-theory (enable aes::invsubbytes aes::copyarraytostate
                                     aes::array-elem-2d invsbox16))))

;; ---------------------------------------------------------------------------
;; (2) the spec's subrange key windows are bytes->cols of kk-iter (from
;; aes_fixslice_final, verbatim -- they are local there).

(local (defthm len-of-keyexpansion
  (implies (aes::inp key) (equal (len (aes::keyexpansion key 4)) 44))
  :hints (("Goal" :use (:instance aes::expanded-keyp-of-keyexpansion (aes::nk 4) (aes::key key))
           :in-theory (e/d (aes::expanded-keyp acl2::2d-bv-arrayp aes::keyp)
                           (aes::keyexpansion aes::keyexpansionloop1 aes::keyexpansionloop2))))))
(local (defun kw4 (l i)
  (list (nth i l) (nth (+ i 1) l) (nth (+ i 2) l) (nth (+ i 3) l))))
(local (defthm len-of-kw4 (equal (len (kw4 l i)) 4)))
(local (defthm true-listp-of-kw4 (true-listp (kw4 l i))))
(local (defthm nth-of-kw4
  (implies (and (natp n) (< n 4)) (equal (nth n (kw4 l i)) (nth (+ i n) l)))
  :hints (("Goal" :in-theory (enable kw4)
           :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3))))))
(local (defthm subrange-is-kw4
  (implies (and (natp i) (<= (+ i 4) (len w)))
           (equal (acl2::subrange i (+ 3 i) w) (kw4 w i)))
  :hints ((acl2::equal-by-nths-hint)
          '(:in-theory (e/d (acl2::nth-of-subrange acl2::len-of-subrange
                             nth-of-kw4 len-of-kw4 true-listp-of-kw4)
                            (kw4 nth acl2::subrange))))))
(local (defthm bytes->cols-of-kk-of-w
  (implies (and (aes::inp key) (natp r) (<= r 10))
           (equal (bytes->cols (kk-of-w (aes::keyexpansion key 4) r))
                  (kw4 (aes::keyexpansion key 4) (* 4 r))))
  :hints (("Goal"
           :use ((:instance exp-row-wordp (j (* 4 r)))
                 (:instance exp-row-wordp (j (+ 1 (* 4 r))))
                 (:instance exp-row-wordp (j (+ 2 (* 4 r))))
                 (:instance exp-row-wordp (j (+ 3 (* 4 r))))
                 (:instance expand-len-4 (x (nth (* 4 r) (aes::keyexpansion key 4))))
                 (:instance expand-len-4 (x (nth (+ 1 (* 4 r)) (aes::keyexpansion key 4))))
                 (:instance expand-len-4 (x (nth (+ 2 (* 4 r)) (aes::keyexpansion key 4))))
                 (:instance expand-len-4 (x (nth (+ 3 (* 4 r)) (aes::keyexpansion key 4)))))
           :in-theory (e/d (bytes->cols kk-of-w acl2::bv-arrayp keyexpansion-open)
                           (aes::keyexpansion aes::inp nth exp-row-wordp))))))

;; per-literal window rules (the goals carry literal indices).
(local (defthm ww-0
  (implies (aes::inp key)
           (equal (acl2::subrange 0 3 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 0))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 0) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 0))
                 (:instance kk-iter-is-keyexpansion (r 0)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-1
  (implies (aes::inp key)
           (equal (acl2::subrange 4 7 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 1))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 4) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 1))
                 (:instance kk-iter-is-keyexpansion (r 1)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-2
  (implies (aes::inp key)
           (equal (acl2::subrange 8 11 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 2))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 8) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 2))
                 (:instance kk-iter-is-keyexpansion (r 2)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-3
  (implies (aes::inp key)
           (equal (acl2::subrange 12 15 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 3))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 12) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 3))
                 (:instance kk-iter-is-keyexpansion (r 3)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-4
  (implies (aes::inp key)
           (equal (acl2::subrange 16 19 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 4))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 16) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 4))
                 (:instance kk-iter-is-keyexpansion (r 4)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-5
  (implies (aes::inp key)
           (equal (acl2::subrange 20 23 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 5))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 20) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 5))
                 (:instance kk-iter-is-keyexpansion (r 5)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-6
  (implies (aes::inp key)
           (equal (acl2::subrange 24 27 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 6))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 24) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 6))
                 (:instance kk-iter-is-keyexpansion (r 6)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-7
  (implies (aes::inp key)
           (equal (acl2::subrange 28 31 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 7))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 28) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 7))
                 (:instance kk-iter-is-keyexpansion (r 7)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-8
  (implies (aes::inp key)
           (equal (acl2::subrange 32 35 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 8))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 32) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 8))
                 (:instance kk-iter-is-keyexpansion (r 8)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-9
  (implies (aes::inp key)
           (equal (acl2::subrange 36 39 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 9))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 36) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 9))
                 (:instance kk-iter-is-keyexpansion (r 9)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))
(local (defthm ww-10
  (implies (aes::inp key)
           (equal (acl2::subrange 40 43 (aes::keyexpansion key 4))
                  (bytes->cols (kk-iter key 10))))
  :hints (("Goal"
           :use ((:instance subrange-is-kw4 (i 40) (w (aes::keyexpansion key 4)))
                 (:instance bytes->cols-of-kk-of-w (r 10))
                 (:instance kk-iter-is-keyexpansion (r 10)))
           :in-theory (e/d (len-of-keyexpansion)
                           (kw4 bytes->cols kk-of-w kk-iter acl2::subrange
                            aes::keyexpansion aes::inp nth kk-iter-is-keyexpansion))))))

;; ---------------------------------------------------------------------------
;; (3) each spec inverse round, through the representation, is one z-chain
;; step: invapply-round (10-k) advances z-chain from k-1 to k.
(local (defthm spec-dround-1
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 9 (aes::copyarraytostate (z-chain key b 0)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 1))))
  :hints (("Goal" :expand ((z-chain key b 1))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-2
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 8 (aes::copyarraytostate (z-chain key b 1)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 2))))
  :hints (("Goal" :expand ((z-chain key b 2))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-3
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 7 (aes::copyarraytostate (z-chain key b 2)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 3))))
  :hints (("Goal" :expand ((z-chain key b 3))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-4
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 6 (aes::copyarraytostate (z-chain key b 3)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 4))))
  :hints (("Goal" :expand ((z-chain key b 4))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-5
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 5 (aes::copyarraytostate (z-chain key b 4)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 5))))
  :hints (("Goal" :expand ((z-chain key b 5))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-6
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 4 (aes::copyarraytostate (z-chain key b 5)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 6))))
  :hints (("Goal" :expand ((z-chain key b 6))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-7
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 3 (aes::copyarraytostate (z-chain key b 6)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 7))))
  :hints (("Goal" :expand ((z-chain key b 7))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-8
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 2 (aes::copyarraytostate (z-chain key b 7)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 8))))
  :hints (("Goal" :expand ((z-chain key b 8))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-dround-9
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-round 1 (aes::copyarraytostate (z-chain key b 8)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (z-chain key b 9))))
  :hints (("Goal" :expand ((z-chain key b 9))
           :in-theory (e/d (aes::invapply-round)
                           (aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm drounds-chain
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invapply-rounds 9 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                  (aes::copyarraytostate (z-chain key b 9))))
  :hints (("Goal" :do-not-induct t
           :expand ((aes::invapply-rounds 9 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 8 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 7 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 6 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 5 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 4 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 3 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 2 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 1 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4)
                    (aes::invapply-rounds 0 (aes::copyarraytostate (z-chain key b 0)) (aes::keyexpansion key 4) 4))
           :in-theory (e/d ()
                           (aes::invapply-round aes::invapply-rounds aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))

;; ---------------------------------------------------------------------------
;; (4) the hop, and THE MAIN THEOREMS.
(local (defthm z0-fold
  (equal (xorbytes b (kk-iter key 10)) (z-chain key b 0))
  :hints (("Goal" :expand ((z-chain key b 0))))))
;; stated in the invsbox16-of-isr1 normal form the goals reach.
(local (defthm zfin-fold
  (implies (and (aes::inp key) (aes::inp b))
           (equal (xorbytes (inv-shift-rows-1-bytes (invsbox16 (z-chain key b 9))) (kk-iter key 0))
                  (z-final key b)))
  :hints (("Goal" :expand ((z-final key b))
           :use ((:instance invsbox16-of-isr1 (b (z-chain key b 9))))
           :in-theory (e/d () (invsbox16-of-isr1 z-chain kk-iter invsbox16
                               inv-shift-rows-1-bytes xorbytes aes::inp nth))))))
(defthm invcipher-is-z-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::invcipher b (aes::keyexpansion key 4) 4)
                  (z-final key b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes::invcipher-core z0-fold zfin-fold)
                           (aes::invapply-round aes::invapply-rounds aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

(defthm z-final-is-aes-128-decrypt
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::aes-128-decrypt b key) (z-final key b)))
  :hints (("Goal" :in-theory (e/d () (aes::invcipher aes::invapply-round aes::invapply-rounds aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

;; The extracted decrypt_block, on the extracted key schedule, computes
;; the audited Kestrel AES-128 inverse cipher -- for ALL keys and blocks.
(defthm decrypt-block-correct
  (implies (and (aes::inp key) (aes::inp block))
           (equal (aes-fixslice-encrypt-decrypt-block 100
                    (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) block)
                  (ok (aes::aes-128-decrypt block key))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance decrypt-block-is-z-final (b block))
                 (:instance z-final-is-aes-128-decrypt (b block)))
           :in-theory (e/d () (aes-fixslice-encrypt-decrypt-block
                               aes-fixslice-encrypt-aes128-key-schedule
                               decrypt-block-is-z-final z-final-is-aes-128-decrypt
                               aes::aes-128-decrypt aes::invcipher aes::invapply-round aes::invapply-rounds aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

;; THE THEOREM: the extracted RustCrypto fixslice decrypt -- key schedule
;; and inverse cipher, exactly as extracted by the Aeneas ACL2 backend --
;; equals the audited Kestrel AES-128 inverse spec, for all 16-byte keys
;; and blocks.
(defthm decrypt-correct
  (implies (and (aes::inp key) (aes::inp block))
           (equal (aes-fixslice-encrypt-decrypt 100 key block)
                  (ok (aes::aes-128-decrypt block key))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes128-key-schedule-ok decrypt-block-correct)
                           (aes-fixslice-encrypt-decrypt-block
                            aes-fixslice-encrypt-aes128-key-schedule
                            aes::aes-128-decrypt aes::invcipher aes::invapply-round aes::invapply-rounds aes::invsubbytes aes::invshiftrows aes::invmixcolumns aes::addroundkey aes::subbytes aes::shiftrows aes::mixcolumns aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion z-chain z-final kk-iter invsbox16 map-invsbox16 inv-shift-rows-1-bytes inv-shift-rows-2-bytes inv-shift-rows-3-bytes shift-rows-2-bytes imc0-bytes imc1-bytes imc2-bytes imc3-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))
