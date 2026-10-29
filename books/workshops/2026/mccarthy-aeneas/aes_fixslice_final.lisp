; Phase 5 -- cipher side, part 8: THE SPEC HOP, and the MAIN THEOREM.
;
; aes_fixslice_ladder ended with encrypt_block == (ok (y-final key b)) --
; a statement with no extracted function left in it: y-final is built from
; byte ops DEFINED over the Kestrel spec (kmix-bytes is copy-state-to-array
; o aes::mixcolumns o copyarraytostate, etc.) and the kk-iter round keys,
; already bridged to aes::keyexpansion.  What remains is a fact about the
; audited spec alone: its cipher loop, read through the 16-byte flat
; representation, IS the y-chain recurrence.  Three ingredient families,
; all equational (no GL, nothing bit-level):
;   1. copyarraytostate commutes over each spec round op (definition
;      unfolding + the copy round trip);
;   2. the spec's subrange key windows are bytes->cols of kk-iter
;      (list indexing + kk-iter-is-keyexpansion);
;   3. one round-by-round alignment of apply-rounds with y-chain.
; Then the extracted encrypt_block -- and the full extracted encrypt
; driver, key schedule included -- equals aes::aes-128-encrypt.
(in-package "ACL2")
(include-book "aes_fixslice_ladder")
(include-book "aes_fixslice_keymain")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "kestrel/lists-light/subrange" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))
(local (in-theory (disable keyexpansion-open kk-iter-step ks-decomp enc-collapse
                           window-bitslice-0 window-bitslice-1 window-bitslice-2
                           window-bitslice-3 window-bitslice-4 window-bitslice-5
                           window-bitslice-6 window-bitslice-7 window-bitslice-8
                           window-bitslice-9 window-bitslice-10)))

;; ---------------------------------------------------------------------------
;; (1) representation round trip and the two missing commute rules.
(defthm copy-state-of-copyarr
  (implies (aes::inp b)
           (equal (aes::copy-state-to-array (aes::copyarraytostate b)) b))
  :hints (("Goal"
           :use ((:instance expand-len-16 (x b)))
           :in-theory (e/d (aes::copy-state-to-array aes::copyarraytostate
                            aes::array-elem-2d)
                           (aes::inp)))))
(defthm shiftrows-copyarr-commute
  (implies (aes::inp x)
           (equal (aes::shiftrows (aes::copyarraytostate x))
                  (aes::copyarraytostate (sr1-bytes x))))
  :hints (("Goal" :in-theory (e/d (sr1-bytes copyarraytostate-of-copy-state-to-array)
                                  (aes::shiftrows aes::copyarraytostate
                                   aes::copy-state-to-array aes::inp nth)))))
(defthm mixcolumns-copyarr-commute
  (implies (aes::inp x)
           (equal (aes::mixcolumns (aes::copyarraytostate x))
                  (aes::copyarraytostate (kmix-bytes x))))
  :hints (("Goal" :in-theory (e/d (kmix-bytes copyarraytostate-of-copy-state-to-array)
                                  (aes::mixcolumns aes::copyarraytostate
                                   aes::copy-state-to-array aes::inp nth)))))

;; ---------------------------------------------------------------------------
;; (2) the spec's subrange key windows are bytes->cols of kk-iter.
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
;; (3) each spec round, through the representation, is one y-chain step.
(local (defthm spec-round-1
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 1 (aes::copyarraytostate (y-chain key b 0)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 1))))
  :hints (("Goal" :expand ((y-chain key b 1))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-2
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 2 (aes::copyarraytostate (y-chain key b 1)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 2))))
  :hints (("Goal" :expand ((y-chain key b 2))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-3
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 3 (aes::copyarraytostate (y-chain key b 2)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 3))))
  :hints (("Goal" :expand ((y-chain key b 3))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-4
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 4 (aes::copyarraytostate (y-chain key b 3)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 4))))
  :hints (("Goal" :expand ((y-chain key b 4))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-5
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 5 (aes::copyarraytostate (y-chain key b 4)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 5))))
  :hints (("Goal" :expand ((y-chain key b 5))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-6
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 6 (aes::copyarraytostate (y-chain key b 5)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 6))))
  :hints (("Goal" :expand ((y-chain key b 6))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-7
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 7 (aes::copyarraytostate (y-chain key b 6)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 7))))
  :hints (("Goal" :expand ((y-chain key b 7))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-8
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 8 (aes::copyarraytostate (y-chain key b 7)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 8))))
  :hints (("Goal" :expand ((y-chain key b 8))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm spec-round-9
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-round 9 (aes::copyarraytostate (y-chain key b 8)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 9))))
  :hints (("Goal" :expand ((y-chain key b 9))
           :in-theory (e/d (aes::apply-round)
                           (aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))
(local (defthm rounds-chain
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::apply-rounds 1 9 (aes::copyarraytostate (y-chain key b 0)) 4 (aes::keyexpansion key 4))
                  (aes::copyarraytostate (y-chain key b 9))))
  :hints (("Goal" :do-not-induct t
           :expand ((aes::apply-rounds 1 9 (aes::copyarraytostate (y-chain key b 0)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 2 9 (aes::copyarraytostate (y-chain key b 1)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 3 9 (aes::copyarraytostate (y-chain key b 2)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 4 9 (aes::copyarraytostate (y-chain key b 3)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 5 9 (aes::copyarraytostate (y-chain key b 4)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 6 9 (aes::copyarraytostate (y-chain key b 5)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 7 9 (aes::copyarraytostate (y-chain key b 6)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 8 9 (aes::copyarraytostate (y-chain key b 7)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 9 9 (aes::copyarraytostate (y-chain key b 8)) 4 (aes::keyexpansion key 4))
                    (aes::apply-rounds 10 9 (aes::copyarraytostate (y-chain key b 9)) 4 (aes::keyexpansion key 4)))
           :in-theory (e/d () (aes::apply-round aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange))))))

;; ---------------------------------------------------------------------------
;; (4) the hop, and THE MAIN THEOREMS.
(local (defthm y0-fold
  (equal (xorbytes b (kk-iter key 0)) (y-chain key b 0))
  :hints (("Goal" :expand ((y-chain key b 0))))))
(local (defthm yfin-fold
  (equal (xorbytes (sr1-bytes (map-sbox16 (y-chain key b 9))) (kk-iter key 10))
         (y-final key b))
  :hints (("Goal" :expand ((y-final key b))))))
(defthm cipher-is-y-final
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::cipher b (aes::keyexpansion key 4) 4)
                  (y-final key b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes::cipher-core y0-fold yfin-fold)
                           (aes::apply-round aes::apply-rounds aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

(defthm y-final-is-aes-128-encrypt
  (implies (and (aes::inp key) (aes::inp b))
           (equal (aes::aes-128-encrypt b key) (y-final key b)))
  :hints (("Goal" :in-theory (e/d () (aes::cipher aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

;; The extracted encrypt_block, on the extracted key schedule, computes
;; the audited Kestrel AES-128 -- for ALL keys and blocks.
(defthm encrypt-block-correct
  (implies (and (aes::inp key) (aes::inp block))
           (equal (aes-fixslice-encrypt-encrypt-block 100
                    (result-ok->val (aes-fixslice-encrypt-aes128-key-schedule 100 key)) block)
                  (ok (aes::aes-128-encrypt block key))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance encrypt-block-is-y-final (b block))
                 (:instance y-final-is-aes-128-encrypt (b block)))
           :in-theory (e/d () (aes-fixslice-encrypt-encrypt-block
                               aes-fixslice-encrypt-aes128-key-schedule
                               encrypt-block-is-y-final y-final-is-aes-128-encrypt
                               y-final aes::aes-128-encrypt aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))

;; THE THEOREM: the extracted RustCrypto fixslice encrypt -- key schedule
;; and cipher, exactly as extracted by the Aeneas ACL2 backend -- equals
;; the audited Kestrel AES-128 spec, for all 16-byte keys and blocks.
(defthm encrypt-correct
  (implies (and (aes::inp key) (aes::inp block))
           (equal (aes-fixslice-encrypt-encrypt 100 key block)
                  (ok (aes::aes-128-encrypt block key))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (aes128-key-schedule-ok encrypt-block-correct)
                           (aes-fixslice-encrypt-encrypt-block
                            aes-fixslice-encrypt-aes128-key-schedule
                            aes::aes-128-encrypt aes::subbytes aes::shiftrows aes::mixcolumns aes::addroundkey aes::copyarraytostate aes::copy-state-to-array aes::keyexpansion y-chain y-final kk-iter map-sbox16 sr1-bytes kmix-bytes xorbytes bytes->cols aes::inp nth acl2::subrange)))))
