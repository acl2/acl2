; Phase 4 -- round-induction core: spec-level commutation + telescoping.
;
; These are the algebraic facts (all PURE REWRITING over the Kestrel spec, no
; GL) that make the ShiftRows fold telescope. With the per-op correspondences
; (aes_fixslice_shiftrows), applying shiftrows^i to the fixslice mix_columns_i
; effect cancels its invshiftrows^i conjugation, leaving MixColumns in the
; shiftrows^i frame -- exactly the spec's round op. Together with SubBytes/
; ShiftRows commuting, the change of variable y_r = shiftrows^r(phi(state_r))
; collapses the fixslice recurrence onto the spec's.
(in-package "ACL2")
(include-book "aes_fixslice_shiftrows")

;; ---- spec-level commutation lemmas ----
(defthm subbytes-of-shiftrows
  (implies (aes::statep s)
           (equal (aes::subbytes (aes::shiftrows s)) (aes::shiftrows (aes::subbytes s))))
  :hints (("Goal" :in-theory (e/d (aes::subbytes aes::shiftrows aes::array-elem-2d
                                   expand-len-4 acl2::2d-bv-arrayp acl2::bv-arrayp) (nth)))))
(defthm shiftrows-of-invshiftrows
  (implies (aes::statep s) (equal (aes::shiftrows (aes::invshiftrows s)) s))
  :hints (("Goal" :in-theory (e/d (aes::shiftrows aes::invshiftrows aes::array-elem-2d
                                   expand-len-4 acl2::2d-bv-arrayp acl2::bv-arrayp) (nth)))))
(defthm invshiftrows-of-shiftrows
  (implies (aes::statep s) (equal (aes::invshiftrows (aes::shiftrows s)) s))
  :hints (("Goal" :in-theory (e/d (aes::shiftrows aes::invshiftrows aes::array-elem-2d
                                   expand-len-4 acl2::2d-bv-arrayp acl2::bv-arrayp) (nth)))))
(defthm shiftrows-period-4
  (implies (aes::statep s)
           (equal (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::shiftrows s)))) s))
  :hints (("Goal" :in-theory (e/d (aes::shiftrows aes::array-elem-2d
                                   expand-len-4 acl2::2d-bv-arrayp acl2::bv-arrayp) (nth)))))

;; statep-ness of the conjugated form, so the absorption lemmas' round-trip fires.
(defthm statep-of-shiftrows-gen
  (implies (aes::statep s) (aes::statep (aes::shiftrows s)))
  :hints (("Goal" :in-theory (enable aes::statep-of-shiftrows))))

;; Telescoping absorption i=1: shiftrows^1 cancels the invshiftrows^1 conjugation.
(defthm shiftrows-1-of-mix-columns-1
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (aes::shiftrows (fixslice->statep (result-ok->val (aes-fixslice-encrypt-mix-columns-1 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)) (aes::mixcolumns (aes::shiftrows (aes::copyarraytostate b0)))))
  :hints (("Goal" :in-theory (e/d (mix-columns-1-correspondence)
                                  (aes-fixslice-encrypt-mix-columns-1
                                   aes-fixslice-encrypt-bitslice fixslice->statep))
           :use ((:instance mix-columns-1-correspondence)))))

;; Telescoping absorption i=2: shiftrows^2 cancels the invshiftrows^2 conjugation.
(defthm shiftrows-2-of-mix-columns-2
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (aes::shiftrows (aes::shiftrows (fixslice->statep (result-ok->val (aes-fixslice-encrypt-mix-columns-2 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0))) (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0))))))
  :hints (("Goal" :in-theory (e/d (mix-columns-2-correspondence)
                                  (aes-fixslice-encrypt-mix-columns-2
                                   aes-fixslice-encrypt-bitslice fixslice->statep))
           :use ((:instance mix-columns-2-correspondence)))))

;; Telescoping absorption i=3: shiftrows^3 cancels the invshiftrows^3 conjugation.
(defthm shiftrows-3-of-mix-columns-3
  (implies (and (aes::inp b0) (aes::inp b1))
           (equal (aes::shiftrows (aes::shiftrows (aes::shiftrows (fixslice->statep (result-ok->val (aes-fixslice-encrypt-mix-columns-3 (result-ok->val (aes-fixslice-encrypt-bitslice (list 0 0 0 0 0 0 0 0) b0 b1)))) 0)))) (aes::mixcolumns (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b0)))))))
  :hints (("Goal" :in-theory (e/d (mix-columns-3-correspondence)
                                  (aes-fixslice-encrypt-mix-columns-3
                                   aes-fixslice-encrypt-bitslice fixslice->statep))
           :use ((:instance mix-columns-3-correspondence)))))
