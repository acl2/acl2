; Phase 6 -- DECRYPT SIDE, part 1a: byte-level specs for the inverse ops.
; inv_sub_bytes    : x |-> invsbox[x ^ 0x63] (affine constant on the INPUT
;                    of the inverse circuit; compensated by the schedule's
;                    1..11 NOTs adjustment)
; inv_mix_columns_c: invshiftrows^c . invmixcolumns . shiftrows^c through
;                    the packing (forward frames, inverse core)
; Probed by execution, certified by GL in aes_fixslice_invops{,2,3} -- a
; minimal-include home so those heavy BDD books load slim sessions.
(in-package "ACL2")
(include-book "aes_fixslice_correspondence")

(defund map-invsbox16 (b)
  (list (nth (logxor (nth 0 b) #x63) (aes::invsbox))
        (nth (logxor (nth 1 b) #x63) (aes::invsbox))
        (nth (logxor (nth 2 b) #x63) (aes::invsbox))
        (nth (logxor (nth 3 b) #x63) (aes::invsbox))
        (nth (logxor (nth 4 b) #x63) (aes::invsbox))
        (nth (logxor (nth 5 b) #x63) (aes::invsbox))
        (nth (logxor (nth 6 b) #x63) (aes::invsbox))
        (nth (logxor (nth 7 b) #x63) (aes::invsbox))
        (nth (logxor (nth 8 b) #x63) (aes::invsbox))
        (nth (logxor (nth 9 b) #x63) (aes::invsbox))
        (nth (logxor (nth 10 b) #x63) (aes::invsbox))
        (nth (logxor (nth 11 b) #x63) (aes::invsbox))
        (nth (logxor (nth 12 b) #x63) (aes::invsbox))
        (nth (logxor (nth 13 b) #x63) (aes::invsbox))
        (nth (logxor (nth 14 b) #x63) (aes::invsbox))
        (nth (logxor (nth 15 b) #x63) (aes::invsbox))))
(defund imc0-bytes (b)
  (aes::copy-state-to-array (aes::invmixcolumns (aes::copyarraytostate b))))
(defund imc1-bytes (b)
  (aes::copy-state-to-array (aes::invshiftrows (aes::invmixcolumns (aes::shiftrows (aes::copyarraytostate b))))))
(defund imc2-bytes (b)
  (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::invmixcolumns (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b))))))))
(defund imc3-bytes (b)
  (aes::copy-state-to-array (aes::invshiftrows (aes::invshiftrows (aes::invshiftrows (aes::invmixcolumns (aes::shiftrows (aes::shiftrows (aes::shiftrows (aes::copyarraytostate b))))))))))
