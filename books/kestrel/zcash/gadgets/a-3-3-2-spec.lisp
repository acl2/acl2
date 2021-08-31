; Specification of the gadget in [ZPS:A.3.3.2].

(in-package "ZCASH")

(include-book "a-3-3-1-spec")

(define [de]compress-precond (u~)
  :guard (fep u~ (jubjub-q))
  (bitp u~))

;; Checks that (u,v) is on the curve.  Also checks that, of the (at most) two
;; possible u's such that (u,v) is on the curve, u has least significant bit
;; u~.  Usually for a given v value, there are two u values with opposite
;; polarity such that (u,v) is on the curve.  Then u~ distinguishes between
;; them.  That is, we can "compress" (u,v) into (u~,v) by cutting down u to
;; only its least significant bit, u~.  And we can later "decompress" to
;; recover u by choosing the u value whose least significant bit is u~.
(define [de]compress-spec (u v u~)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q))
              (fep u~ (jubjub-q))
              ([de]compress-precond u~))
  (and (affine-edwards-spec u v)
       (equal u~ (mod u 2))
       ;; No range check is needed here.  That is an implementation detail of
       ;; the R1CS, to ensure we get the right unpacking.
       ;; (<= u (1- (jubjub-q)))
       ))
