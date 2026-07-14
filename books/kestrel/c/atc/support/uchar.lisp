; Rules about uchar functions
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/c/representation/integer-operations" :dir :system)
(include-book "kestrel/c/atc/let-designations" :dir :system) ; for assign and declar
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (enable uchar-integer-fix uchar-integerp char-bits uchar-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

(defthm <=-of-uchar-integer-fix-linear
  (<= (uchar-integer-fix x) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-uchar-integer-fix
  (implies (and (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (uchar-integer-fix x))))

(defthm <=-of-integer-from-uchar-linear
  (<= (integer-from-uchar x) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-uchar))))

(defthm unsigned-byte-p-of-integer-from-uchar
  (implies (and (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (integer-from-uchar x)))
  :hints (("Goal" :in-theory (enable integer-from-uchar))))

;; Seems ok to leave enabled.
;; Needed below.
;; The suffix -2 distinguishes this from a disabled rule in ATC -- just enable it here?
(defthm integer-from-sint-of-sint-from-uchar-2
  (equal (integer-from-sint (sint-from-uchar x))
         (integer-from-uchar x))
  :hints (("Goal" :in-theory (enable sint-from-uchar sint-integer-fix sint-integerp int-bits))))

;; We might like uchar-integerp-of-integer-from-sint-of-bitnot-uchar, but it is
;; not true, because the value can go negative.

;; bitand-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitand-uchar-uchar
  (uchar-integerp (integer-from-sint (bitand-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable bitand-uchar-uchar bitand-sint-sint sint-integer-fix sint-integerp int-bits))))

;; bitior-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitior-uchar-uchar
  (uchar-integerp (integer-from-sint (bitior-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable bitior-uchar-uchar bitior-sint-sint sint-integer-fix sint-integerp int-bits))))

;; bitxor-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitxor-uchar-uchar
  (uchar-integerp (integer-from-sint (bitxor-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable bitxor-uchar-uchar bitxor-sint-sint sint-integer-fix sint-integerp int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion, etc

;; Needed below (because constants must be at least size int):
(defthm uchar-from-uint-of-uint-from-integer
  (implies (uchar-integerp k)
           (equal (uchar-from-uint (uint-from-integer k))
                  (uchar-from-integer k)))
  :hints (("Goal" :in-theory (enable uchar-from-uint
                                     uint-from-integer
                                     uchar-from-integer
                                     uchar-from-integer-mod
                                     integer-from-uint
                                     uint-integerp
                                     int-bits
                                     uint-integer-fix))))

(defthmd equal-of-integer-from-uchar-and-integer-from-uchar
  (equal (equal (integer-from-uchar x) (integer-from-uchar y))
         (equal (uchar-fix x) (uchar-fix y)))
  :hints (("Goal" :in-theory (enable integer-from-uchar uchar-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants:

(defthmd uchar-from-integer-when-constant-dec
  (implies (and (syntaxp (quotep k))
                (uchar-integerp k))
           (equal (uchar-from-integer k)
                  (uchar-from-uint (uint-dec-const k))))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-integer-fix uint-integerp int-bits))))

(defthmd uchar-from-integer-when-constant-hex
  (implies (and (syntaxp (quotep k))
                (uchar-integerp k))
           (equal (uchar-from-integer k)
                  (uchar-from-uint (uint-hex-const k))))
  :hints (("Goal" :in-theory (enable uint-hex-const uint-integer-fix uint-integerp int-bits))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uchar-uchar-of-uchar-from-uint-of-uchar-dec-const-convert-to-hex-arg1
  (equal (bitand-uchar-uchar (uchar-from-uint (uint-dec-const x)) y)
         (bitand-uchar-uchar (uchar-from-uint (uint-hex-const x)) y))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uchar-uchar-of-uchar-from-uint-of-uchar-dec-const-convert-to-hex-arg2
  (equal (bitand-uchar-uchar x (uchar-from-uint (uint-dec-const y)))
         (bitand-uchar-uchar x (uchar-from-uint (uint-hex-const y))))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C operations:

;; Converts bitnot-uchar into lognot
;; sint is involved because bitnot-uchar returns a sint
(defthmd integer-from-sint-of-bitnot-uchar
  (equal (integer-from-sint (bitnot-uchar x))
         (lognot (integer-from-uchar x)))
  :hints (("Goal" :in-theory (enable bitnot-uchar
                                     bitnot-sint ; todo
                                     sint-from-uchar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitand-uchar-uchar into logand
;; sint is involved because bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitand-uchar-uchar
  (equal (integer-from-sint (bitand-uchar-uchar x y))
         (logand (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable bitand-uchar-uchar
                                     bitand-sint-sint ; todo
                                     sint-from-uchar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitior-uchar-uchar into logior
;; sint is involved because bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitior-uchar-uchar
  (equal (integer-from-sint (bitior-uchar-uchar x y))
         (logior (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable bitior-uchar-uchar
                                     bitior-sint-sint ; todo
                                     sint-from-uchar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitxor-uchar-uchar into logxor
;; sint is involved because bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitxor-uchar-uchar
  (equal (integer-from-sint (bitxor-uchar-uchar x y))
         (logxor (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable bitxor-uchar-uchar
                                     bitxor-sint-sint ; todo
                                     sint-from-uchar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-uchar-uchar into <
(defthmd boolean-from-sint-of-lt-uchar-uchar
  (equal (boolean-from-sint (lt-uchar-uchar x y))
         (< (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint lt-uchar-uchar lt-sint-sint))))

;; (theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uchar-uchar)
;;                                 (:rewrite boolean-from-sint-of-lt-uchar-uchar)))

;; Converts le-uchar-uchar into <=
(defthmd boolean-from-sint-of-le-uchar-uchar
  (equal (boolean-from-sint (le-uchar-uchar x y))
         (<= (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint le-uchar-uchar le-sint-sint))))

;; Converts gt-uchar-uchar into >
(defthmd boolean-from-sint-of-gt-uchar-uchar
  (equal (boolean-from-sint (gt-uchar-uchar x y))
         (> (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint gt-uchar-uchar gt-sint-sint))))

;; Converts ge-uchar-uchar into >=
(defthmd boolean-from-sint-of-ge-uchar-uchar
  (equal (boolean-from-sint (ge-uchar-uchar x y))
         (>= (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint ge-uchar-uchar ge-sint-sint))))

;; Converts eq-uchar-uchar into equal
(defthmd boolean-from-sint-of-eq-uchar-uchar
  (equal (boolean-from-sint (eq-uchar-uchar x y))
         (equal (integer-from-uchar x) (integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint eq-uchar-uchar eq-sint-sint))))

;; Converts ne-uchar-uchar into not equal
(defthmd boolean-from-sint-of-ne-uchar-uchar
  (equal (boolean-from-sint (ne-uchar-uchar x y))
         (not (equal (integer-from-uchar x) (integer-from-uchar y))))
  :hints (("Goal" :in-theory (enable boolean-from-sint ne-uchar-uchar ne-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

;; todo: more for other types, and other inner ops
(defthm lognot-sint-of-ne-uchar-uchar
  (equal (lognot-sint (ne-uchar-uchar x y))
         (eq-uchar-uchar x y))
  :hints (("Goal" :in-theory (enable ne-uchar-uchar eq-uchar-uchar ne-sint-sint eq-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable uchar-removal-rules.

(defthm ucharp-of-declar
  (equal (ucharp (declar x))
         (ucharp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm ucharp-of-assign
  (equal (ucharp (assign x))
         (ucharp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
;; todo: add to this
(deftheory uchar-removal-rules
    '(assign
      declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
      ;; integer-from-uint-of-add-uint-uint ; or we could introduce bvplus
      ;; integer-from-uint-of-sub-uint-uint
      integer-from-sint-of-bitnot-uchar
      integer-from-sint-of-bitand-uchar-uchar
      integer-from-sint-of-bitior-uchar-uchar
      integer-from-sint-of-bitxor-uchar-uchar
      ;; ;; integer-from-uint-of-shl-uint ; needed?
      ;; integer-from-uint-of-shl-uint-uint
      boolean-from-sint-of-lt-uchar-uchar
      ;; boolean-from-sint-of-le-uint-uint
      ;; boolean-from-sint-of-gt-uint-uint
      ;; boolean-from-sint-of-ge-uint-uint
      ;; boolean-from-sint-of-eq-uint-uint
      ;; boolean-from-sint-of-ne-uint-uint
      add-uchar-uchar-okp
      div-uchar-uchar-okp
      minus-uchar-okp
      mul-uchar-uchar-okp
      rem-uchar-uchar-okp
      shl-uchar-okp
      shl-uchar-uchar-okp
      shr-uchar-okp
      shr-uchar-uchar-okp
      sub-uchar-uchar-okp
      uchar-integerp ; exposes signed-byte-p
      char-bits
      ;; uchar-dec-const
      )
  :redundant-okp t)
