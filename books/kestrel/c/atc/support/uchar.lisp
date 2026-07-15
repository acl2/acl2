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

(local (in-theory (enable c::uchar-integer-fix c::uchar-integerp c::char-bits c::uchar-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

(defthm <=-of-uchar-integer-fix-linear
  (<= (c::uchar-integer-fix x) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-uchar-integer-fix
  (implies (and (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (c::uchar-integer-fix x))))

(defthm <=-of-integer-from-uchar-linear
  (<= (c::integer-from-uchar x) 255)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-uchar))))

(defthm unsigned-byte-p-of-integer-from-uchar
  (implies (and (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (c::integer-from-uchar x)))
  :hints (("Goal" :in-theory (enable c::integer-from-uchar))))

;; Seems ok to leave enabled.
;; Needed below.
;; The suffix -2 distinguishes this from a disabled rule in ATC -- just enable it here?
(defthm integer-from-sint-of-sint-from-uchar-2
  (equal (c::integer-from-sint (c::sint-from-uchar x))
         (c::integer-from-uchar x))
  :hints (("Goal" :in-theory (enable c::sint-from-uchar c::sint-integer-fix c::sint-integerp c::int-bits))))

;; We might like uchar-integerp-of-integer-from-sint-of-bitnot-uchar, but it is
;; not true, because the value can go negative.

;; bitand-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitand-uchar-uchar
  (c::uchar-integerp (c::integer-from-sint (c::bitand-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable c::bitand-uchar-uchar c::bitand-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))

;; bitior-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitior-uchar-uchar
  (c::uchar-integerp (c::integer-from-sint (c::bitior-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable c::bitior-uchar-uchar c::bitior-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))

;; bitxor-uchar-uchar returns a sint, but the result would fit in a uchar
(defthm uchar-integerp-of-integer-from-sint-of-bitxor-uchar-uchar
  (c::uchar-integerp (c::integer-from-sint (c::bitxor-uchar-uchar x y)))
  :hints (("Goal" :in-theory (enable c::bitxor-uchar-uchar c::bitxor-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion, etc

;; Needed below (because constants must be at least size int):
(defthm uchar-from-uint-of-uint-from-integer
  (implies (c::uchar-integerp k)
           (equal (c::uchar-from-uint (c::uint-from-integer k))
                  (c::uchar-from-integer k)))
  :hints (("Goal" :in-theory (enable c::uchar-from-uint
                                     c::uint-from-integer
                                     c::uchar-from-integer
                                     c::uchar-from-integer-mod
                                     c::integer-from-uint
                                     c::uint-integerp
                                     c::int-bits
                                     c::uint-integer-fix))))

(defthmd equal-of-integer-from-uchar-and-integer-from-uchar
  (equal (equal (c::integer-from-uchar x) (c::integer-from-uchar y))
         (equal (c::uchar-fix x) (c::uchar-fix y)))
  :hints (("Goal" :in-theory (enable c::integer-from-uchar c::uchar-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants:

(defthmd uchar-from-integer-when-constant-dec
  (implies (and (syntaxp (quotep k))
                (c::uchar-integerp k))
           (equal (c::uchar-from-integer k)
                  (c::uchar-from-uint (c::uint-dec-const k))))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-integer-fix c::uint-integerp c::int-bits))))

(defthmd uchar-from-integer-when-constant-hex
  (implies (and (syntaxp (quotep k))
                (c::uchar-integerp k))
           (equal (c::uchar-from-integer k)
                  (c::uchar-from-uint (c::uint-hex-const k))))
  :hints (("Goal" :in-theory (enable c::uint-hex-const c::uint-integer-fix c::uint-integerp c::int-bits))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uchar-uchar-of-uchar-from-uint-of-uchar-dec-const-convert-to-hex-arg1
  (equal (c::bitand-uchar-uchar (c::uchar-from-uint (c::uint-dec-const x)) y)
         (c::bitand-uchar-uchar (c::uchar-from-uint (c::uint-hex-const x)) y))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uchar-uchar-of-uchar-from-uint-of-uchar-dec-const-convert-to-hex-arg2
  (equal (c::bitand-uchar-uchar x (c::uchar-from-uint (c::uint-dec-const y)))
         (c::bitand-uchar-uchar x (c::uchar-from-uint (c::uint-hex-const y))))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C operations:

;; Converts bitnot-uchar into lognot
;; sint is involved because c::bitnot-uchar returns a sint
(defthmd integer-from-sint-of-bitnot-uchar
  (equal (c::integer-from-sint (c::bitnot-uchar x))
         (lognot (c::integer-from-uchar x)))
  :hints (("Goal" :in-theory (enable c::bitnot-uchar
                                     c::bitnot-sint ; todo
                                     c::sint-from-uchar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitand-uchar-uchar into logand
;; sint is involved because c::bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitand-uchar-uchar
  (equal (c::integer-from-sint (c::bitand-uchar-uchar x y))
         (logand (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::bitand-uchar-uchar
                                     c::bitand-sint-sint ; todo
                                     c::sint-from-uchar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitior-uchar-uchar into logior
;; sint is involved because c::bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitior-uchar-uchar
  (equal (c::integer-from-sint (c::bitior-uchar-uchar x y))
         (logior (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::bitior-uchar-uchar
                                     c::bitior-sint-sint ; todo
                                     c::sint-from-uchar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitxor-uchar-uchar into logxor
;; sint is involved because c::bitand-uchar-uchar returns a sint
(defthmd integer-from-sint-of-bitxor-uchar-uchar
  (equal (c::integer-from-sint (c::bitxor-uchar-uchar x y))
         (logxor (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::bitxor-uchar-uchar
                                     c::bitxor-sint-sint ; todo
                                     c::sint-from-uchar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-uchar-uchar into <
(defthmd boolean-from-sint-of-lt-uchar-uchar
  (equal (c::boolean-from-sint (c::lt-uchar-uchar x y))
         (< (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::lt-uchar-uchar c::lt-sint-sint))))

;; (theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uchar-uchar)
;;                                 (:rewrite boolean-from-sint-of-lt-uchar-uchar)))

;; Converts le-uchar-uchar into <=
(defthmd boolean-from-sint-of-le-uchar-uchar
  (equal (c::boolean-from-sint (c::le-uchar-uchar x y))
         (<= (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::le-uchar-uchar c::le-sint-sint))))

;; Converts gt-uchar-uchar into >
(defthmd boolean-from-sint-of-gt-uchar-uchar
  (equal (c::boolean-from-sint (c::gt-uchar-uchar x y))
         (> (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::gt-uchar-uchar c::gt-sint-sint))))

;; Converts ge-uchar-uchar into >=
(defthmd boolean-from-sint-of-ge-uchar-uchar
  (equal (c::boolean-from-sint (c::ge-uchar-uchar x y))
         (>= (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::ge-uchar-uchar c::ge-sint-sint))))

;; Converts eq-uchar-uchar into equal
(defthmd boolean-from-sint-of-eq-uchar-uchar
  (equal (c::boolean-from-sint (c::eq-uchar-uchar x y))
         (equal (c::integer-from-uchar x) (c::integer-from-uchar y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::eq-uchar-uchar c::eq-sint-sint))))

;; Converts ne-uchar-uchar into not equal
(defthmd boolean-from-sint-of-ne-uchar-uchar
  (equal (c::boolean-from-sint (c::ne-uchar-uchar x y))
         (not (equal (c::integer-from-uchar x) (c::integer-from-uchar y))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::ne-uchar-uchar c::ne-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

;; todo: more for other types, and other inner ops
(defthm lognot-sint-of-ne-uchar-uchar
  (equal (c::lognot-sint (c::ne-uchar-uchar x y))
         (c::eq-uchar-uchar x y))
  :hints (("Goal" :in-theory (enable c::ne-uchar-uchar c::eq-uchar-uchar c::ne-sint-sint c::eq-sint-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable uchar-removal-rules.

(defthm ucharp-of-declar
  (equal (c::ucharp (c::declar x))
         (c::ucharp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm ucharp-of-assign
  (equal (c::ucharp (c::assign x))
         (c::ucharp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
;; todo: add to this
(deftheory uchar-removal-rules
    '(c::assign
      c::declar
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
      c::add-uchar-uchar-okp
      c::div-uchar-uchar-okp
      c::minus-uchar-okp
      c::mul-uchar-uchar-okp
      c::rem-uchar-uchar-okp
      c::shl-uchar-okp
      c::shl-uchar-uchar-okp
      c::shr-uchar-okp
      c::shr-uchar-uchar-okp
      c::sub-uchar-uchar-okp
      c::uchar-integerp ; exposes signed-byte-p
      c::char-bits
      ;; c::uchar-dec-const
      )
  :redundant-okp t)
