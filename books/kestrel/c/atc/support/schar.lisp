; Rules about schar functions
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

(defthm <=-of-schar-integer-fix-linear
  (<= (c::schar-integer-fix x) 127)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::schar-integer-fix
                                     c::schar-integerp
                                     c::char-bits
                                     signed-byte-p))))

(defthm <=-of-schar-integer-fix-linear-2
  (<= -128 (c::schar-integer-fix x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::schar-integer-fix
                                     c::schar-integerp
                                     c::char-bits
                                     signed-byte-p))))

(defthm <=-of-integer-from-schar-linear
  (<= (c::integer-from-schar x) 127)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-schar))))

(defthm <=-of-integer-from-schar-linear-2
  (<= -128 (c::integer-from-schar x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-schar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts bitnot-schar into lognot
;; sint is involved because c::bitnot-schar returns a sint
(defthmd integer-from-sint-of-bitnot-schar
  (equal (c::integer-from-sint (c::bitnot-schar x))
         (lognot (c::integer-from-schar x)))
  :hints (("Goal" :in-theory (enable c::bitnot-schar
                                     c::bitnot-sint ; todo
                                     c::sint-from-schar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitand-schar-schar into logand
;; sint is involved because c::bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitand-schar-schar
  (equal (c::integer-from-sint (c::bitand-schar-schar x y))
         (logand (c::integer-from-schar x) (c::integer-from-schar y)))
  :hints (("Goal" :in-theory (enable c::bitand-schar-schar
                                     c::bitand-sint-sint ; todo
                                     c::sint-from-schar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitior-schar-schar into logior
;; sint is involved because c::bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitior-schar-schar
  (equal (c::integer-from-sint (c::bitior-schar-schar x y))
         (logior (c::integer-from-schar x) (c::integer-from-schar y)))
  :hints (("Goal" :in-theory (enable c::bitior-schar-schar
                                     c::bitior-sint-sint ; todo
                                     c::sint-from-schar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitxor-schar-schar into logxor
;; sint is involved because c::bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitxor-schar-schar
  (equal (c::integer-from-sint (c::bitxor-schar-schar x y))
         (logxor (c::integer-from-schar x) (c::integer-from-schar y)))
  :hints (("Goal" :in-theory (enable c::bitxor-schar-schar
                                     c::bitxor-sint-sint ; todo
                                     c::sint-from-schar
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable schar-removal-rules.

(defthm scharp-of-declar
  (equal (c::scharp (c::declar x))
         (c::scharp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm scharp-of-assign
  (equal (c::scharp (c::assign x))
         (c::scharp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory schar-removal-rules
    '(c::assign
      c::declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
      ;; integer-from-uint-of-add-uint-uint ; or we could introduce bvplus
      ;; integer-from-uint-of-sub-uint-uint
      integer-from-sint-of-bitnot-schar
      integer-from-sint-of-bitand-schar-schar
      integer-from-sint-of-bitior-schar-schar
      integer-from-sint-of-bitxor-schar-schar
      ;; ;; integer-from-uint-of-shl-uint ; needed?
      ;; integer-from-uint-of-shl-uint-uint
      ;; boolean-from-sint-of-lt-uint-uint
      ;; boolean-from-sint-of-le-uint-uint
      ;; boolean-from-sint-of-gt-uint-uint
      ;; boolean-from-sint-of-ge-uint-uint
      ;; boolean-from-sint-of-eq-uint-uint
      ;; boolean-from-sint-of-ne-uint-uint
      ;; c::add-uchar-uchar-okp
      ;; c::div-uchar-uchar-okp
      ;; c::minus-uchar-okp
      ;; c::mul-uchar-uchar-okp
      ;; c::rem-uchar-uchar-okp
      ;; c::shl-uchar-okp
      ;; c::shl-uchar-uchar-okp
      ;; c::shr-uchar-okp
      ;; c::shr-uchar-uchar-okp
      ;; c::sub-uchar-uchar-okp
      c::schar-integerp ; exposes signed-byte-p
      c::char-bits
      ;; c::schar-dec-const ; does not exist
      )
  :redundant-okp t)
