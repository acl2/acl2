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
  (<= (schar-integer-fix x) 127)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable schar-integer-fix
                                     schar-integerp
                                     char-bits
                                     signed-byte-p))))

(defthm <=-of-schar-integer-fix-linear-2
  (<= -128 (schar-integer-fix x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable schar-integer-fix
                                     schar-integerp
                                     char-bits
                                     signed-byte-p))))

(defthm <=-of-integer-from-schar-linear
  (<= (integer-from-schar x) 127)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-schar))))

(defthm <=-of-integer-from-schar-linear-2
  (<= -128 (integer-from-schar x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-schar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts bitnot-schar into lognot
;; sint is involved because bitnot-schar returns a sint
(defthmd integer-from-sint-of-bitnot-schar
  (equal (integer-from-sint (bitnot-schar x))
         (lognot (integer-from-schar x)))
  :hints (("Goal" :in-theory (enable bitnot-schar
                                     bitnot-sint ; todo
                                     sint-from-schar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitand-schar-schar into logand
;; sint is involved because bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitand-schar-schar
  (equal (integer-from-sint (bitand-schar-schar x y))
         (logand (integer-from-schar x) (integer-from-schar y)))
  :hints (("Goal" :in-theory (enable bitand-schar-schar
                                     bitand-sint-sint ; todo
                                     sint-from-schar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitior-schar-schar into logior
;; sint is involved because bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitior-schar-schar
  (equal (integer-from-sint (bitior-schar-schar x y))
         (logior (integer-from-schar x) (integer-from-schar y)))
  :hints (("Goal" :in-theory (enable bitior-schar-schar
                                     bitior-sint-sint ; todo
                                     sint-from-schar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitxor-schar-schar into logxor
;; sint is involved because bitand-schar-schar returns a sint
(defthmd integer-from-sint-of-bitxor-schar-schar
  (equal (integer-from-sint (bitxor-schar-schar x y))
         (logxor (integer-from-schar x) (integer-from-schar y)))
  :hints (("Goal" :in-theory (enable bitxor-schar-schar
                                     bitxor-sint-sint ; todo
                                     sint-from-schar
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable schar-removal-rules.

(defthm scharp-of-declar
  (equal (scharp (declar x))
         (scharp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm scharp-of-assign
  (equal (scharp (assign x))
         (scharp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory schar-removal-rules
    '(assign
      declar
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
      ;; add-uchar-uchar-okp
      ;; div-uchar-uchar-okp
      ;; minus-uchar-okp
      ;; mul-uchar-uchar-okp
      ;; rem-uchar-uchar-okp
      ;; shl-uchar-okp
      ;; shl-uchar-uchar-okp
      ;; shr-uchar-okp
      ;; shr-uchar-uchar-okp
      ;; sub-uchar-uchar-okp
      schar-integerp ; exposes signed-byte-p
      char-bits
      ;; schar-dec-const ; does not exist
      )
  :redundant-okp t)

;; This theory introduces C operators
(deftheory schar-intro-rules
    '(;;ushort-from-integer-of-+-of---arg1
      ;;ushort-from-integer-of-+-of---arg2
      )
  :redundant-okp t)
