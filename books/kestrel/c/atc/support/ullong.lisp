; C support material dealing with ullongs
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
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable (:e c::ullong-from-integer)
                    (:e c::ullong-dec-const) ; ensures these are retained by simplify
                    (:e c::ullong-hex-const)
                    (:e c::ullong-oct-const)))

(local (in-theory (enable c::llong-bits c::ullong-max c::ullong-integerp c::ullong-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm <=-of-ullong-integer-fix-linear
  (<= (c::ullong-integer-fix x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm <=-of-integer-from-ullong-linear
  (<= (c::integer-from-ullong x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-ullong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Enabled since this is essentially an inversion rule.
(defthm integer-from-ullong-of-ullong-from-integer-mod
  (implies (integerp x)
           (equal (c::integer-from-ullong (c::ullong-from-integer-mod x))
                  (mod x (expt 2 (c::llong-bits)))))
  :hints (("Goal" :in-theory (enable c::ullong-from-integer-mod c::integer-from-ullong c::ullongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + on ullongs into add-ullong-ullong (strong-rule)
(defthmd +-becomes-add-ullong-ullong
  (implies (and (c::ullong-integerp x)
                (c::ullong-integerp y)
                (c::ullong-integerp (+ x y)))
           (equal (+ x y)
                  (c::integer-from-ullong (c::add-ullong-ullong (c::ullong-from-integer x) (c::ullong-from-integer y)))))
  :hints (("Goal" :in-theory (enable c::add-ullong-ullong))))

;; Converts + to c::add-ullong-ullong.
;; Requires showing that the addition doesn't overflow.
(defthmd ullong-from-integer-of-+-becomes-add-ullong-ullong
  (implies (and (c::ullong-integerp (+ x y))
                (c::ullong-integerp x)
                (c::ullong-integerp y))
           (equal (c::ullong-from-integer (+ x y))
                  (c::add-ullong-ullong (c::ullong-from-integer x) (c::ullong-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-ullong-ullong c::ullong-from-integer-mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd c::ullong-from-integer-of-if
  (equal (c::ullong-from-integer (if test tp ep))
         (if test (c::ullong-from-integer tp) (c::ullong-from-integer ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ullong-removal-rules.

(defthm ullongp-of-declar
  (equal (c::ullongp (c::declar x))
         (c::ullongp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm ullongp-of-assign
  (equal (c::ullongp (c::assign x))
         (c::ullongp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory introduces C operators
(deftheory ullong-intro-rules
    '(;ullong-from-integer-becomes-ullong-dec-const-when-constant
      ullong-from-integer-of-+-becomes-add-ullong-ullong
      ;; ullong-from-integer-of-mod-of-+-and-expt2-of-llong-bits
      ;ullong-from-integer-of-mod-of-+-and-18446744073709551616
      ;c::ullong-from-integer-of-if ; so that we convert the branches
      )
  :redundant-okp t)

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
(deftheory ullong-removal-rules
    '(c::assign
      c::declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
      ;; integer-from-ullong-of-add-ullong-ullong ; or we could introduce bvplus
      ;; integer-from-ullong-of-sub-ullong-ullong
      ;; integer-from-ullong-of-bitand-ullong-ullong
      ;; integer-from-ullong-of-bitior-ullong-ullong
      ;; ;; integer-from-ullong-of-shl-ullong ; needed?
      ;; integer-from-ullong-of-shl-ullong-ullong
      ;; boolean-from-sint-of-lt-ullong-ullong
      ;; boolean-from-sint-of-le-ullong-ullong
      ;; boolean-from-sint-of-gt-ullong-ullong
      ;; boolean-from-sint-of-ge-ullong-ullong
      ;; boolean-from-sint-of-eq-ullong-ullong
      ;; boolean-from-sint-of-ne-ullong-ullong
      ;; c::div-ullong-ullong-okp
      ;; c::rem-ullong-ullong-okp
      ;; c::shl-ullong-ullong-okp
      ;; c::shr-ullong-ullong-okp
      c::ullong-integerp ; exposes unsigned-byte-p
      c::llong-bits
      c::ullong-dec-const ; exposes ullong-from-integer
      c::ullong-hex-const ; exposes ullong-from-integer
      c::ullong-oct-const ; exposes ullong-from-integer
      c::ullong-max)
  :redundant-okp t)
