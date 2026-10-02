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

(in-theory (disable (:e ullong-from-integer)
                    (:e ullong-dec-const) ; ensures these are retained by simplify
                    (:e ullong-hex-const)
                    (:e ullong-oct-const)))

(local (in-theory (enable llong-bits ullong-max ullong-integerp ullong-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm <=-of-ullong-integer-fix-linear
  (<= (ullong-integer-fix x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm <=-of-integer-from-ullong-linear
  (<= (integer-from-ullong x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-ullong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Enabled since this is essentially an inversion rule.
(defthm integer-from-ullong-of-ullong-from-integer-mod
  (implies (integerp x)
           (equal (integer-from-ullong (ullong-from-integer-mod x))
                  (mod x (expt 2 (llong-bits)))))
  :hints (("Goal" :in-theory (enable ullong-from-integer-mod integer-from-ullong ullongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + on ullongs into add-ullong-ullong (strong-rule)
(defthmd +-becomes-add-ullong-ullong
  (implies (and (ullong-integerp x)
                (ullong-integerp y)
                (ullong-integerp (+ x y)))
           (equal (+ x y)
                  (integer-from-ullong (add-ullong-ullong (ullong-from-integer x) (ullong-from-integer y)))))
  :hints (("Goal" :in-theory (enable add-ullong-ullong))))

;; Converts + to add-ullong-ullong.
;; Requires showing that the addition doesn't overflow.
(defthmd ullong-from-integer-of-+-becomes-add-ullong-ullong
  (implies (and (ullong-integerp (+ x y))
                (ullong-integerp x)
                (ullong-integerp y))
           (equal (ullong-from-integer (+ x y))
                  (add-ullong-ullong (ullong-from-integer x) (ullong-from-integer y))))
  :hints (("Goal" :in-theory (enable add-ullong-ullong ullong-from-integer-mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd ullong-from-integer-of-if
  (equal (ullong-from-integer (if test tp ep))
         (if test (ullong-from-integer tp) (ullong-from-integer ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ullong-removal-rules.

(defthm ullongp-of-declar
  (equal (ullongp (declar x))
         (ullongp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm ullongp-of-assign
  (equal (ullongp (assign x))
         (ullongp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory introduces C operators
(deftheory ullong-intro-rules
    '(;ullong-from-integer-becomes-ullong-dec-const-when-constant
      ullong-from-integer-of-+-becomes-add-ullong-ullong
      ;; ullong-from-integer-of-mod-of-+-and-expt2-of-llong-bits
      ;ullong-from-integer-of-mod-of-+-and-18446744073709551616
      ;ullong-from-integer-of-if ; so that we convert the branches
      )
  :redundant-okp t)

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
(deftheory ullong-removal-rules
    '(assign
      declar
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
      ;; div-ullong-ullong-okp
      ;; rem-ullong-ullong-okp
      ;; shl-ullong-ullong-okp
      ;; shr-ullong-ullong-okp
      ullong-integerp ; exposes unsigned-byte-p
      llong-bits
      ullong-dec-const ; exposes ullong-from-integer
      ullong-hex-const ; exposes ullong-from-integer
      ullong-oct-const ; exposes ullong-from-integer
      ullong-max)
  :redundant-okp t)
