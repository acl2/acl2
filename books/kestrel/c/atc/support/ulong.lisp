; C support material dealing with ulongs
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

;; TODO: Add ulong versions of the material from uint.lisp?
;; TODO: Add ulong versions of the material from sint.lisp?

(include-book "kestrel/c/representation/integer-operations" :dir :system)
(include-book "kestrel/c/atc/let-designations" :dir :system) ; for assign and declar
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable (:e c::ulong-from-integer)
                    (:e c::ulong-dec-const) ; ensures these are retained by simplify
                    (:e c::ulong-hex-const)
                    (:e c::ulong-oct-const)))

(local (in-theory (enable c::long-bits c::ulong-max c::ulong-integerp c::ulong-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-ulong-integer-fix-linear
  (<= (c::ulong-integer-fix x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-ulong-integer-fix
  (implies (and (<= 64 size)
                (integerp size))
           (unsigned-byte-p size (c::ulong-integer-fix x))))

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-integer-from-ulong-linear
  (<= (c::integer-from-ulong x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-ulong))))

(defthm unsigned-byte-p-of-integer-from-ulong
  (implies (and (<= 64 size)
                (integerp size))
           (unsigned-byte-p size (c::integer-from-ulong x)))
  :hints (("Goal" :in-theory (enable c::integer-from-ulong))))

;; or enable c::ulong-integerp
(defthm ulong-integerp-of-mod
  (implies (and (<= y (expt 2 (c::long-bits)))
                (posp y)
                (integerp x))
           (c::ulong-integerp (mod x y)))
  :hints (("Goal" :in-theory (enable c::ulong-integerp c::long-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion theorems

(defthm integer-from-ulong-of-ulong-dec-const
  (equal (c::integer-from-ulong (c::ulong-dec-const x))
         (c::ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable c::ulong-dec-const))))

(defthm integer-from-ulong-of-ulong-hex-const
  (equal (c::integer-from-ulong (c::ulong-hex-const x))
         (c::ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable c::ulong-hex-const))))

(defthm integer-from-ulong-of-ulong-oct-const
  (equal (c::integer-from-ulong (c::ulong-oct-const x))
         (c::ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable c::ulong-oct-const))))

;; Enabled since this is essentially an inversion rule.
;; Or we could introduce bvplus.
(defthm integer-from-ulong-of-ulong-from-integer-mod
  (implies (integerp x)
           (equal (c::integer-from-ulong (c::ulong-from-integer-mod x))
                  (mod x (expt 2 (c::long-bits)))))
  :hints (("Goal" :in-theory (enable c::ulong-from-integer-mod c::integer-from-ulong c::ulongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + to c::add-ulong-ulong.
;; Requires showing that the addition doesn't overflow.
(defthmd ulong-from-integer-of-+-becomes-add-ulong-ulong
  (implies (and (c::ulong-integerp (+ x y))
                (c::ulong-integerp x)
                (c::ulong-integerp y))
           (equal (c::ulong-from-integer (+ x y))
                  (c::add-ulong-ulong (c::ulong-from-integer x) (c::ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-ulong-ulong c::ulong-from-integer-mod))))

;; Converts mod of + to c::add-ulong-ulong.
(defthmd ulong-from-integer-of-mod-of-+-and-expt2-of-long-bits
  (implies (and (c::ulong-integerp x)
                (c::ulong-integerp y))
           (equal (c::ulong-from-integer (mod (+ x y) (expt 2 (c::long-bits))))
                  (c::add-ulong-ulong (c::ulong-from-integer x) (c::ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-ulong-ulong c::ulong-from-integer-mod))))

;; Converts mod of + to c::add-ulong-ulong.
;; May have to change when we parameterize the size of ulongs.
(defthmd ulong-from-integer-of-mod-of-+-and-18446744073709551616
  (implies (and (c::ulong-integerp x)
                (c::ulong-integerp y))
           (equal (c::ulong-from-integer (mod (+ x y) 18446744073709551616))
                  (c::add-ulong-ulong (c::ulong-from-integer x) (c::ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-ulong-ulong c::ulong-from-integer-mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-ulong-ulong to <
(defthmd boolean-from-sint-of-lt-ulong-ulong
  (equal (c::boolean-from-sint (c::lt-ulong-ulong x y))
         (< (c::integer-from-ulong x) (c::integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::lt-ulong-ulong))))

;; Converts le-ulong-ulong to <=
(defthmd boolean-from-sint-of-le-ulong-ulong
  (equal (c::boolean-from-sint (c::le-ulong-ulong x y))
         (<= (c::integer-from-ulong x) (c::integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::le-ulong-ulong))))

;; Converts gt-ulong-ulong to >
(defthmd boolean-from-sint-of-gt-ulong-ulong
  (equal (c::boolean-from-sint (c::gt-ulong-ulong x y))
         (> (c::integer-from-ulong x) (c::integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::gt-ulong-ulong))))

;; Converts ge-ulong-ulong to >=
(defthmd boolean-from-sint-of-ge-ulong-ulong
  (equal (c::boolean-from-sint (c::ge-ulong-ulong x y))
         (>= (c::integer-from-ulong x) (c::integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::ge-ulong-ulong))))

;; Converts eq-ulong-ulong to equal
(defthmd boolean-from-sint-of-eq-ulong-ulong
  (equal (c::boolean-from-sint (c::eq-ulong-ulong x y))
         (equal (c::integer-from-ulong x) (c::integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::eq-ulong-ulong))))

;; Converts ne-ulong-ulong to equal
(defthmd boolean-from-sint-of-ne-ulong-ulong
  (equal (c::boolean-from-sint (c::ne-ulong-ulong x y))
         (not (equal (c::integer-from-ulong x) (c::integer-from-ulong y))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::ne-ulong-ulong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd ulong-from-integer-becomes-ulong-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (c::ulong-from-integer x)
                  (c::ulong-dec-const x)))
  :hints (("Goal" :in-theory (enable c::ulong-dec-const))))

(theory-invariant (incompatible (:rewrite ulong-from-integer-becomes-ulong-dec-const-when-constant)
                                (:definition c::ulong-dec-const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd c::ulong-from-integer-of-if
  (equal (c::ulong-from-integer (if test tp ep))
         (if test (c::ulong-from-integer tp) (c::ulong-from-integer ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ulong-removal-rules.

(defthm ulongp-of-declar
  (equal (c::ulongp (c::declar x))
         (c::ulongp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm ulongp-of-assign
  (equal (c::ulongp (c::assign x))
         (c::ulongp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory introduces C operators
(deftheory ulong-intro-rules
    '(ulong-from-integer-becomes-ulong-dec-const-when-constant
      ulong-from-integer-of-+-becomes-add-ulong-ulong
      ;; ulong-from-integer-of-mod-of-+-and-expt2-of-long-bits
      ulong-from-integer-of-mod-of-+-and-18446744073709551616
      c::ulong-from-integer-of-if ; so that we convert the branches
      )
  :redundant-okp t)

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
(deftheory ulong-removal-rules
    '(c::assign
      c::declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
      ;; integer-from-ulong-of-add-ulong-ulong ; or we could introduce bvplus
      ;; integer-from-ulong-of-sub-ulong-ulong
      ;; integer-from-ulong-of-bitand-ulong-ulong
      ;; integer-from-ulong-of-bitior-ulong-ulong
      ;; ;; integer-from-ulong-of-shl-ulong ; needed?
      ;; integer-from-ulong-of-shl-ulong-ulong
      boolean-from-sint-of-lt-ulong-ulong
      boolean-from-sint-of-le-ulong-ulong
      boolean-from-sint-of-gt-ulong-ulong
      boolean-from-sint-of-ge-ulong-ulong
      boolean-from-sint-of-eq-ulong-ulong
      boolean-from-sint-of-ne-ulong-ulong
      c::div-ulong-ulong-okp
      c::rem-ulong-ulong-okp
      c::shl-ulong-ulong-okp
      c::shr-ulong-ulong-okp
      c::ulong-integerp ; exposes unsigned-byte-p
      c::long-bits
      c::ulong-dec-const ; exposes ulong-from-integer
      c::ulong-hex-const ; exposes ulong-from-integer
      c::ulong-oct-const ; exposes ulong-from-integer
      c::ulong-max)
  :redundant-okp t)
