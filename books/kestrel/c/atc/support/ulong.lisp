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

(in-theory (disable (:e ulong-from-integer)
                    (:e ulong-dec-const) ; ensures these are retained by simplify
                    (:e ulong-hex-const)
                    (:e ulong-oct-const)))

(local (in-theory (enable long-bits ulong-max ulong-integerp ulong-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-ulong-integer-fix-linear
  (<= (ulong-integer-fix x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-ulong-integer-fix
  (implies (and (<= 64 size)
                (integerp size))
           (unsigned-byte-p size (ulong-integer-fix x))))

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-integer-from-ulong-linear
  (<= (integer-from-ulong x) 18446744073709551615)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-ulong))))

(defthm unsigned-byte-p-of-integer-from-ulong
  (implies (and (<= 64 size)
                (integerp size))
           (unsigned-byte-p size (integer-from-ulong x)))
  :hints (("Goal" :in-theory (enable integer-from-ulong))))

;; or enable ulong-integerp
(defthm ulong-integerp-of-mod
  (implies (and (<= y (expt 2 (long-bits)))
                (posp y)
                (integerp x))
           (ulong-integerp (mod x y)))
  :hints (("Goal" :in-theory (enable ulong-integerp long-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion theorems

(defthm integer-from-ulong-of-ulong-dec-const
  (equal (integer-from-ulong (ulong-dec-const x))
         (ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable ulong-dec-const))))

(defthm integer-from-ulong-of-ulong-hex-const
  (equal (integer-from-ulong (ulong-hex-const x))
         (ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable ulong-hex-const))))

(defthm integer-from-ulong-of-ulong-oct-const
  (equal (integer-from-ulong (ulong-oct-const x))
         (ulong-integer-fix x))
  :hints (("Goal" :in-theory (enable ulong-oct-const))))

;; Enabled since this is essentially an inversion rule.
;; Or we could introduce bvplus.
(defthm integer-from-ulong-of-ulong-from-integer-mod
  (implies (integerp x)
           (equal (integer-from-ulong (ulong-from-integer-mod x))
                  (mod x (expt 2 (long-bits)))))
  :hints (("Goal" :in-theory (enable ulong-from-integer-mod integer-from-ulong ulongp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + to add-ulong-ulong.
;; Requires showing that the addition doesn't overflow.
(defthmd ulong-from-integer-of-+-becomes-add-ulong-ulong
  (implies (and (ulong-integerp (+ x y))
                (ulong-integerp x)
                (ulong-integerp y))
           (equal (ulong-from-integer (+ x y))
                  (add-ulong-ulong (ulong-from-integer x) (ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable add-ulong-ulong ulong-from-integer-mod))))

;; Converts mod of + to add-ulong-ulong.
(defthmd ulong-from-integer-of-mod-of-+-and-expt2-of-long-bits
  (implies (and (ulong-integerp x)
                (ulong-integerp y))
           (equal (ulong-from-integer (mod (+ x y) (expt 2 (long-bits))))
                  (add-ulong-ulong (ulong-from-integer x) (ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable add-ulong-ulong ulong-from-integer-mod))))

;; Converts mod of + to add-ulong-ulong.
;; May have to change when we parameterize the size of ulongs.
(defthmd ulong-from-integer-of-mod-of-+-and-18446744073709551616
  (implies (and (ulong-integerp x)
                (ulong-integerp y))
           (equal (ulong-from-integer (mod (+ x y) 18446744073709551616))
                  (add-ulong-ulong (ulong-from-integer x) (ulong-from-integer y))))
  :hints (("Goal" :in-theory (enable add-ulong-ulong ulong-from-integer-mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-ulong-ulong to <
(defthmd boolean-from-sint-of-lt-ulong-ulong
  (equal (boolean-from-sint (lt-ulong-ulong x y))
         (< (integer-from-ulong x) (integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint lt-ulong-ulong))))

;; Converts le-ulong-ulong to <=
(defthmd boolean-from-sint-of-le-ulong-ulong
  (equal (boolean-from-sint (le-ulong-ulong x y))
         (<= (integer-from-ulong x) (integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint le-ulong-ulong))))

;; Converts gt-ulong-ulong to >
(defthmd boolean-from-sint-of-gt-ulong-ulong
  (equal (boolean-from-sint (gt-ulong-ulong x y))
         (> (integer-from-ulong x) (integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint gt-ulong-ulong))))

;; Converts ge-ulong-ulong to >=
(defthmd boolean-from-sint-of-ge-ulong-ulong
  (equal (boolean-from-sint (ge-ulong-ulong x y))
         (>= (integer-from-ulong x) (integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint ge-ulong-ulong))))

;; Converts eq-ulong-ulong to equal
(defthmd boolean-from-sint-of-eq-ulong-ulong
  (equal (boolean-from-sint (eq-ulong-ulong x y))
         (equal (integer-from-ulong x) (integer-from-ulong y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     eq-ulong-ulong))))

;; Converts ne-ulong-ulong to equal
(defthmd boolean-from-sint-of-ne-ulong-ulong
  (equal (boolean-from-sint (ne-ulong-ulong x y))
         (not (equal (integer-from-ulong x) (integer-from-ulong y))))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     ne-ulong-ulong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd ulong-from-integer-becomes-ulong-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (ulong-from-integer x)
                  (ulong-dec-const x)))
  :hints (("Goal" :in-theory (enable ulong-dec-const))))

(theory-invariant (incompatible (:rewrite ulong-from-integer-becomes-ulong-dec-const-when-constant)
                                (:definition ulong-dec-const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd ulong-from-integer-of-if
  (equal (ulong-from-integer (if test tp ep))
         (if test (ulong-from-integer tp) (ulong-from-integer ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ulong-removal-rules.

(defthm ulongp-of-declar
  (equal (ulongp (declar x))
         (ulongp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm ulongp-of-assign
  (equal (ulongp (assign x))
         (ulongp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory introduces C operators
(deftheory ulong-intro-rules
    '(ulong-from-integer-becomes-ulong-dec-const-when-constant
      ulong-from-integer-of-+-becomes-add-ulong-ulong
      ;; ulong-from-integer-of-mod-of-+-and-expt2-of-long-bits
      ulong-from-integer-of-mod-of-+-and-18446744073709551616
      ulong-from-integer-of-if ; so that we convert the branches
      )
  :redundant-okp t)

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
(deftheory ulong-removal-rules
    '(assign
      declar
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
      div-ulong-ulong-okp
      rem-ulong-ulong-okp
      shl-ulong-ulong-okp
      shr-ulong-ulong-okp
      ulong-integerp ; exposes unsigned-byte-p
      long-bits
      ulong-dec-const ; exposes ulong-from-integer
      ulong-hex-const ; exposes ulong-from-integer
      ulong-oct-const ; exposes ulong-from-integer
      ulong-max)
  :redundant-okp t)
