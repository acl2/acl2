; C support material dealing with uints
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

;; TODO: Try to do derivations without exposing the sizes of data types (may
;; require modifications to this machinery)

(include-book "kestrel/c/representation/integer-operations" :dir :system)
(include-book "kestrel/c/atc/let-designations" :dir :system) ; for assign and declar
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;(include-book "kestrel/bv/bvchop" :dir :system) ; todo: drop.  this disables unsigned-byte-p
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/lognot" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))

(in-theory (disable (:e uint-from-integer)
                    (:e uint-dec-const) ; ensures these are retained by simplify
                    (:e uint-hex-const)
                    (:e uint-oct-const)))

(local (in-theory (enable int-bits uint-max uint-integerp uint-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-uint-integer-fix-linear
  (<= (uint-integer-fix x) 4294967295)
  :rule-classes :linear)

(defthm unsigned-byte-p-of-uint-integer-fix
  (implies (and ;; (<= 32 size)
                (<= (int-bits) size)
                (integerp size))
           (unsigned-byte-p size (uint-integer-fix x))))

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-integer-from-uint-linear
  (<= (integer-from-uint x) 4294967295)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-uint))))

(defthm unsigned-byte-p-of-integer-from-uint
  (implies (and ;; (<= 32 size)
                (<= (int-bits) size)
                (integerp size))
           (unsigned-byte-p size (integer-from-uint x)))
  :hints (("Goal" :in-theory (enable integer-from-uint))))

;; The mod does nothing - drop?
;; (defthm mod-of-integer-from-uint-and-4294967296
;;   (equal (mod (integer-from-uint x) 4294967296)
;;          (integer-from-uint x))
;;   :hints (("Goal" :in-theory (enable integer-from-uint
;;
;;                                      unsigned-byte-p))))

;; ;drop or improve? avoid int-bits?
(local
 (defthmd uint-integerp-of-mod-of-expt-of-int-bits
   (implies (integerp x)
            (uint-integerp (mod x (expt 2 (int-bits)))))))

;drop or improve? avoid int-bits?
(defthmd uint-integer-fix-of-mod-of-expt-of-int-bits
  (implies (integerp x)
           (equal (uint-integer-fix (mod x (expt 2 (int-bits))))
                  (mod x (expt 2 (int-bits)))))
  :hints (("Goal" :in-theory (enable uint-integerp-of-mod-of-expt-of-int-bits))))

;; or enable uint-integerp
(defthm uint-integerp-of-mod
  (implies (and (<= y (expt 2 (int-bits)))
                (posp y)
                (integerp x))
           (uint-integerp (mod x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; todo: more like this
(defthm cinteger-kind-of-uint-from-integer
  (equal (cinteger-kind (uint-from-integer x))
         :uint)
  :hints (("Goal" :in-theory (enable cinteger-kind
                                     scharp sshortp sintp ucharp ushortp
                                     uint-from-integer uintp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion theorems

;; Note that integer-from-uint-of-uint-from-integer is built in to ATC.

(defthm integer-from-uint-of-uint-dec-const
  (equal (integer-from-uint (uint-dec-const x))
         (uint-integer-fix x))
  :hints (("Goal" :in-theory (enable uint-dec-const))))

(defthm integer-from-uint-of-uint-hex-const
  (equal (integer-from-uint (uint-hex-const x))
         (uint-integer-fix x))
  :hints (("Goal" :in-theory (enable uint-hex-const))))

(defthm integer-from-uint-of-uint-oct-const
  (equal (integer-from-uint (uint-oct-const x))
         (uint-integer-fix x))
  :hints (("Goal" :in-theory (enable uint-oct-const))))

;; Enabled since this is essentially an inversion rule.
;; Or we could introduce bvplus.
(defthm integer-from-uint-of-uint-from-integer-mod
  (implies (integerp x)
           (equal (integer-from-uint (uint-from-integer-mod x))
                  (mod x (expt 2 (int-bits)))))
  :hints (("Goal" :in-theory (enable uint-from-integer-mod integer-from-uint uintp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants:

;; Introduces proper C constants (the rules below convert to hex constants in certain cases).
(defthmd uint-from-integer-becomes-uint-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (uint-from-integer x)
                  (uint-dec-const x)))
  :hints (("Goal" :in-theory (enable uint-dec-const))))

(theory-invariant (incompatible (:rewrite uint-from-integer-becomes-uint-dec-const-when-constant)
                                (:definition uint-dec-const)))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (bitand-uint-uint (uint-dec-const x) y)
         (bitand-uint-uint (uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (bitand-uint-uint x (uint-dec-const y))
         (bitand-uint-uint x (uint-hex-const y)))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitior to be in hex.
(defthmd bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (bitior-uint-uint (uint-dec-const x) y)
         (bitior-uint-uint (uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitior to be in hex.
(defthmd bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (bitior-uint-uint x (uint-dec-const y))
         (bitior-uint-uint x (uint-hex-const y)))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitxor to be in hex.
(defthmd bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (bitxor-uint-uint (uint-dec-const x) y)
         (bitxor-uint-uint (uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;; We often want constant arguments of bitxor to be in hex.
(defthmd bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (bitxor-uint-uint x (uint-dec-const y))
         (bitxor-uint-uint x (uint-hex-const y)))
  :hints (("Goal" :in-theory (enable uint-dec-const uint-hex-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + on uints into add-uint-uint (strong-rule)
;improve name?
(defthmd +-becomes-add-uint-uint
  (implies (and (uint-integerp x)
                (uint-integerp y)
                (uint-integerp (+ x y)))
           (equal (+ x y)
                  (integer-from-uint (add-uint-uint (uint-from-integer x) (uint-from-integer y)))))
  :hints (("Goal" :in-theory (enable add-uint-uint))))

;; Converts + to add-uint-uint
(defthmd uint-from-integer-of-+-becomes-add-uint-uint
  (implies (and (unsigned-byte-p 32 (+ x y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (uint-from-integer (+ x y))
                  (add-uint-uint (uint-from-integer x) (uint-from-integer y))))
  :hints (("Goal" :in-theory (enable +-becomes-add-uint-uint))))

;; No overflow check
;; todo: think about whether the hyps should say unsigned-byte-p or uint-integerp
(defthmd uint-from-integer-of-mod-of-+-and-expt2-of-int-bits
  (implies (and (uint-integerp x)
                (uint-integerp y))
           (equal (uint-from-integer (mod (+ x y) (expt 2 (int-bits))))
                  (add-uint-uint (uint-from-integer x) (uint-from-integer y))))
  :hints (("Goal" :in-theory (enable add-uint-uint uint-from-integer-mod))))

;; Pushes the conversion inward and converts the addition to add-uint-uint.
;; May have to change when we parameterize the size of uints.
(defthmd uint-from-integer-of-mod-of-+-and-4294967296
  (implies (and (uint-integerp x)
                (uint-integerp y))
           (equal (uint-from-integer (mod (+ x y) 4294967296))
                  (add-uint-uint (uint-from-integer x) (uint-from-integer y))))
  :hints (("Goal" :in-theory (enable add-uint-uint uint-from-integer-mod))))

;; Somewhat unusual.  Do we really need this?
(defthmd +-of-1-and-integer-from-uint
  (implies (and (uintp n)
                (force (not (equal (integer-from-uint n) 4294967295))))
           (equal (+ 1 (integer-from-uint n))
                  (integer-from-uint (add-uint-uint (uint-from-integer 1) n))))
  :hints (("Goal" :in-theory (enable add-uint-uint
                                     uint-from-integer-mod
                                     unsigned-byte-p))))

;; Somewhat unusual.  Do we really need this?
(defthmd +-of-1-and-integer-from-uint-gen
  (implies (uintp n)
           (equal (+ 1 (integer-from-uint n))
                  (if (equal (integer-from-uint n) 4294967295)
                      4294967296
                    (integer-from-uint (add-uint-uint (uint-from-integer '1) n)))))
  :hints (("Goal" :in-theory (enable add-uint-uint
                                     uint-from-integer-mod))))

;; Converts * to mul-uint-uint
(defthmd uint-from-integer-of-*-becomes-mul-uint-uint
  (implies (and (unsigned-byte-p 32 (* x y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (uint-from-integer (* x y))
                  (mul-uint-uint (uint-from-integer x) (uint-from-integer y))))
  :hints (("Goal" :in-theory (enable mul-uint-uint uint-from-integer-mod ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C comparisons:

;; Converts < on uints into lt-uint-uint
;strong rule
(defthmd <-becomes-boolean-from-sint-of-lt-uint-uint
  (implies (and (uint-integerp x)
                (uint-integerp y))
           (equal (< x y)
                  (boolean-from-sint (lt-uint-uint (uint-from-integer x) (uint-from-integer y)))))
  :hints (("Goal" :in-theory (enable boolean-from-sint
                                     lt-uint-uint))))

(theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uint-uint)
                                (:definition lt-uint-uint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C operations:

;; Converts add-uint-uint into + (essentially).
(defthmd integer-from-uint-of-add-uint-uint
  (equal (integer-from-uint (add-uint-uint x y))
         (mod (+ (integer-from-uint x) (integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable add-uint-uint uint-from-integer-mod))))

;; Converts sub-uint-uint into - (essentially).
(defthmd integer-from-uint-of-sub-uint-uint
  (equal (integer-from-uint (sub-uint-uint x y))
         (mod (- (integer-from-uint x) (integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable sub-uint-uint uint-from-integer-mod))))

;; Converts bitnot-uint into lognot
;; sint is involved because bitnot-uint returns a sint
(defthmd integer-from-uint-of-bitnot-uint
  (equal (integer-from-uint (bitnot-uint x))
         (mod (lognot (integer-from-uint x))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable bitnot-uint))))

;; Converts bitand-uint-uint to logand (essentially)
(defthmd integer-from-uint-of-bitand-uint-uint
  (equal (integer-from-uint (bitand-uint-uint x y))
         (mod (logand (integer-from-uint x) (integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable bitand-uint-uint uint-from-integer-mod))))

;; Converts bitior-uint-uint to logior (essentially)
(defthmd integer-from-uint-of-bitior-uint-uint
  (equal (integer-from-uint (bitior-uint-uint x y))
         (mod (logior (integer-from-uint x) (integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable bitior-uint-uint uint-from-integer-mod))))

;; Converts bitxor-uint-uint to logxor (essentially)
(defthmd integer-from-uint-of-bitxor-uint-uint
  (equal (integer-from-uint (bitxor-uint-uint x y))
         (mod (logxor (integer-from-uint x) (integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable bitxor-uint-uint uint-from-integer-mod))))

;; Converts shl-uint into * of expt (essentially)
;; May only be needed for library proofs.
(defthmd integer-from-uint-of-shl-uint
  (implies (natp amt)
           (equal (integer-from-uint (shl-uint val amt))
                  (mod (* (expt 2 amt) (integer-from-uint val))
                       (expt 2 32))))
  :hints (("Goal" :in-theory (enable shl-uint integer-from-uint-of-uint-from-integer-mod))))

;; Converts shl-uint-uint into * of expt (essentially)
(defthmd integer-from-uint-of-shl-uint-uint
  (equal (integer-from-uint (shl-uint-uint val amt))
         (mod (* (expt 2 (integer-from-uint amt)) (integer-from-uint val))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable shl-uint-uint integer-from-uint-of-shl-uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-uint-uint into <
(defthmd boolean-from-sint-of-lt-uint-uint
  (equal (boolean-from-sint (lt-uint-uint x y))
         (< (integer-from-uint x) (integer-from-uint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint lt-uint-uint))))

(theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uint-uint)
                                (:rewrite boolean-from-sint-of-lt-uint-uint)))

;; Converts le-uint-uint into <=
(defthmd boolean-from-sint-of-le-uint-uint
  (equal (boolean-from-sint (le-uint-uint x y))
         (<= (integer-from-uint x) (integer-from-uint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint le-uint-uint))))

;; Converts gt-uint-uint into >
(defthmd boolean-from-sint-of-gt-uint-uint
  (equal (boolean-from-sint (gt-uint-uint x y))
         (> (integer-from-uint x) (integer-from-uint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint gt-uint-uint))))

;; Converts ge-uint-uint into >=
(defthmd boolean-from-sint-of-ge-uint-uint
  (equal (boolean-from-sint (ge-uint-uint x y))
         (>= (integer-from-uint x) (integer-from-uint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint ge-uint-uint))))

;; Converts eq-uint-uint into equal
(defthmd boolean-from-sint-of-eq-uint-uint
  (equal (boolean-from-sint (eq-uint-uint x y))
         (equal (integer-from-uint x) (integer-from-uint y)))
  :hints (("Goal" :in-theory (enable boolean-from-sint eq-uint-uint))))

;; Converts ne-uint-uint into not equal
(defthmd boolean-from-sint-of-ne-uint-uint
  (equal (boolean-from-sint (ne-uint-uint x y))
         (not (equal (integer-from-uint x) (integer-from-uint y))))
  :hints (("Goal" :in-theory (enable boolean-from-sint ne-uint-uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

; x < 0 is false for uints
;; not used?
(defthmd lt-uint-uint-of-uint-of-0-arg2
  (equal (lt-uint-uint x (uint-from-integer 0))
         (sint-from-integer 0) ; use sint-dec-const?
         )
  :hints (("Goal" :in-theory (enable lt-uint-uint))))

; x < x is false
(defthmd lt-uint-uint-same
  (equal (lt-uint-uint x x)
         (sint-from-integer 0) ; use sint-dec-const?
         )
  :hints (("Goal" :in-theory (enable lt-uint-uint))))

; perhaps unusual, can help avoid parens in generated code
(defthmd bitand-uint-uint-associative-left
  (equal (bitand-uint-uint x (bitand-uint-uint y z))
         (bitand-uint-uint (bitand-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable bitand-uint-uint
                                     uint-from-integer-mod
                                     integer-from-uint))))

; perhaps unusual, can help avoid parens in generated code
;; used one time
(defthmd bitior-uint-uint-associative-left
  (equal (bitior-uint-uint x (bitior-uint-uint y z))
         (bitior-uint-uint (bitior-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable bitior-uint-uint
                                     uint-from-integer-mod
                                     integer-from-uint))))

; perhaps unusual, can help avoid parens in generated code
(defthmd bitxor-uint-uint-associative-left
  (equal (bitxor-uint-uint x (bitxor-uint-uint y z))
         (bitxor-uint-uint (bitxor-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable bitxor-uint-uint
                                     uint-from-integer-mod
                                     integer-from-uint))))

;; Needed for applicability conditions of tailrec
(defthm add-uint-uint-associative
  (equal (add-uint-uint (add-uint-uint x y) z)
         (add-uint-uint x (add-uint-uint y z)))
  :hints (("Goal" :in-theory (enable add-uint-uint uint-from-integer-mod))))

;; Only used just below
(local
 (defthmd add-uint-uint-of-uint-of-0-arg1
   (equal (add-uint-uint (uint-from-integer 0) y)
          (uint-fix y))
   :hints (("Goal" :in-theory (enable add-uint-uint uintp uint-from-integer-mod)))))

;; Only used just below
(local
 (defthmd add-uint-uint-of-uint-of-0-arg2
   (equal (add-uint-uint x (uint-from-integer 0))
          (uint-fix x))
   :hints (("Goal" :in-theory (enable add-uint-uint uintp uint-from-integer-mod)))))

;; For a tailrec applicability condition
(defthm add-uint-uint-of-uint-dec-const-of-0-arg1
  (equal (add-uint-uint (uint-dec-const 0) x)
         (uint-fix x))
  :hints (("Goal" :in-theory (e/d (uint-dec-const add-uint-uint-of-uint-of-0-arg1)
                                  ((:e uint-from-integer)
                                   (:e uint-dec-const))))))

;; For a tailrec applicability condition
(defthm add-uint-uint-of-uint-dec-const-of-0-arg2
  (equal (add-uint-uint x (uint-dec-const 0))
         (uint-fix x))
  :hints (("Goal" :in-theory (e/d (uint-dec-const add-uint-uint-of-uint-of-0-arg2)
                                  ((:e uint-from-integer)
                                   (:e uint-dec-const))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable uint-removal-rules.

(defthm uintp-of-declar
  (equal (uintp (declar x))
         (uintp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm uintp-of-assign
  (equal (uintp (assign x))
         (uintp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: add for other types
;; Let's keep this enabled, to resolve the case dispatch and expose integer-from-uint.
;; Or we could just enable integer-from-cinteger or integer-from-cinteger-alt-def.
(defthm integer-from-cinteger-when-uintp
  (implies (uintp x)
           (equal (integer-from-cinteger x)
                  (integer-from-uint x)))
  :hints (("Goal" :in-theory (enable ucharp
                                     ushortp
                                     uintp
                                     scharp
                                     sshortp
                                     sintp
                                     integer-from-cinteger
                                     cinteger-kind
                                     cinteger-uint->get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This theory introduces C operators
(deftheory uint-intro-rules
  '(uint-from-integer-becomes-uint-dec-const-when-constant
    bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg1
    bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg2
    bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg1
    bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg2
    bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg1
    bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg2
    uint-from-integer-of-+-becomes-add-uint-uint
    uint-from-integer-of-mod-of-+-and-expt2-of-int-bits
    uint-from-integer-of-mod-of-+-and-4294967296
    uint-from-integer-of-*-becomes-mul-uint-uint
    ;; add-sint-sint-commute-of-constant-and-var
    )
  :redundant-okp t)

;; todo: compute from uint-intro-rules
(deftheory uint-intro-rules-strong
  (union-theories (theory 'uint-intro-rules)
                  '(;; This strong rule fires even when there is no conversion function involved:
                    <-becomes-boolean-from-sint-of-lt-uint-uint
                    ))
  :redundant-okp t)

;; This theory converts C operations into ACL2 arithmetic operations.
;; It often has to be enabled in guard and termination proofs:
(deftheory uint-removal-rules
  '(assign
    declar
    ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
    ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
    integer-from-uint-of-add-uint-uint ; or we could introduce bvplus
    integer-from-uint-of-sub-uint-uint
    integer-from-uint-of-bitnot-uint
    integer-from-uint-of-bitand-uint-uint
    integer-from-uint-of-bitior-uint-uint
    integer-from-uint-of-bitxor-uint-uint
    ;; integer-from-uint-of-shl-uint ; needed?
    integer-from-uint-of-shl-uint-uint
    boolean-from-sint-of-lt-uint-uint
    boolean-from-sint-of-le-uint-uint
    boolean-from-sint-of-gt-uint-uint
    boolean-from-sint-of-ge-uint-uint
    boolean-from-sint-of-eq-uint-uint
    boolean-from-sint-of-ne-uint-uint
    ;; sub-uint-uint-okp
    ;; add-uint-uint-okp
    ;; mul-uint-uint-okp
    div-uint-uint-okp
    rem-uint-uint-okp
    shl-uint-uint-okp
    shl-uint-okp
    shr-uint-uint-okp
    shr-uint-okp
    uint-integerp ; exposes unsigned-byte-p
    int-bits
    uint-dec-const ; exposes uint-from-integer
    uint-hex-const ; exposes uint-from-integer
    uint-oct-const ; exposes uint-from-integer
    uint-max)
  :redundant-okp t)
