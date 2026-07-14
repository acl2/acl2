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

(in-theory (disable (:e c::uint-from-integer)
                    (:e c::uint-dec-const) ; ensures these are retained by simplify
                    (:e c::uint-hex-const)
                    (:e c::uint-oct-const)))

(local (in-theory (enable c::int-bits c::uint-max c::uint-integerp c::uint-integer-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-uint-integer-fix-linear
  (<= (c::uint-integer-fix x) 4294967295)
  :rule-classes :linear)

(defthm unsigned-byte-p-of-uint-integer-fix
  (implies (and ;; (<= 32 size)
                (<= (c::int-bits) size)
                (integerp size))
           (unsigned-byte-p size (c::uint-integer-fix x))))

;; ACL2 should already know the lower bound, by type reasoning
(defthm <=-of-integer-from-uint-linear
  (<= (c::integer-from-uint x) 4294967295)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-uint))))

(defthm unsigned-byte-p-of-integer-from-uint
  (implies (and ;; (<= 32 size)
                (<= (c::int-bits) size)
                (integerp size))
           (unsigned-byte-p size (c::integer-from-uint x)))
  :hints (("Goal" :in-theory (enable c::integer-from-uint))))

;; The mod does nothing - drop?
;; (defthm mod-of-integer-from-uint-and-4294967296
;;   (equal (mod (c::integer-from-uint x) 4294967296)
;;          (c::integer-from-uint x))
;;   :hints (("Goal" :in-theory (enable c::integer-from-uint
;;
;;                                      unsigned-byte-p))))

;; ;drop or improve? avoid c::int-bits?
(local
 (defthmd uint-integerp-of-mod-of-expt-of-int-bits
   (implies (integerp x)
            (c::uint-integerp (mod x (expt 2 (c::int-bits)))))))

;drop or improve? avoid c::int-bits?
(defthmd uint-integer-fix-of-mod-of-expt-of-int-bits
  (implies (integerp x)
           (equal (c::uint-integer-fix (mod x (expt 2 (c::int-bits))))
                  (mod x (expt 2 (c::int-bits)))))
  :hints (("Goal" :in-theory (enable uint-integerp-of-mod-of-expt-of-int-bits))))

;; or enable c::uint-integerp
(defthm uint-integerp-of-mod
  (implies (and (<= y (expt 2 (c::int-bits)))
                (posp y)
                (integerp x))
           (c::uint-integerp (mod x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; todo: more like this
(defthm cinteger-kind-of-uint-from-integer
  (equal (c::cinteger-kind (c::uint-from-integer x))
         :uint)
  :hints (("Goal" :in-theory (enable c::cinteger-kind
                                     c::scharp c::sshortp c::sintp c::ucharp c::ushortp
                                     c::uint-from-integer c::uintp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion theorems

;; Note that c::integer-from-uint-of-uint-from-integer is built in to ATC.

(defthm integer-from-uint-of-uint-dec-const
  (equal (c::integer-from-uint (c::uint-dec-const x))
         (c::uint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::uint-dec-const))))

(defthm integer-from-uint-of-uint-hex-const
  (equal (c::integer-from-uint (c::uint-hex-const x))
         (c::uint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::uint-hex-const))))

(defthm integer-from-uint-of-uint-oct-const
  (equal (c::integer-from-uint (c::uint-oct-const x))
         (c::uint-integer-fix x))
  :hints (("Goal" :in-theory (enable c::uint-oct-const))))

;; Enabled since this is essentially an inversion rule.
;; Or we could introduce bvplus.
(defthm integer-from-uint-of-uint-from-integer-mod
  (implies (integerp x)
           (equal (c::integer-from-uint (c::uint-from-integer-mod x))
                  (mod x (expt 2 (c::int-bits)))))
  :hints (("Goal" :in-theory (enable c::uint-from-integer-mod c::integer-from-uint c::uintp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Handling constants:

;; Introduces proper C constants (the rules below convert to hex constants in certain cases).
(defthmd uint-from-integer-becomes-uint-dec-const-when-constant
  (implies (syntaxp (quotep x))
           (equal (c::uint-from-integer x)
                  (c::uint-dec-const x)))
  :hints (("Goal" :in-theory (enable c::uint-dec-const))))

(theory-invariant (incompatible (:rewrite uint-from-integer-becomes-uint-dec-const-when-constant)
                                (:definition c::uint-dec-const)))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (c::bitand-uint-uint (c::uint-dec-const x) y)
         (c::bitand-uint-uint (c::uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitand to be in hex.
(defthmd bitand-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (c::bitand-uint-uint x (c::uint-dec-const y))
         (c::bitand-uint-uint x (c::uint-hex-const y)))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitior to be in hex.
(defthmd bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (c::bitior-uint-uint (c::uint-dec-const x) y)
         (c::bitior-uint-uint (c::uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitior to be in hex.
(defthmd bitior-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (c::bitior-uint-uint x (c::uint-dec-const y))
         (c::bitior-uint-uint x (c::uint-hex-const y)))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitxor to be in hex.
(defthmd bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg1
  (equal (c::bitxor-uint-uint (c::uint-dec-const x) y)
         (c::bitxor-uint-uint (c::uint-hex-const x) y))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;; We often want constant arguments of bitxor to be in hex.
(defthmd bitxor-uint-uint-of-uint-dec-const-convert-to-hex-arg2
  (equal (c::bitxor-uint-uint x (c::uint-dec-const y))
         (c::bitxor-uint-uint x (c::uint-hex-const y)))
  :hints (("Goal" :in-theory (enable c::uint-dec-const c::uint-hex-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + on uints into add-uint-uint (strong-rule)
;improve name?
(defthmd +-becomes-add-uint-uint
  (implies (and (c::uint-integerp x)
                (c::uint-integerp y)
                (c::uint-integerp (+ x y)))
           (equal (+ x y)
                  (c::integer-from-uint (c::add-uint-uint (c::uint-from-integer x) (c::uint-from-integer y)))))
  :hints (("Goal" :in-theory (enable c::add-uint-uint))))

;; Converts + to add-uint-uint
(defthmd uint-from-integer-of-+-becomes-add-uint-uint
  (implies (and (unsigned-byte-p 32 (+ x y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (c::uint-from-integer (+ x y))
                  (c::add-uint-uint (c::uint-from-integer x) (c::uint-from-integer y))))
  :hints (("Goal" :in-theory (enable +-becomes-add-uint-uint))))

;; No overflow check
;; todo: think about whether the hyps should say unsigned-byte-p or c::uint-integerp
(defthmd uint-from-integer-of-mod-of-+-and-expt2-of-int-bits
  (implies (and (c::uint-integerp x)
                (c::uint-integerp y))
           (equal (c::uint-from-integer (mod (+ x y) (expt 2 (c::int-bits))))
                  (c::add-uint-uint (c::uint-from-integer x) (c::uint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-uint-uint c::uint-from-integer-mod))))

;; Pushes the conversion inward and converts the addition to c::add-uint-uint.
;; May have to change when we parameterize the size of uints.
(defthmd uint-from-integer-of-mod-of-+-and-4294967296
  (implies (and (c::uint-integerp x)
                (c::uint-integerp y))
           (equal (c::uint-from-integer (mod (+ x y) 4294967296))
                  (c::add-uint-uint (c::uint-from-integer x) (c::uint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::add-uint-uint c::uint-from-integer-mod))))

;; Somewhat unusual.  Do we really need this?
(defthmd +-of-1-and-integer-from-uint
  (implies (and (c::uintp n)
                (force (not (equal (c::integer-from-uint n) 4294967295))))
           (equal (+ 1 (c::integer-from-uint n))
                  (c::integer-from-uint (c::add-uint-uint (c::uint-from-integer 1) n))))
  :hints (("Goal" :in-theory (enable c::add-uint-uint
                                     c::uint-from-integer-mod
                                     unsigned-byte-p))))

;; Somewhat unusual.  Do we really need this?
(defthmd +-of-1-and-integer-from-uint-gen
  (implies (c::uintp n)
           (equal (+ 1 (c::integer-from-uint n))
                  (if (equal (c::integer-from-uint n) 4294967295)
                      4294967296
                    (c::integer-from-uint (c::add-uint-uint (c::uint-from-integer '1) n)))))
  :hints (("Goal" :in-theory (enable c::add-uint-uint
                                     c::uint-from-integer-mod))))

;; Converts * to mul-uint-uint
(defthmd uint-from-integer-of-*-becomes-mul-uint-uint
  (implies (and (unsigned-byte-p 32 (* x y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (c::uint-from-integer (* x y))
                  (c::mul-uint-uint (c::uint-from-integer x) (c::uint-from-integer y))))
  :hints (("Goal" :in-theory (enable c::mul-uint-uint c::uint-from-integer-mod ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C comparisons:

;; Converts < on uints into lt-uint-uint
;strong rule
(defthmd <-becomes-boolean-from-sint-of-lt-uint-uint
  (implies (and (c::uint-integerp x)
                (c::uint-integerp y))
           (equal (< x y)
                  (c::boolean-from-sint (c::lt-uint-uint (c::uint-from-integer x) (c::uint-from-integer y)))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint
                                     c::lt-uint-uint))))

(theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uint-uint)
                                (:definition c::lt-uint-uint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C operations:

;; Converts add-uint-uint into + (essentially).
(defthmd integer-from-uint-of-add-uint-uint
  (equal (c::integer-from-uint (c::add-uint-uint x y))
         (mod (+ (c::integer-from-uint x) (c::integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::add-uint-uint c::uint-from-integer-mod))))

;; Converts sub-uint-uint into - (essentially).
(defthmd integer-from-uint-of-sub-uint-uint
  (equal (c::integer-from-uint (c::sub-uint-uint x y))
         (mod (- (c::integer-from-uint x) (c::integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::sub-uint-uint c::uint-from-integer-mod))))

;; Converts bitnot-uint into lognot
;; sint is involved because c::bitnot-uint returns a sint
(defthmd integer-from-uint-of-bitnot-uint
  (equal (c::integer-from-uint (c::bitnot-uint x))
         (mod (lognot (c::integer-from-uint x))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::bitnot-uint))))

;; Converts bitand-uint-uint to logand (essentially)
(defthmd integer-from-uint-of-bitand-uint-uint
  (equal (c::integer-from-uint (c::bitand-uint-uint x y))
         (mod (logand (c::integer-from-uint x) (c::integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::bitand-uint-uint c::uint-from-integer-mod))))

;; Converts bitior-uint-uint to logior (essentially)
(defthmd integer-from-uint-of-bitior-uint-uint
  (equal (c::integer-from-uint (c::bitior-uint-uint x y))
         (mod (logior (c::integer-from-uint x) (c::integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::bitior-uint-uint c::uint-from-integer-mod))))

;; Converts bitxor-uint-uint to logxor (essentially)
(defthmd integer-from-uint-of-bitxor-uint-uint
  (equal (c::integer-from-uint (c::bitxor-uint-uint x y))
         (mod (logxor (c::integer-from-uint x) (c::integer-from-uint y))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::bitxor-uint-uint c::uint-from-integer-mod))))

;; Converts shl-uint into * of expt (essentially)
;; May only be needed for library proofs.
(defthmd integer-from-uint-of-shl-uint
  (implies (natp amt)
           (equal (c::integer-from-uint (c::shl-uint val amt))
                  (mod (* (expt 2 amt) (c::integer-from-uint val))
                       (expt 2 32))))
  :hints (("Goal" :in-theory (enable c::shl-uint integer-from-uint-of-uint-from-integer-mod))))

;; Converts shl-uint-uint into * of expt (essentially)
(defthmd integer-from-uint-of-shl-uint-uint
  (equal (c::integer-from-uint (c::shl-uint-uint val amt))
         (mod (* (expt 2 (c::integer-from-uint amt)) (c::integer-from-uint val))
              (expt 2 32)))
  :hints (("Goal" :in-theory (enable c::shl-uint-uint integer-from-uint-of-shl-uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that remove C comparisons:

;; Converts lt-uint-uint into <
(defthmd boolean-from-sint-of-lt-uint-uint
  (equal (c::boolean-from-sint (c::lt-uint-uint x y))
         (< (c::integer-from-uint x) (c::integer-from-uint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::lt-uint-uint))))

(theory-invariant (incompatible (:rewrite <-becomes-boolean-from-sint-of-lt-uint-uint)
                                (:rewrite boolean-from-sint-of-lt-uint-uint)))

;; Converts le-uint-uint into <=
(defthmd boolean-from-sint-of-le-uint-uint
  (equal (c::boolean-from-sint (c::le-uint-uint x y))
         (<= (c::integer-from-uint x) (c::integer-from-uint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::le-uint-uint))))

;; Converts gt-uint-uint into >
(defthmd boolean-from-sint-of-gt-uint-uint
  (equal (c::boolean-from-sint (c::gt-uint-uint x y))
         (> (c::integer-from-uint x) (c::integer-from-uint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::gt-uint-uint))))

;; Converts ge-uint-uint into >=
(defthmd boolean-from-sint-of-ge-uint-uint
  (equal (c::boolean-from-sint (c::ge-uint-uint x y))
         (>= (c::integer-from-uint x) (c::integer-from-uint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::ge-uint-uint))))

;; Converts eq-uint-uint into equal
(defthmd boolean-from-sint-of-eq-uint-uint
  (equal (c::boolean-from-sint (c::eq-uint-uint x y))
         (equal (c::integer-from-uint x) (c::integer-from-uint y)))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::eq-uint-uint))))

;; Converts ne-uint-uint into not equal
(defthmd boolean-from-sint-of-ne-uint-uint
  (equal (c::boolean-from-sint (c::ne-uint-uint x y))
         (not (equal (c::integer-from-uint x) (c::integer-from-uint y))))
  :hints (("Goal" :in-theory (enable c::boolean-from-sint c::ne-uint-uint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about the C operators

; x < 0 is false for uints
;; not used?
(defthmd lt-uint-uint-of-uint-of-0-arg2
  (equal (c::lt-uint-uint x (c::uint-from-integer 0))
         (c::sint-from-integer 0) ; use sint-dec-const?
         )
  :hints (("Goal" :in-theory (enable c::lt-uint-uint))))

; x < x is false
(defthmd lt-uint-uint-same
  (equal (c::lt-uint-uint x x)
         (c::sint-from-integer 0) ; use sint-dec-const?
         )
  :hints (("Goal" :in-theory (enable c::lt-uint-uint))))

; perhaps unusual, can help avoid parens in generated code
(defthmd bitand-uint-uint-associative-left
  (equal (c::bitand-uint-uint x (c::bitand-uint-uint y z))
         (c::bitand-uint-uint (c::bitand-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable c::bitand-uint-uint
                                     c::uint-from-integer-mod
                                     c::integer-from-uint))))

; perhaps unusual, can help avoid parens in generated code
;; used one time
(defthmd bitior-uint-uint-associative-left
  (equal (c::bitior-uint-uint x (c::bitior-uint-uint y z))
         (c::bitior-uint-uint (c::bitior-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable c::bitior-uint-uint
                                     c::uint-from-integer-mod
                                     c::integer-from-uint))))

; perhaps unusual, can help avoid parens in generated code
(defthmd bitxor-uint-uint-associative-left
  (equal (c::bitxor-uint-uint x (c::bitxor-uint-uint y z))
         (c::bitxor-uint-uint (c::bitxor-uint-uint x y) z))
  :hints (("Goal" :in-theory (enable c::bitxor-uint-uint
                                     c::uint-from-integer-mod
                                     c::integer-from-uint))))

;; Needed for applicability conditions of tailrec
(defthm add-uint-uint-associative
  (equal (c::add-uint-uint (c::add-uint-uint x y) z)
         (c::add-uint-uint x (c::add-uint-uint y z)))
  :hints (("Goal" :in-theory (enable c::add-uint-uint c::uint-from-integer-mod))))

;; Only used just below
(local
 (defthmd add-uint-uint-of-uint-of-0-arg1
   (equal (c::add-uint-uint (c::uint-from-integer 0) y)
          (c::uint-fix y))
   :hints (("Goal" :in-theory (enable c::add-uint-uint c::uintp c::uint-from-integer-mod)))))

;; Only used just below
(local
 (defthmd add-uint-uint-of-uint-of-0-arg2
   (equal (c::add-uint-uint x (c::uint-from-integer 0))
          (c::uint-fix x))
   :hints (("Goal" :in-theory (enable c::add-uint-uint c::uintp c::uint-from-integer-mod)))))

;; For a tailrec applicability condition
(defthm add-uint-uint-of-uint-dec-const-of-0-arg1
  (equal (c::add-uint-uint (c::uint-dec-const 0) x)
         (c::uint-fix x))
  :hints (("Goal" :in-theory (e/d (c::uint-dec-const add-uint-uint-of-uint-of-0-arg1)
                                  ((:e c::uint-from-integer)
                                   (:e c::uint-dec-const))))))

;; For a tailrec applicability condition
(defthm add-uint-uint-of-uint-dec-const-of-0-arg2
  (equal (c::add-uint-uint x (c::uint-dec-const 0))
         (c::uint-fix x))
  :hints (("Goal" :in-theory (e/d (c::uint-dec-const add-uint-uint-of-uint-of-0-arg2)
                                  ((:e c::uint-from-integer)
                                   (:e c::uint-dec-const))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable uint-removal-rules.

(defthm uintp-of-declar
  (equal (c::uintp (c::declar x))
         (c::uintp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm uintp-of-assign
  (equal (c::uintp (c::assign x))
         (c::uintp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: add for other types
;; Let's keep this enabled, to resolve the case dispatch and expose integer-from-uint.
;; Or we could just enable c::integer-from-cinteger or integer-from-cinteger-alt-def.
(defthm integer-from-cinteger-when-uintp
  (implies (c::uintp x)
           (equal (c::integer-from-cinteger x)
                  (c::integer-from-uint x)))
  :hints (("Goal" :in-theory (enable c::ucharp
                                     c::ushortp
                                     c::uintp
                                     c::scharp
                                     c::sshortp
                                     c::sintp
                                     c::integer-from-cinteger
                                     c::cinteger-kind
                                     c::cinteger-uint->get))))

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
  '(c::assign
    c::declar
    ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
    ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
    c::integer-from-uint-of-add-uint-uint ; or we could introduce bvplus
    c::integer-from-uint-of-sub-uint-uint
    c::integer-from-uint-of-bitnot-uint
    c::integer-from-uint-of-bitand-uint-uint
    c::integer-from-uint-of-bitior-uint-uint
    c::integer-from-uint-of-bitxor-uint-uint
    ;; c::integer-from-uint-of-shl-uint ; needed?
    c::integer-from-uint-of-shl-uint-uint
    c::boolean-from-sint-of-lt-uint-uint
    c::boolean-from-sint-of-le-uint-uint
    c::boolean-from-sint-of-gt-uint-uint
    c::boolean-from-sint-of-ge-uint-uint
    c::boolean-from-sint-of-eq-uint-uint
    c::boolean-from-sint-of-ne-uint-uint
    ;; c::sub-uint-uint-okp
    ;; c::add-uint-uint-okp
    ;; c::mul-uint-uint-okp
    c::div-uint-uint-okp
    c::rem-uint-uint-okp
    c::shl-uint-uint-okp
    c::shl-uint-okp
    c::shr-uint-uint-okp
    c::shr-uint-okp
    c::uint-integerp ; exposes unsigned-byte-p
    c::int-bits
    c::uint-dec-const ; exposes uint-from-integer
    c::uint-hex-const ; exposes uint-from-integer
    c::uint-oct-const ; exposes uint-from-integer
    c::uint-max)
  :redundant-okp t)
