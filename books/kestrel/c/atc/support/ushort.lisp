; C support material dealing with ushorts
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
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "sint")) ; for things like integer-from-sint-of-sub-sint-sint

(local (in-theory (enable c::ushort-integer-fix c::ushort-integerp c::short-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This mentions sint but is needed for things below (note that add-ushort-ushort calls add-sint-sint).
;; There is something similar in atc
;; but it is in kestrel/c/atc/symbolic-execution-rules/exec-binary-strict-pure-gen.lisp.
(defthm integer-from-sint-of-sint-from-ushort
  (equal (c::integer-from-sint (c::sint-from-ushort x))
         (c::integer-from-ushort x))
  :hints (("Goal" :in-theory (enable c::integer-from-sint
                                     c::integer-from-ushort
                                     c::sint-integer-fix
                                     c::sint-from-ushort
                                     c::sint-integerp
                                     c::int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

(defthm <=-of-ushort-integer-fix-linear
  (<= (c::ushort-integer-fix x) 65535)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-ushort-integer-fix
  (implies (and (<= 16 size)
                (integerp size))
           (unsigned-byte-p size (c::ushort-integer-fix x))))

(defthm <=-of-integer-from-ushort-linear
  (<= (c::integer-from-ushort x) 65535)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable c::integer-from-ushort))))

(defthm unsigned-byte-p-of-integer-from-ushort
  (implies (and (<= 16 size)
                (integerp size))
           (unsigned-byte-p size (c::integer-from-ushort x)))
  :hints (("Goal" :in-theory (enable c::integer-from-ushort))))

;; todo: improve (see the version for uints)
;; May have to change when we parameterize the size of ushorts.
;move
(defthm ushort-integerp-of-mod-of-+-of-65536
  (implies (and (integerp x)
                (integerp y))
           (c::ushort-integerp (mod (+ x y) 65536))))

;; We might like ushort-integerp-of-integer-from-sint-of-bitnot-ushort, but it is
;; not true, because the value can go negative.

;; bitand-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitand-ushort-ushort
  (c::ushort-integerp (c::integer-from-sint (c::bitand-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable c::bitand-ushort-ushort c::bitand-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))

;; bitior-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitior-ushort-ushort
  (c::ushort-integerp (c::integer-from-sint (c::bitior-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable c::bitior-ushort-ushort c::bitior-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))

;; bitxor-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitxor-ushort-ushort
  (c::ushort-integerp (c::integer-from-sint (c::bitxor-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable c::bitxor-ushort-ushort c::bitxor-sint-sint c::sint-integer-fix c::sint-integerp c::int-bits))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helps get rid of redundant guard conjunct in c::add-ushort-ushort.
;; This depends on the choice of sizes for ints, which we may not want to rely on in general.
(defthm add-ushort-ushort-okp-when-ushortp-and-ushortp
  (implies (and (c::ushortp c::x)
                (c::ushortp c::y))
           (c::add-ushort-ushort-okp c::x c::y))
  :hints (("Goal" :in-theory (enable c::add-ushort-ushort-okp
                                     c::sint-from-ushort
                                     c::add-sint-sint-okp
                                     c::sint-integerp
                                     c::sint-integer-fix
                                     c::int-bits))))

(defthm equal-of-ushort-fix
  (equal (equal (c::ushort-fix x) x)
         (c::ushortp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + of - into c::sub-ushort-ushort
(defthmd ushort-from-integer-of-+-of---arg2
  (implies (and (<= y x)
                (c::ushort-integerp x)
                (c::ushort-integerp y))
           (equal (c::ushort-from-integer (+ x (- y)))
                  ;; Note that the sub returns a sint, so we have to convert it to a ushort:
                  (c::ushort-from-sint (c::sub-ushort-ushort (c::ushort-from-integer x)
                                                             (c::ushort-from-integer y)))))
  :hints (("Goal" :in-theory (enable c::sub-ushort-ushort
                                     c::ushort-max
                                     c::int-bits
                                     c::add-sint-sint
                                     c::ushort-from-sint
                                     c::sint-integer-fix ; todo
                                     unsigned-byte-p     ; todo
                                     c::ushort-from-integer-mod
                                     c::integer-from-sint-of-add-sint-sint
                                     c::integer-from-sint-of-sub-sint-sint
                                     c::sub-sint-sint-okp
                                     c::sint-integerp
                                     ))))

;; Converts + of - into c::sub-ushort-ushort
(defthmd ushort-from-integer-of-+-of---arg1
  (implies (and (<= y x)
                (c::ushort-integerp x)
                (c::ushort-integerp y))
           (equal (c::ushort-from-integer (+ (- y) x))
                  ;; Note that the sub returns a sint, so we have to convert it to a ushort:
                  (c::ushort-from-sint (c::sub-ushort-ushort (c::ushort-from-integer x)
                                                             (c::ushort-from-integer y)))))
  :hints (("Goal" :in-theory (enable ushort-from-integer-of-+-of---arg2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts bitnot-ushort into lognot
;; sint is involved because c::bitnot-ushort returns a sint
(defthmd integer-from-sint-of-bitnot-ushort
  (equal (c::integer-from-sint (c::bitnot-ushort x))
         (lognot (c::integer-from-ushort x)))
  :hints (("Goal" :in-theory (enable c::bitnot-ushort
                                     c::bitnot-sint ; todo
                                     c::sint-from-ushort
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitand-ushort-ushort into logand
;; sint is involved because c::bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitand-ushort-ushort
  (equal (c::integer-from-sint (c::bitand-ushort-ushort x y))
         (logand (c::integer-from-ushort x) (c::integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable c::bitand-ushort-ushort
                                     c::bitand-sint-sint ; todo
                                     c::sint-from-ushort
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitior-ushort-ushort into logior
;; sint is involved because c::bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitior-ushort-ushort
  (equal (c::integer-from-sint (c::bitior-ushort-ushort x y))
         (logior (c::integer-from-ushort x) (c::integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable c::bitior-ushort-ushort
                                     c::bitior-sint-sint ; todo
                                     c::sint-from-ushort
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))

;; Converts bitxor-ushort-ushort into logxor
;; sint is involved because c::bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitxor-ushort-ushort
  (equal (c::integer-from-sint (c::bitxor-ushort-ushort x y))
         (logxor (c::integer-from-ushort x) (c::integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable c::bitxor-ushort-ushort
                                     c::bitxor-sint-sint ; todo
                                     c::sint-from-ushort
                                     c::sint-integer-fix
                                     c::sint-integerp
                                     c::int-bits))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ushort-removal-rules.

(defthm ushortp-of-declar
  (equal (c::ushortp (c::declar x))
         (c::ushortp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm ushortp-of-assign
  (equal (c::ushortp (c::assign x))
         (c::ushortp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not used yet?
(deftheory ushort-removal-rules
    '(c::assign
      c::declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-ushort-ushort without conversion wrappers outside of them:
      ;; integer-from-ushort-of-add-ushort-ushort ; or we could introduce bvplus
      ;; integer-from-ushort-of-sub-ushort-ushort
      integer-from-sint-of-bitnot-ushort
      integer-from-sint-of-bitand-ushort-ushort
      integer-from-sint-of-bitior-ushort-ushort
      integer-from-sint-of-bitxor-ushort-ushort
      ;; ;; integer-from-ushort-of-shl-ushort ; needed?
      ;; integer-from-ushort-of-shl-ushort-ushort
      ;; boolean-from-sint-of-lt-ushort-ushort
      ;; boolean-from-sint-of-le-ushort-ushort
      ;; boolean-from-sint-of-gt-ushort-ushort
      ;; boolean-from-sint-of-ge-ushort-ushort
      ;; boolean-from-sint-of-eq-ushort-ushort
      ;; boolean-from-sint-of-ne-ushort-ushort
      c::add-ushort-ushort-okp
      c::sub-ushort-ushort-okp
      c::mul-ushort-ushort-okp
      c::div-ushort-ushort-okp
      c::rem-ushort-ushort-okp
      c::shl-ushort-ushort-okp
      c::shr-ushort-ushort-okp
      c::ushort-integerp ; exposes unsigned-byte-p
      c::short-bits
      ;; c::ushort-dec-const ; doesn't exit
      )
  :redundant-okp t)

;; This theory introduces C operators
(deftheory ushort-intro-rules
    '(ushort-from-integer-of-+-of---arg1
      ushort-from-integer-of-+-of---arg2)
  :redundant-okp t)
