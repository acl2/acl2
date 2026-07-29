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

(local (in-theory (enable ushort-integer-fix ushort-integerp short-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This mentions sint but is needed for things below (note that add-ushort-ushort calls add-sint-sint).
;; There is something similar in atc
;; but it is in kestrel/c/atc/symbolic-execution-rules/exec-binary-strict-pure-gen.lisp.
(defthm integer-from-sint-of-sint-from-ushort
  (equal (integer-from-sint (sint-from-ushort x))
         (integer-from-ushort x))
  :hints (("Goal" :in-theory (enable integer-from-sint
                                     integer-from-ushort
                                     sint-integer-fix
                                     sint-from-ushort
                                     sint-integerp
                                     int-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types and bounds (warning: some of these bake in the size of the integer types)

(defthm <=-of-ushort-integer-fix-linear
  (<= (ushort-integer-fix x) 65535)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-ushort-integer-fix
  (implies (and (<= 16 size)
                (integerp size))
           (unsigned-byte-p size (ushort-integer-fix x))))

(defthm <=-of-integer-from-ushort-linear
  (<= (integer-from-ushort x) 65535)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-ushort))))

(defthm unsigned-byte-p-of-integer-from-ushort
  (implies (and (<= 16 size)
                (integerp size))
           (unsigned-byte-p size (integer-from-ushort x)))
  :hints (("Goal" :in-theory (enable integer-from-ushort))))

;; todo: improve (see the version for uints)
;; May have to change when we parameterize the size of ushorts.
;move
(defthm ushort-integerp-of-mod-of-+-of-65536
  (implies (and (integerp x)
                (integerp y))
           (ushort-integerp (mod (+ x y) 65536))))

;; We might like ushort-integerp-of-integer-from-sint-of-bitnot-ushort, but it is
;; not true, because the value can go negative.

;; bitand-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitand-ushort-ushort
  (ushort-integerp (integer-from-sint (bitand-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable bitand-ushort-ushort bitand-sint-sint sint-integer-fix sint-integerp int-bits))))

;; bitior-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitior-ushort-ushort
  (ushort-integerp (integer-from-sint (bitior-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable bitior-ushort-ushort bitior-sint-sint sint-integer-fix sint-integerp int-bits))))

;; bitxor-ushort-ushort returns a sint, but the result would fit in a ushort
(defthm ushort-integerp-of-integer-from-sint-of-bitxor-ushort-ushort
  (ushort-integerp (integer-from-sint (bitxor-ushort-ushort x y)))
  :hints (("Goal" :in-theory (enable bitxor-ushort-ushort bitxor-sint-sint sint-integer-fix sint-integerp int-bits))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helps get rid of redundant guard conjunct in add-ushort-ushort.
;; This depends on the choice of sizes for ints, which we may not want to rely on in general.
(defthm add-ushort-ushort-okp-when-ushortp-and-ushortp
  (implies (and (ushortp x)
                (ushortp y))
           (add-ushort-ushort-okp x y))
  :hints (("Goal" :in-theory (enable add-ushort-ushort-okp
                                     sint-from-ushort
                                     add-sint-sint-okp
                                     sint-integerp
                                     sint-integer-fix
                                     int-bits))))

(defthm equal-of-ushort-fix
  (equal (equal (ushort-fix x) x)
         (ushortp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conversions that introduce C operations:

;; Converts + of - into sub-ushort-ushort
(defthmd ushort-from-integer-of-+-of---arg2
  (implies (and (<= y x)
                (ushort-integerp x)
                (ushort-integerp y))
           (equal (ushort-from-integer (+ x (- y)))
                  ;; Note that the sub returns a sint, so we have to convert it to a ushort:
                  (ushort-from-sint (sub-ushort-ushort (ushort-from-integer x)
                                                             (ushort-from-integer y)))))
  :hints (("Goal" :in-theory (enable sub-ushort-ushort
                                     ushort-max
                                     int-bits
                                     add-sint-sint
                                     ushort-from-sint
                                     sint-integer-fix ; todo
                                     unsigned-byte-p     ; todo
                                     ushort-from-integer-mod
                                     integer-from-sint-of-add-sint-sint
                                     integer-from-sint-of-sub-sint-sint
                                     sub-sint-sint-okp
                                     sint-integerp
                                     ))))

;; Converts + of - into sub-ushort-ushort
(defthmd ushort-from-integer-of-+-of---arg1
  (implies (and (<= y x)
                (ushort-integerp x)
                (ushort-integerp y))
           (equal (ushort-from-integer (+ (- y) x))
                  ;; Note that the sub returns a sint, so we have to convert it to a ushort:
                  (ushort-from-sint (sub-ushort-ushort (ushort-from-integer x)
                                                             (ushort-from-integer y)))))
  :hints (("Goal" :in-theory (enable ushort-from-integer-of-+-of---arg2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Converts bitnot-ushort into lognot
;; sint is involved because bitnot-ushort returns a sint
(defthmd integer-from-sint-of-bitnot-ushort
  (equal (integer-from-sint (bitnot-ushort x))
         (lognot (integer-from-ushort x)))
  :hints (("Goal" :in-theory (enable bitnot-ushort
                                     bitnot-sint ; todo
                                     sint-from-ushort
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitand-ushort-ushort into logand
;; sint is involved because bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitand-ushort-ushort
  (equal (integer-from-sint (bitand-ushort-ushort x y))
         (logand (integer-from-ushort x) (integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable bitand-ushort-ushort
                                     bitand-sint-sint ; todo
                                     sint-from-ushort
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitior-ushort-ushort into logior
;; sint is involved because bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitior-ushort-ushort
  (equal (integer-from-sint (bitior-ushort-ushort x y))
         (logior (integer-from-ushort x) (integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable bitior-ushort-ushort
                                     bitior-sint-sint ; todo
                                     sint-from-ushort
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))

;; Converts bitxor-ushort-ushort into logxor
;; sint is involved because bitand-ushort-ushort returns a sint
(defthmd integer-from-sint-of-bitxor-ushort-ushort
  (equal (integer-from-sint (bitxor-ushort-ushort x y))
         (logxor (integer-from-ushort x) (integer-from-ushort y)))
  :hints (("Goal" :in-theory (enable bitxor-ushort-ushort
                                     bitxor-sint-sint ; todo
                                     sint-from-ushort
                                     sint-integer-fix
                                     sint-integerp
                                     int-bits))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable ushort-removal-rules.

(defthm ushortp-of-declar
  (equal (ushortp (declar x))
         (ushortp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm ushortp-of-assign
  (equal (ushortp (assign x))
         (ushortp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not used yet?
(deftheory ushort-removal-rules
    '(assign
      declar
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
      add-ushort-ushort-okp
      sub-ushort-ushort-okp
      mul-ushort-ushort-okp
      div-ushort-ushort-okp
      rem-ushort-ushort-okp
      shl-ushort-ushort-okp
      shr-ushort-ushort-okp
      ushort-integerp ; exposes unsigned-byte-p
      short-bits
      ;; ushort-dec-const ; doesn't exit
      )
  :redundant-okp t)

;; This theory introduces C operators
(deftheory ushort-intro-rules
    '(ushort-from-integer-of-+-of---arg1
      ushort-from-integer-of-+-of---arg2)
  :redundant-okp t)
