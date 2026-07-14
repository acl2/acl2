; C support material dealing with slongs
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
;(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
;(local (include-book "sint")) ; for things like integer-from-sint-of-sub-sint-sint

(in-theory (disable (:e slong-from-integer)
                    (:e slong-dec-const) ; ensures these are retained by simplify
                    (:e slong-hex-const)
                    (:e slong-oct-const)))

(defthm <=-of-slong-fix-linear
  (<= -9223372036854775808 (slong-integer-fix value))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable slong-integer-fix slong-integerp long-bits))))

(defthm <-of-slong-fix-linear
  (<= (slong-integer-fix value) 9223372036854775807)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable slong-integer-fix slong-integerp long-bits))))

(defthm <=-of-integer-from-slong-linear
  (<= -9223372036854775808 (integer-from-slong value))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-slong))))

;todo: tighten this and others
(defthm <-of-integer-from-slong-linear
  (<= (integer-from-slong value) 9223372036854775807)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-slong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable slong-removal-rules.

(defthm slongp-of-declar
  (equal (slongp (declar x))
         (slongp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm slongp-of-assign
  (equal (slongp (assign x))
         (slongp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This ruleset turns C operations into ACL2 arithmetic operations
;; It often has to be enabled in guard and termination proofs:
;; todo: improve the name
(deftheory slong-removal-rules
  '(assign
    declar
    ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
    ;; and rewrite/open functions like add-slong-slong without conversion wrappers outside of them:
    ;; integer-from-slong-of-add-slong-slong
    ;; integer-from-slong-of-sub-slong-slong
    ;; integer-from-slong-of-minus-slong
    ;; integer-from-slong-of-mul-slong-slong
    ;; boolean-from-slong-of-lt-slong-slong
    ;; boolean-from-slong-of-le-slong-slong
    ;; boolean-from-slong-of-gt-slong-slong
    ;; boolean-from-slong-of-ge-slong-slong
    ;; boolean-from-slong-of-eq-slong-slong
    ;; boolean-from-slong-of-ne-slong-slong
    ;; boolean-from-slong-of-lognot-slong
    ;; sub-slong-slong-okp
    ;; add-slong-slong-okp
    ;; minus-slong-okp
    ;; mul-slong-slong-okp
    ;; div-slong-slong-okp
    ;; rem-slong-slong-okp
    ;; shl-slong-slong-okp
    ;; shr-slong-slong-okp
    slong-integerp ; exposes signed-byte-p
    long-bits
    slong-dec-const ; exposes slong-from-integer
    slong-hex-const ; exposes slong-from-integer
    slong-oct-const ; exposes slong-from-integer
    )
  :redundant-okp t)
