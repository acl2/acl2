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

(in-theory (disable (:e c::sllong-from-integer)
                    (:e c::sllong-dec-const) ; ensures these are retained by simplify
                    (:e c::sllong-hex-const)
                    (:e c::sllong-oct-const)))

;; These can sometimes save us from having to enable sllong-removal-rules.

(defthm sllongp-of-declar
  (equal (c::sllongp (c::declar x))
         (c::sllongp x))
  :hints (("Goal" :in-theory (enable c::declar))))

(defthm sllongp-of-assign
  (equal (c::sllongp (c::assign x))
         (c::sllongp x))
  :hints (("Goal" :in-theory (enable c::assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This ruleset turns C operations into ACL2 arithmetic operations
;; It often has to be enabled in guard and termination proofs:
;; todo: improve the name
(deftheory sllong-removal-rules
  '(c::assign
    c::declar
    ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
    ;; and rewrite/open functions like add-sllong-sllong without conversion wrappers outside of them:
    ;; integer-from-sllong-of-add-sllong-sllong
    ;; integer-from-sllong-of-sub-sllong-sllong
    ;; integer-from-sllong-of-minus-sllong
    ;; integer-from-sllong-of-mul-sllong-sllong
    ;; boolean-from-sllong-of-lt-sllong-sllong
    ;; boolean-from-sllong-of-le-sllong-sllong
    ;; boolean-from-sllong-of-gt-sllong-sllong
    ;; boolean-from-sllong-of-ge-sllong-sllong
    ;; boolean-from-sllong-of-eq-sllong-sllong
    ;; boolean-from-sllong-of-ne-sllong-sllong
    ;; boolean-from-sllong-of-lognot-sllong
    ;; c::sub-sllong-sllong-okp
    ;; c::add-sllong-sllong-okp
    ;; c::minus-sllong-okp
    ;; c::mul-sllong-sllong-okp
    ;; c::div-sllong-sllong-okp
    ;; c::rem-sllong-sllong-okp
    ;; c::shl-sllong-sllong-okp
    ;; c::shr-sllong-sllong-okp
    c::sllong-integerp ; exposes signed-byte-p
    c::llong-bits
    c::sllong-dec-const ; exposes sllong-from-integer
    c::sllong-hex-const ; exposes sllong-from-integer
    c::sllong-oct-const ; exposes sllong-from-integer
    )
  :redundant-okp t)
