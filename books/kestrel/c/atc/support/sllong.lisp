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

(in-theory (disable (:e sllong-from-integer)
                    (:e sllong-dec-const) ; ensures these are retained by simplify
                    (:e sllong-hex-const)
                    (:e sllong-oct-const)))

;; These can sometimes save us from having to enable sllong-removal-rules.

(defthm sllongp-of-declar
  (equal (sllongp (declar x))
         (sllongp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm sllongp-of-assign
  (equal (sllongp (assign x))
         (sllongp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This ruleset turns C operations into ACL2 arithmetic operations
;; It often has to be enabled in guard and termination proofs:
;; todo: improve the name
(deftheory sllong-removal-rules
  '(assign
    declar
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
    ;; sub-sllong-sllong-okp
    ;; add-sllong-sllong-okp
    ;; minus-sllong-okp
    ;; mul-sllong-sllong-okp
    ;; div-sllong-sllong-okp
    ;; rem-sllong-sllong-okp
    ;; shl-sllong-sllong-okp
    ;; shr-sllong-sllong-okp
    sllong-integerp ; exposes signed-byte-p
    llong-bits
    sllong-dec-const ; exposes sllong-from-integer
    sllong-hex-const ; exposes sllong-from-integer
    sllong-oct-const ; exposes sllong-from-integer
    )
  :redundant-okp t)

;; This theory introduces C operators
(deftheory sllong-intro-rules
    '(;;ushort-from-integer-of-+-of---arg1
      ;;ushort-from-integer-of-+-of---arg2
      )
  :redundant-okp t)
