; C support material dealing with sshorts
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

(defthm <=-of-sshort-fix-linear
  (<= -32768 (sshort-integer-fix value))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sshort-integer-fix sshort-integerp short-bits))))

(defthm <-of-sshort-fix-linear
  (<= (sshort-integer-fix value) 32767)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sshort-integer-fix sshort-integerp short-bits))))

(defthm <=-of-integer-from-sshort-linear
  (<= -32768 (integer-from-sshort value))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-sshort))))

(defthm <-of-integer-from-sshort-linear
  (<= (integer-from-sshort value) 32767)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable integer-from-sshort))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can sometimes save us from having to enable sshort-removal-rules.

(defthm sshortp-of-declar
  (equal (sshortp (declar x))
         (sshortp x))
  :hints (("Goal" :in-theory (enable declar))))

(defthm sshortp-of-assign
  (equal (sshortp (assign x))
         (sshortp x))
  :hints (("Goal" :in-theory (enable assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory sshort-removal-rules
    '(assign
      declar
      ;; ;; these are triggered by conversion functions on the outside.  if needed we could be more aggressive
      ;; ;; and rewrite/open functions like add-uint-uint without conversion wrappers outside of them:
      ;; integer-from-uint-of-add-uint-uint ; or we could introduce bvplus
      ;; integer-from-uint-of-sub-uint-uint
      ;; integer-from-sint-of-bitnot-sshort
      ;; integer-from-sint-of-bitand-sshort-sshort
      ;; integer-from-sint-of-bitior-sshort-sshort
      ;; integer-from-sint-of-bitxor-sshort-sshort
      ;; ;; integer-from-uint-of-shl-uint ; needed?
      ;; integer-from-uint-of-shl-uint-uint
      ;; boolean-from-sint-of-lt-uint-uint
      ;; boolean-from-sint-of-le-uint-uint
      ;; boolean-from-sint-of-gt-uint-uint
      ;; boolean-from-sint-of-ge-uint-uint
      ;; boolean-from-sint-of-eq-uint-uint
      ;; boolean-from-sint-of-ne-uint-uint
      ;; add-uchar-uchar-okp
      ;; div-uchar-uchar-okp
      ;; minus-uchar-okp
      ;; mul-uchar-uchar-okp
      ;; rem-uchar-uchar-okp
      ;; shl-uchar-okp
      ;; shl-uchar-uchar-okp
      ;; shr-uchar-okp
      ;; shr-uchar-uchar-okp
      ;; sub-uchar-uchar-okp
;;      sshort-integerp ; exposes signed-byte-p
;;      char-bits
      ;; sshort-dec-const ; does not exist
      )
  :redundant-okp t)

;; This theory introduces C operators
(deftheory sshort-intro-rules
    '(;;ushort-from-integer-of-+-of---arg1
      ;;ushort-from-integer-of-+-of---arg2
      )
  :redundant-okp t)
