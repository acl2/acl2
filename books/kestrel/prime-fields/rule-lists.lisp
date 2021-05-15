; Lists of rules about prime fields
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(defun add-and-mul-normalization-rules ()
  (declare (xargs :guard t))
  '(add-associative
    add-commutative-axe
    add-commutative-2-axe
    mul-associative
    mul-commutative-axe
    mul-commutative-2-axe))

(defun prime-field-proof-rules ()
  (declare (xargs :guard t))
  '(mul-of-1-arg1
    mul-of-1-arg2
    add-of-0-arg1
    add-of-0-arg2
    mul-constant-opener
    add-constant-opener
    fep-constant-opener
    fep-of-mul
    fep-of-add
    integerp-of-mul
    pow-opener
    pow-of-0-arg2
    add-commutative-axe
    add-commutative-2-axe
    mul-associative
    mul-of-mod-arg1
    mul-of-mod-arg2
    ;; this one has a free var which can be expensive to relieve.  we could specialize it for the prime of interest if we need it:
    ;;integerp-when-fep
    ))

(defun bitp-idiom-rules ()
  (declare (xargs :guard t))
  '(bitp-idiom-1
    bitp-idiom-1-alt
    bitp-idiom-2
    bitp-idiom-2-alt
    bitp-idiom-with-constant-1
    bitp-idiom-with-constant-1-alt))
