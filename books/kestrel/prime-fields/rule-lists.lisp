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
  '(pfield::add-associative
    pfield::add-commutative-axe
    pfield::add-commutative-2-axe
    pfield::mul-associative
    pfield::mul-commutative-axe
    pfield::mul-commutative-2-axe))

(defun prime-field-proof-rules ()
  (declare (xargs :guard t))
  '(pfield::mul-of-1-arg1
    pfield::mul-of-1-arg2
    pfield::add-of-0-arg1
    pfield::add-of-0-arg2
    pfield::mul-constant-opener
    pfield::add-constant-opener
    pfield::fep-constant-opener
    pfield::fep-of-mul
    pfield::fep-of-add
    pfield::integerp-of-mul
    pfield::pow-opener
    pfield::pow-of-0
    pfield::add-commutative-axe
    pfield::add-commutative-2-axe
    pfield::mul-associative
    pfield::mul-of-mod-arg1
    pfield::mul-of-mod-arg2
    ;; this one has a free var which can be expensive to relieve.  we could specialize it for the prime of interest if we need it:
    ;;pfield::integerp-when-fep
    ))
