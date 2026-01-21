; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "field-samples")

(include-book "projects/aleo/vm/circuits/sampling/prime-field-macros" :dir :system)

(include-book "projects/aleo/vm/circuits/r1cs/field-lt" :dir :system)

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (b* ((x (wvar 0))
             (xs (loop$ for i from 2 to 254 collect (wvar i)))
             (xrs (loop$ for i from 255 to 506 collect (wvar i)))
             (y (wvar 1))
             (ys (loop$ for i from 507 to 759 collect (wvar i)))
             (yrs (loop$ for i from 760 to 1011 collect (wvar i)))
             (ds (loop$ for i from 1012 to 1516 by 2 collect (wvar i)))
             (rs (loop$ for i from 1013 to 1517 by 2 collect (wvar i)))
             (u 'r1cs::|x0|)
             (p (eprime)))
          (aleovm::field-lt-gadget x xs xrs y ys yrs ds rs u p))
        (field-compare--constraints) ; from sample
))
