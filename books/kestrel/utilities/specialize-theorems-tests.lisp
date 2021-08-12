; Tests of specialize-theorems
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "specialize-theorems")

(specialize-theorem 'car-cons '-with-x-3 '((x . 3)))

(specialize-theorems '(car-cons associativity-of-+) '-with-x-3 '((x . 3)))
