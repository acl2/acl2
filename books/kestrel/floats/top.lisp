; Top level book for floats library
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ieee-floats-helpers") ; could omit
(include-book "ieee-floats")
(include-book "round")
(include-book "ieee-floats-as-bvs")
(include-book "ieee-floats-validation")
(include-book "rtl")
(include-book "rtl-axe")
