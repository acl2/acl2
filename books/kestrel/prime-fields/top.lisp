; Prime fields library
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep")
(include-book "fep-fix")
(include-book "minus1")
(include-book "add")
(include-book "neg")
(include-book "sub")
(include-book "mul")
(include-book "pow")
(include-book "inv")
(include-book "div")
(include-book "prime-fields")
;; (include-book "prime-fields-alt") ;incompatible
(include-book "prime-fields-rules")
;; (include-book "prime-fields-rules-axe") ;; uncomment after fixing name clash on perm
(include-book "bind-free-rules")
;; (include-book "equal-of-add-rules") ;incompatible with the bind-free rules
(include-book "doc")
(include-book "rule-lists")
(include-book "printing")

(include-book "bitp-idioms")
