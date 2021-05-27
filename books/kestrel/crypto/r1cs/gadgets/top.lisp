; Top file for gadget recognition rules
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "boolean-rules")
(include-book "boolean-alt-rules")
;; (No special rules seem needed for conditional equality.)
(include-book "selection-rules")
(include-book "nonzero-rules")
(include-book "xor-rules")
