; Top file for the lightweight world utilities
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These require the argument to be a function
(include-book "fn-logicp")
(include-book "fn-programp")
(include-book "fn-definedp")
(include-book "fn-primitivep")

(include-book "defined-functionp")

(include-book "defthm-or-defaxiom-symbolp")
(include-book "function-symbolsp")

(include-book "all-functions-in-world")
(include-book "world-triples-for")
(include-book "world-since-boot-strap")

(include-book "filter-defined-fns")
(include-book "filter-logic-mode-fns")
(include-book "defined-fns-in-term")
