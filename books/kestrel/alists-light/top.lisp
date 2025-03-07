; Top book for the alists-light library
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Books about built-in functions:
(include-book "alistp")
(include-book "acons")
(include-book "assoc-equal")
(include-book "rassoc-equal")
(include-book "strip-cars")
(include-book "strip-cdrs")
(include-book "remove-assoc-equal")

;; Books about new functions:
(include-book "acons-unique")
(include-book "clear-keys")
(include-book "keep-pairs")
(include-book "lookup-eq-def")
(include-book "lookup-eq")
(include-book "lookup-equal-def")
(include-book "lookup-equal")
(include-book "lookup")
(include-book "lookup-eq-required")
(include-book "lookup-eq-safe")
(include-book "lookup-equal-safe")
(include-book "lookup-safe")
(include-book "lookup-eq-lst")
(include-book "map-lookup-equal")
(include-book "pairlis-dollar")
(include-book "pairlis-dollar-fast")
(include-book "uniquify-alist-eq")
(include-book "alists-equiv-on")

;; Books mixing built-in and new functions:
(include-book "strip-cars2")

;; Typed alists (TODO: Consider moving to a new dir):
(include-book "symbol-alistp")
(include-book "maybe-replace-var")
(include-book "string-string-alistp")
(include-book "symbol-symbol-alistp-def")
(include-book "symbol-symbol-alistp")
(include-book "term-alists")
