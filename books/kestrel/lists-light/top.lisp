; Top-level book for the lightweight-lists library.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note: We recommend including just the individual books that you need, rather
;; than including this top.lisp book, which is likely to include material you
;; don't need and which we expect to grow over time.

;; Books about built-in functions:
(include-book "take")
(include-book "cons")
(include-book "nthcdr")
(include-book "cdr")
(include-book "len")
(include-book "true-list-fix")
(include-book "reverse")
(include-book "first-n-ac")
(include-book "member-equal")
(include-book "subsetp-equal")
(include-book "last")
(include-book "nth")
(include-book "update-nth")
(include-book "no-duplicatesp-equal")
(include-book "butlast")
(include-book "append")
(include-book "revappend")
(include-book "remove-equal")
(include-book "remove1-equal")
(include-book "union-equal")
(include-book "intersection-equal")
(include-book "add-to-set-equal")
(include-book "set-difference-equal")

;; Books about non-built-in functions:
(include-book "firstn-def")
(include-book "firstn")
(include-book "repeat")
(include-book "reverse-list-def")
(include-book "reverse-list")
(include-book "memberp-def")
(include-book "memberp")
(include-book "perm-def")
(include-book "perm")
(include-book "perm2")
(include-book "subrange-def")
(include-book "subrange")

;; Typed lists:
(include-book "symbol-listp")
