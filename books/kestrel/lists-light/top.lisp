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
(include-book "remove-duplicates-equal")
(include-book "remove-equal")
(include-book "remove1-equal")
(include-book "union-equal")
(include-book "intersection-equal")
(include-book "add-to-set-equal")
(include-book "set-difference-equal")
(include-book "subsequencep")
(include-book "length")

;; Books about non-built-in functions:
(include-book "equiv-def")
(include-book "find-index")
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
(include-book "repeat-tail")
(include-book "subrange-def")
(include-book "subrange")
(include-book "subsequencep-equal")
(include-book "update-nth2")
(include-book "last-elem")
(include-book "finalcdr")
(include-book "all-equal-dollar")
(include-book "all-equal-dollar2")
(include-book "all-eql-dollar")
(include-book "all-same")
(include-book "all-same-eql")
(include-book "update-subrange")
(include-book "add-to-end")
(include-book "first-non-member")
(include-book "count-occs")
(include-book "prefixp")
(include-book "prefixp2")
(include-book "remove-nth")

(include-book "len-at-least")

(include-book "take2")
(include-book "memberp2")

(include-book "group")
(include-book "group2")
(include-book "ungroup")
(include-book "group-and-ungroup")
(include-book "group-rules")

(include-book "rules")
(include-book "rules2")

(include-book "append-with-key")

(include-book "union-eql-tail")

(include-book "replace-item")
