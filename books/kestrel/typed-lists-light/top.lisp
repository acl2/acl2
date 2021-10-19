; A lightwright library about lists whose elements have particular types
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "character-listp")
(include-book "rational-listp")
(include-book "nat-listp")
(include-book "integer-listp")
(include-book "pseudo-term-listp")
(include-book "pseudo-term-list-listp")
(include-book "string-listp")
(include-book "symbol-listp")
(include-book "symbol-listp2")

(include-book "character-list-listp")

(include-book "all-true-listp")
(include-book "all-natp")
(include-book "all-integerp")
(include-book "all-integerp2")
(include-book "all-integerp-of-repeat") ;todo: combine with all-integerp2
(include-book "all-rationalp")
(include-book "all-all-integerp")
(include-book "all-consp")

(include-book "integer-lists")

(include-book "items-have-len")

(include-book "map-char-code")
(include-book "map-code-char")
(include-book "bytes-to-printable-string")

(include-book "maxelem")
(include-book "maxelem2")
(include-book "minelem")
(include-book "minelem2")

(include-book "all-less")
(include-book "all-less-rules")
(include-book "all-less-than-or-equal")
(include-book "less-than-or-equal-all")
(include-book "all-less-than-or-equal-all")

(include-book "all-greater")

(include-book "cons-listp-dollar")

;; Stuff about lists of alists:
(include-book "all-alistp")
(include-book "map-strip-cars")

(include-book "doc")
