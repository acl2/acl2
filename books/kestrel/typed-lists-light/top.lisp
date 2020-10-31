; A lightwright library about lists whose elements have particular types
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "character-listp")
(include-book "rational-listp")
(include-book "nat-listp")
(include-book "pseudo-term-listp")
(include-book "symbol-listp")

(include-book "all-true-listp")
(include-book "all-natp")
(include-book "all-integerp")
(include-book "all-integerp2")
(include-book "all-integerp-of-repeat") ;todo: combine with all-integerp2
(include-book "items-have-len")

(include-book "maxelem")
(include-book "minelem")

(include-book "all-less")
