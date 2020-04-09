; Tests of packbv and unpackbv
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-def")
(include-book "unpackbv")
(include-book "../../std/testing/assert-equal")

;; Pack 3 items of size 4 into a single bv
(assert-equal (packbv 3 4 '(#b1111 #b0000 #b0101)) #b111100000101)

;; Unpack a BV into 3 items of size 4
(assert-equal (unpackbv 3 4 '#b111100000101) '(#b1111 #b0000 #b0101))
