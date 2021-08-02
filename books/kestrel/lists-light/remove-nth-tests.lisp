; Tests for remove-nth
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-nth")
(include-book "std/testing/assert-equal" :dir :system)

(assert-event (equal (remove-nth 0 '(a b c)) '(b c)))
(assert-event (equal (remove-nth 1 '(a b c)) '(a c)))
(assert-event (equal (remove-nth 2 '(a b c)) '(a b)))
