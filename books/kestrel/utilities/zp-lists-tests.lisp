; Lists of Values that are not Positive Integers -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "zp-lists")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (zp-listp nil))

(assert! (zp-listp '(0 0 0)))

(assert! (zp-listp '((1) "5" #\c)))

(assert! (not (zp-listp '(0 . 0))))

(assert! (not (zp-listp 1)))

(assert! (not (zp-listp '(1))))

(assert! (not (zp-listp '(0 0 10))))
