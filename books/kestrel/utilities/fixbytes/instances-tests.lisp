; Fixtypes for (Lists of) Unsigned and Signed Bytes of Common Sizes -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "instances")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (ubyte8p 0))

(assert! (ubyte8p 100))

(assert! (ubyte8p 255))

(assert! (not (ubyte8p -1)))

(assert! (not (ubyte8p 1000)))

(assert! (not (ubyte8p 4/5)))

(assert! (not (ubyte8p #\u)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8-fix 11) 11)

(assert-equal (with-guard-checking nil (ubyte8-fix "11")) 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (ubyte8-listp nil))

(assert! (ubyte8-listp '(10 20 250)))

(assert! (not (ubyte8-listp '(#\1 20))))

(assert! (not (ubyte8-listp 10)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8-list-fix '(0 50 22 160)) '(0 50 22 160))

(assert-equal (with-guard-checking nil (ubyte8-list-fix 33)) nil)

(assert-equal (with-guard-checking nil (ubyte8-list-fix '(10 2000 "abc" 250)))
              '(10 0 0 250))
