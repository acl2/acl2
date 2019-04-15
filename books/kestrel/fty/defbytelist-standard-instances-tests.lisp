; FTY -- Standard Byte List Fixtype Instances -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbytelist-standard-instances")

(include-book "kestrel/utilities/testing" :dir :system)

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
