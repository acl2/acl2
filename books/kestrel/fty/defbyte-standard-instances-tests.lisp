; FTY -- Standard Byte Fixtype Instances -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbyte-standard-instances")

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
