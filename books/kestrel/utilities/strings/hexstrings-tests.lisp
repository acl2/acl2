; String Utilities -- Conversions from 8-Bit Bytes to Hex Strings -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "hexstrings")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexstring nil)
              "")

(assert-equal (ubyte8s=>hexstring '(0))
              "00")

(assert-equal (ubyte8s=>hexstring '(1 2 3))
              "010203")

(assert-equal (ubyte8s=>hexstring '(70 160 180 255 11))
              "46A0B4FF0B")
