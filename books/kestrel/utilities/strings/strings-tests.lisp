; String Utilities -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)s
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "strings")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nonempty-stringp "ab"))

(assert! (not (nonempty-stringp "")))

(assert! (not (nonempty-stringp 33)))

(assert! (not (nonempty-stringp '(1 g))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nats=>string nil) "")

(assert-equal (nats=>string '(72 32 109)) "H m")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (string=>nats "") nil)

(assert-equal (string=>nats "#if") '(35 105 102))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexstring nil)
              "")

(assert-equal (ubyte8s=>hexstring '(0))
              "00")

(assert-equal (ubyte8s=>hexstring '(1 2 3))
              "010203")

(assert-equal (ubyte8s=>hexstring '(70 160 180 255 11))
              "46A0B4FF0B")
