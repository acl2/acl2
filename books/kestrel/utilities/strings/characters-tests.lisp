; Character Utilities -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nats=>chars nil) nil)

(assert-equal (nats=>chars '(65 99 46)) '(#\A #\c #\.))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (chars=>nats nil) nil)

(assert-equal (chars=>nats '(#\a #\5 #\~)) '(97 53 126))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexchars nil)
              nil)

(assert-equal (ubyte8s=>hexchars '(0 1 2 3))
              '(#\0 #\0 #\0 #\1 #\0 #\2 #\0 #\3))

(assert-equal (ubyte8s=>hexchars '(240 15 169))
              '(#\F #\0 #\0 #\F #\A #\9))
