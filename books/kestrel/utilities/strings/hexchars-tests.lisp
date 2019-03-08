; String Utilities -- Conversions from 8-Bit Bytes to Hex Characters -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "hexchars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexchars nil)
              nil)

(assert-equal (ubyte8s=>hexchars '(0 1 2 3))
              '(#\0 #\0 #\0 #\1 #\0 #\2 #\0 #\3))

(assert-equal (ubyte8s=>hexchars '(240 15 169))
              '(#\F #\0 #\0 #\F #\A #\9))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (hexchars=>ubyte8s nil)
              nil)

(assert-equal (hexchars=>ubyte8s '(#\0 #\0 #\0 #\1 #\0 #\2 #\0 #\3))
              '(0 1 2 3))

(assert-equal (hexchars=>ubyte8s '(#\F #\0 #\0 #\F #\A #\9))
              '(240 15 169))

(assert-equal (hexchars=>ubyte8s '(#\f #\0 #\0 #\f #\a #\9))
              '(240 15 169))
