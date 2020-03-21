; Crypto Library: Tests of pad-to-896
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PADDING")

(include-book "pad-to-896")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)

;; Does not include the length field.
(acl2::assert-equal
 (pad-to-896 (acl2::bytes-to-bits (list #b01100001 #b01100010 #b01100011)))
 (append (acl2::bytes-to-bits (list #b01100001 #b01100010 #b01100011))
         (list 1)
         (repeat 871 0)))
