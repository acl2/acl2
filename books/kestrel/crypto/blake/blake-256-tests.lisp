; Tests for BLAKE-256
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "blake-256")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/bv-lists/string-to-bits" :dir :system)

;; From https://131002.net/blake/blake.pdf.

(acl2::assert-equal (blake-256-bytes (list 0))
                    '(#x0C #xE8 #xD4 #xEF  #x4D #xD7 #xCD #x8D  #x62 #xDF #xDE #xD9  #xD4 #xED #xB0 #xA7  #x74 #xAE #x6A #x41  #x92 #x9A #x74 #xDA  #x23 #x10 #x9E #x8F  #x11 #x13 #x9C #x87))

;; 576 bits, all zeros, is 72 bytes, all zeros.
(acl2::assert-equal (blake-256-bytes (repeat (/ 576 8) 0))
                    '(#xD4 #x19 #xBA #xD3  #x2D #x50 #x4F #xB7  #xD4 #x4D #x46 #x0C  #x42 #xC5 #x59 #x3F  #xE5 #x44 #xFA #x4C  #x13 #x5D #xEC #x31  #xE2 #x1B #xD9 #xAB  #xDC #xC2 #x2D #x41))

;; From https://www.seanet.com/~bugbee/crypto/blake/blake_test.py

(acl2::assert-equal (blake-256-bytes (acl2::string-to-bytes "Kilroy was here!"))
                    '(#xb2 #x5c #x02 #xcc #xfa #x1f #x66 #x4d #x25 #xa1 #x5d #x99 #x9b #x56 #xa4 #xbe #x1a #xd8 #x4a #x02 #x9a #x96 #xbe #x5d #x65 #x43 #x87 #xa2 #xde #xf9 #x99 #x16))

(acl2::assert-equal (blake-256-bytes (repeat 55 0))
                    '(#xdc #x98 #x05 #x44 #xf4 #x18 #x1c #xc4 #x35 #x05 #x31 #x8e #x31 #x7c #xdf #xd4 #x33 #x4d #xab #x81 #xae #x03 #x5a #x28 #x81 #x83 #x08 #x86 #x7c #xe2 #x30 #x60 ))

(acl2::assert-equal (blake-256-bytes (repeat 56 0))
                    '(#x26 #xae #x7c #x28 #x9e #xbb #x79 #xc9 #xf3 #xaf #x22 #x85 #x02 #x3a #xb1 #x03 #x7a #x9a #x6d #xb6 #x3f #x0d #x6b #x6c #x6b #xbd #x19 #x9a #xb1 #x62 #x75 #x08))
