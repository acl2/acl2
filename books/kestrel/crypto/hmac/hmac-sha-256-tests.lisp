; Tests of HMAC-SHA-256
;
; Copyright (C) 2018-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HMAC")

(include-book "hmac-sha-256")
(include-book "../../../std/testing/assert-equal")

;; Tests from https://tools.ietf.org/html/rfc4231

;; Test Case 1
(acl2::assert-equal (hmac-sha-256 '(#x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b)
                                  (bytes-to-bits '(#x48 #x69 #x20 #x54 #x68 #x65 #x72 #x65)))
                    '(#xb0 #x34 #x4c #x61 #xd8 #xdb #x38 #x53 #x5c #xa8 #xaf #xce #xaf #x0b #xf1 #x2b #x88 #x1d #xc2 #x00 #xc9 #x83 #x3d #xa7 #x26 #xe9 #x37 #x6c #x2e #x32 #xcf #xf7))

;; Test Case 2
(acl2::assert-equal (hmac-sha-256 '(#x4a #x65 #x66 #x65)
                                  (bytes-to-bits '(#x77 #x68 #x61 #x74 #x20 #x64 #x6f #x20 #x79 #x61 #x20 #x77 #x61 #x6e #x74 #x20 #x66 #x6f #x72 #x20 #x6e #x6f #x74 #x68 #x69 #x6e #x67 #x3f)))
                    '(#x5b #xdc #xc1 #x46 #xbf #x60 #x75 #x4e #x6a #x04 #x24 #x26 #x08 #x95 #x75 #xc7 #x5a #x00 #x3f #x08 #x9d #x27 #x39 #x83 #x9d #xec #x58 #xb9 #x64 #xec #x38 #x43))

;; Test Case 3
(acl2::assert-equal (hmac-sha-256 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa)
                                  (bytes-to-bits '(#xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd)))
                    '(#x77 #x3e #xa9 #x1e #x36 #x80 #x0e #x46 #x85 #x4d #xb8 #xeb #xd0 #x91 #x81 #xa7 #x29 #x59 #x09 #x8b #x3e #xf8 #xc1 #x22 #xd9 #x63 #x55 #x14 #xce #xd5 #x65 #xfe))

;; Test Case 4
(acl2::assert-equal (hmac-sha-256 '(#x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19)
                                  (bytes-to-bits '(#xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd)))
                    '(#x82 #x55 #x8a #x38 #x9a #x44 #x3c #x0e #xa4 #xcc #x81 #x98 #x99 #xf2 #x08 #x3a #x85 #xf0 #xfa #xa3 #xe5 #x78 #xf8 #x07 #x7a #x2e #x3f #xf4 #x67 #x29 #x66 #x5b))

;; Test Case 5
(acl2::assert-equal (take 16
                          (hmac-sha-256 '(#x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c)
                                        (bytes-to-bits '(#x54 #x65 #x73 #x74 #x20 #x57 #x69 #x74 #x68 #x20 #x54 #x72 #x75 #x6e #x63 #x61 #x74 #x69 #x6f #x6e))))
                    '(#xa3 #xb6 #x16 #x74 #x73 #x10 #x0e #xe0 #x6e #x0c #x79 #x6c #x29 #x55 #x55 #x2b ))

;; Test Case 6
(acl2::assert-equal (hmac-sha-256 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa )
                                  (bytes-to-bits '(#x54 #x65 #x73 #x74 #x20 #x55 #x73 #x69 #x6e #x67 #x20 #x4c #x61 #x72 #x67 #x65 #x72 #x20 #x54 #x68 #x61 #x6e #x20 #x42 #x6c #x6f #x63 #x6b #x2d #x53 #x69 #x7a #x65 #x20 #x4b #x65 #x79 #x20 #x2d #x20 #x48 #x61 #x73 #x68 #x20 #x4b #x65 #x79 #x20 #x46 #x69 #x72 #x73 #x74)))
                    '(#x60 #xe4 #x31 #x59 #x1e #xe0 #xb6 #x7f #x0d #x8a #x26 #xaa #xcb #xf5 #xb7 #x7f #x8e #x0b #xc6 #x21 #x37 #x28 #xc5 #x14 #x05 #x46 #x04 #x0f #x0e #xe3 #x7f #x54))

;; Test Case 7
(acl2::assert-equal (hmac-sha-256 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa )
                                  (bytes-to-bits '(#x54 #x68 #x69 #x73 #x20 #x69 #x73 #x20 #x61 #x20 #x74 #x65 #x73 #x74 #x20 #x75 #x73 #x69 #x6e #x67 #x20 #x61 #x20 #x6c #x61 #x72 #x67 #x65 #x72 #x20 #x74 #x68 #x61 #x6e #x20 #x62 #x6c #x6f #x63 #x6b #x2d #x73 #x69 #x7a #x65 #x20 #x6b #x65 #x79 #x20 #x61 #x6e #x64 #x20 #x61 #x20 #x6c #x61 #x72 #x67 #x65 #x72 #x20 #x74 #x68 #x61 #x6e #x20 #x62 #x6c #x6f #x63 #x6b #x2d #x73 #x69 #x7a #x65 #x20 #x64 #x61 #x74 #x61 #x2e #x20 #x54 #x68 #x65 #x20 #x6b #x65 #x79 #x20 #x6e #x65 #x65 #x64 #x73 #x20 #x74 #x6f #x20 #x62 #x65 #x20 #x68 #x61 #x73 #x68 #x65 #x64 #x20 #x62 #x65 #x66 #x6f #x72 #x65 #x20 #x62 #x65 #x69 #x6e #x67 #x20 #x75 #x73 #x65 #x64 #x20 #x62 #x79 #x20 #x74 #x68 #x65 #x20 #x48 #x4d #x41 #x43 #x20 #x61 #x6c #x67 #x6f #x72 #x69 #x74 #x68 #x6d #x2e )))
                    '(#x9b #x09 #xff #xa7 #x1b #x94 #x2f #xcb #x27 #x63 #x5f #xbc #xd5 #xb0 #xe9 #x44 #xbf #xdc #x63 #x64 #x4f #x07 #x13 #x93 #x8a #x7f #x51 #x53 #x5c #x3a #x35 #xe2))
