; Tests of HMAC-SHA-512
;
; Copyright (C) 2018-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HMAC")

(include-book "hmac-sha-512")
(include-book "../../../std/testing/assert-equal")

;; Tests from https://tools.ietf.org/html/rfc4231

;; Test Case 1
(acl2::assert-equal (hmac-sha-512 '(#x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b #x0b)
                                  (bytes-to-bits '(#x48 #x69 #x20 #x54 #x68 #x65 #x72 #x65)))
                    '(#x87 #xaa #x7c #xde #xa5 #xef #x61 #x9d #x4f #xf0 #xb4 #x24 #x1a #x1d #x6c #xb0 #x23 #x79 #xf4 #xe2 #xce #x4e #xc2 #x78 #x7a #xd0 #xb3 #x05 #x45 #xe1 #x7c #xde #xda #xa8 #x33 #xb7 #xd6 #xb8 #xa7 #x02 #x03 #x8b #x27 #x4e #xae #xa3 #xf4 #xe4 #xbe #x9d #x91 #x4e #xeb #x61 #xf1 #x70 #x2e #x69 #x6c #x20 #x3a #x12 #x68 #x54))

;; Test Case 2
(acl2::assert-equal (hmac-sha-512 '(#x4a #x65 #x66 #x65)
                                  (bytes-to-bits '(#x77 #x68 #x61 #x74 #x20 #x64 #x6f #x20 #x79 #x61 #x20 #x77 #x61 #x6e #x74 #x20 #x66 #x6f #x72 #x20 #x6e #x6f #x74 #x68 #x69 #x6e #x67 #x3f)))
                    '(#x16 #x4b #x7a #x7b #xfc #xf8 #x19 #xe2 #xe3 #x95 #xfb #xe7 #x3b #x56 #xe0 #xa3 #x87 #xbd #x64 #x22 #x2e #x83 #x1f #xd6 #x10 #x27 #x0c #xd7 #xea #x25 #x05 #x54 #x97 #x58 #xbf #x75 #xc0 #x5a #x99 #x4a #x6d #x03 #x4f #x65 #xf8 #xf0 #xe6 #xfd #xca #xea #xb1 #xa3 #x4d #x4a #x6b #x4b #x63 #x6e #x07 #x0a #x38 #xbc #xe7 #x37))

;; Test Case 3
(acl2::assert-equal (hmac-sha-512 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa)
                                  (bytes-to-bits '(#xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd #xdd)))
                    '(#xfa #x73 #xb0 #x08 #x9d #x56 #xa2 #x84 #xef #xb0 #xf0 #x75 #x6c #x89 #x0b #xe9 #xb1 #xb5 #xdb #xdd #x8e #xe8 #x1a #x36 #x55 #xf8 #x3e #x33 #xb2 #x27 #x9d #x39 #xbf #x3e #x84 #x82 #x79 #xa7 #x22 #xc8 #x06 #xb4 #x85 #xa4 #x7e #x67 #xc8 #x07 #xb9 #x46 #xa3 #x37 #xbe #xe8 #x94 #x26 #x74 #x27 #x88 #x59 #xe1 #x32 #x92 #xfb))

;; Test Case 4
(acl2::assert-equal (hmac-sha-512 '(#x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19)
                                  (bytes-to-bits '(#xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd #xcd)))
                    '(#xb0 #xba #x46 #x56 #x37 #x45 #x8c #x69 #x90 #xe5 #xa8 #xc5 #xf6 #x1d #x4a #xf7 #xe5 #x76 #xd9 #x7f #xf9 #x4b #x87 #x2d #xe7 #x6f #x80 #x50 #x36 #x1e #xe3 #xdb #xa9 #x1c #xa5 #xc1 #x1a #xa2 #x5e #xb4 #xd6 #x79 #x27 #x5c #xc5 #x78 #x80 #x63 #xa5 #xf1 #x97 #x41 #x12 #x0c #x4f #x2d #xe2 #xad #xeb #xeb #x10 #xa2 #x98 #xdd))

;; Test Case 5
(acl2::assert-equal (take 16
                          (hmac-sha-512 '(#x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c #x0c)
                                        (bytes-to-bits '(#x54 #x65 #x73 #x74 #x20 #x57 #x69 #x74 #x68 #x20 #x54 #x72 #x75 #x6e #x63 #x61 #x74 #x69 #x6f #x6e))))
                    '(#x41 #x5f #xad #x62 #x71 #x58 #x0a #x53 #x1d #x41 #x79 #xbc #x89 #x1d #x87 #xa6))

;; Test Case 6
(acl2::assert-equal (hmac-sha-512 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa )
                                  (bytes-to-bits '(#x54 #x65 #x73 #x74 #x20 #x55 #x73 #x69 #x6e #x67 #x20 #x4c #x61 #x72 #x67 #x65 #x72 #x20 #x54 #x68 #x61 #x6e #x20 #x42 #x6c #x6f #x63 #x6b #x2d #x53 #x69 #x7a #x65 #x20 #x4b #x65 #x79 #x20 #x2d #x20 #x48 #x61 #x73 #x68 #x20 #x4b #x65 #x79 #x20 #x46 #x69 #x72 #x73 #x74)))
                    '(#x80 #xb2 #x42 #x63 #xc7 #xc1 #xa3 #xeb #xb7 #x14 #x93 #xc1 #xdd #x7b #xe8 #xb4 #x9b #x46 #xd1 #xf4 #x1b #x4a #xee #xc1 #x12 #x1b #x01 #x37 #x83 #xf8 #xf3 #x52 #x6b #x56 #xd0 #x37 #xe0 #x5f #x25 #x98 #xbd #x0f #xd2 #x21 #x5d #x6a #x1e #x52 #x95 #xe6 #x4f #x73 #xf6 #x3f #x0a #xec #x8b #x91 #x5a #x98 #x5d #x78 #x65 #x98))

;; Test Case 7
(acl2::assert-equal (hmac-sha-512 '(#xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa #xaa )
                                  (bytes-to-bits '(#x54 #x68 #x69 #x73 #x20 #x69 #x73 #x20 #x61 #x20 #x74 #x65 #x73 #x74 #x20 #x75 #x73 #x69 #x6e #x67 #x20 #x61 #x20 #x6c #x61 #x72 #x67 #x65 #x72 #x20 #x74 #x68 #x61 #x6e #x20 #x62 #x6c #x6f #x63 #x6b #x2d #x73 #x69 #x7a #x65 #x20 #x6b #x65 #x79 #x20 #x61 #x6e #x64 #x20 #x61 #x20 #x6c #x61 #x72 #x67 #x65 #x72 #x20 #x74 #x68 #x61 #x6e #x20 #x62 #x6c #x6f #x63 #x6b #x2d #x73 #x69 #x7a #x65 #x20 #x64 #x61 #x74 #x61 #x2e #x20 #x54 #x68 #x65 #x20 #x6b #x65 #x79 #x20 #x6e #x65 #x65 #x64 #x73 #x20 #x74 #x6f #x20 #x62 #x65 #x20 #x68 #x61 #x73 #x68 #x65 #x64 #x20 #x62 #x65 #x66 #x6f #x72 #x65 #x20 #x62 #x65 #x69 #x6e #x67 #x20 #x75 #x73 #x65 #x64 #x20 #x62 #x79 #x20 #x74 #x68 #x65 #x20 #x48 #x4d #x41 #x43 #x20 #x61 #x6c #x67 #x6f #x72 #x69 #x74 #x68 #x6d #x2e )))
                    '(#xe3 #x7b #x6a #x77 #x5d #xc8 #x7d #xba #xa4 #xdf #xa9 #xf9 #x6e #x5e #x3f #xfd #xde #xbd #x71 #xf8 #x86 #x72 #x89 #x86 #x5d #xf5 #xa3 #x2d #x20 #xcd #xc9 #x44 #xb6 #x02 #x2c #xac #x3c #x49 #x82 #xb1 #x0d #x5e #xeb #x55 #xc3 #xe4 #xde #x15 #x13 #x46 #x76 #xfb #x6d #xe0 #x44 #x60 #x65 #xc9 #x74 #x40 #xfa #x8c #x6a #x58))
