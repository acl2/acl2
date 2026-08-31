; Tests of the AES block cipher
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AES")

(include-book "aes-spec")
(include-book "kestrel/utilities/deftest" :dir :system)

;; Tests from FIPS-197 (the Advanced Encryption Standard):
;; - the finite field multiplication example from Section 4.2,
;; - the key expansions of Appendix A,
;; - the cipher example of Appendix B,
;;   including its complete round-by-round trace,
;; - and the example vectors of Appendix C of the original (2001)
;;   edition (the 2023 update, FIPS-197-upd1, replaced that appendix
;;   with a pointer to the example vectors on the NIST website).

;; Test from Section 4.2:

(acl2::assert-equal (gf256mult #x57 #x13) #xfe)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tests from Appendix A (key expansions)
;;
(defconst *aes-128-example-key* '(#x2b #x7e #x15 #x16 #x28 #xae #xd2 #xa6 #xab #xf7 #x15 #x88 #x09 #xcf #x4f #x3c))

(defconst *aes-128-example-expanded-key*
  (list (make-word #x2b #x7e #x15 #x16)
        (make-word #x28 #xae #xd2 #xa6)
        (make-word #xab #xf7 #x15 #x88)
        (make-word #x09 #xcf #x4f #x3c)
        (make-word #xa0 #xfa #xfe #x17)
        (make-word #x88 #x54 #x2c #xb1)
        (make-word #x23 #xa3 #x39 #x39)
        (make-word #x2a #x6c #x76 #x05)
        (make-word #xf2 #xc2 #x95 #xf2)
        (make-word #x7a #x96 #xb9 #x43)
        (make-word #x59 #x35 #x80 #x7a)
        (make-word #x73 #x59 #xf6 #x7f)
        (make-word #x3d #x80 #x47 #x7d)
        (make-word #x47 #x16 #xfe #x3e)
        (make-word #x1e #x23 #x7e #x44)
        (make-word #x6d #x7a #x88 #x3b)
        (make-word #xef #x44 #xa5 #x41)
        (make-word #xa8 #x52 #x5b #x7f)
        (make-word #xb6 #x71 #x25 #x3b)
        (make-word #xdb #x0b #xad #x00)
        (make-word #xd4 #xd1 #xc6 #xf8)
        (make-word #x7c #x83 #x9d #x87)
        (make-word #xca #xf2 #xb8 #xbc)
        (make-word #x11 #xf9 #x15 #xbc)
        (make-word #x6d #x88 #xa3 #x7a)
        (make-word #x11 #x0b #x3e #xfd)
        (make-word #xdb #xf9 #x86 #x41)
        (make-word #xca #x00 #x93 #xfd)
        (make-word #x4e #x54 #xf7 #x0e)
        (make-word #x5f #x5f #xc9 #xf3)
        (make-word #x84 #xa6 #x4f #xb2)
        (make-word #x4e #xa6 #xdc #x4f)
        (make-word #xea #xd2 #x73 #x21)
        (make-word #xb5 #x8d #xba #xd2)
        (make-word #x31 #x2b #xf5 #x60)
        (make-word #x7f #x8d #x29 #x2f)
        (make-word #xac #x77 #x66 #xf3)
        (make-word #x19 #xfa #xdc #x21)
        (make-word #x28 #xd1 #x29 #x41)
        (make-word #x57 #x5c #x00 #x6e)
        (make-word #xd0 #x14 #xf9 #xa8)
        (make-word #xc9 #xee #x25 #x89)
        (make-word #xe1 #x3f #x0c #xc8)
        (make-word #xb6 #x63 #x0c #xa6)))

(acl2::assert-equal (keyexpansion *aes-128-example-key* 4) *aes-128-example-expanded-key*)

(defconst *aes-192-example-key* '(#x8e #x73 #xb0 #xf7 #xda #x0e #x64 #x52 #xc8 #x10 #xf3 #x2b #x80 #x90 #x79 #xe5 #x62 #xf8 #xea #xd2 #x52 #x2c #x6b #x7b))

(defconst *aes-192-example-expanded-key*
  (list (make-word #x8e #x73 #xb0 #xf7)
        (make-word #xda #x0e #x64 #x52)
        (make-word #xc8 #x10 #xf3 #x2b)
        (make-word #x80 #x90 #x79 #xe5)
        (make-word #x62 #xf8 #xea #xd2)
        (make-word #x52 #x2c #x6b #x7b)
        (make-word #xfe #x0c #x91 #xf7)
        (make-word #x24 #x02 #xf5 #xa5)
        (make-word #xec #x12 #x06 #x8e)
        (make-word #x6c #x82 #x7f #x6b)
        (make-word #x0e #x7a #x95 #xb9)
        (make-word #x5c #x56 #xfe #xc2)
        (make-word #x4d #xb7 #xb4 #xbd)
        (make-word #x69 #xb5 #x41 #x18)
        (make-word #x85 #xa7 #x47 #x96)
        (make-word #xe9 #x25 #x38 #xfd)
        (make-word #xe7 #x5f #xad #x44)
        (make-word #xbb #x09 #x53 #x86)
        (make-word #x48 #x5a #xf0 #x57)
        (make-word #x21 #xef #xb1 #x4f)
        (make-word #xa4 #x48 #xf6 #xd9)
        (make-word #x4d #x6d #xce #x24)
        (make-word #xaa #x32 #x63 #x60)
        (make-word #x11 #x3b #x30 #xe6)
        (make-word #xa2 #x5e #x7e #xd5)
        (make-word #x83 #xb1 #xcf #x9a)
        (make-word #x27 #xf9 #x39 #x43)
        (make-word #x6a #x94 #xf7 #x67)
        (make-word #xc0 #xa6 #x94 #x07)
        (make-word #xd1 #x9d #xa4 #xe1)
        (make-word #xec #x17 #x86 #xeb)
        (make-word #x6f #xa6 #x49 #x71)
        (make-word #x48 #x5f #x70 #x32)
        (make-word #x22 #xcb #x87 #x55)
        (make-word #xe2 #x6d #x13 #x52)
        (make-word #x33 #xf0 #xb7 #xb3)
        (make-word #x40 #xbe #xeb #x28)
        (make-word #x2f #x18 #xa2 #x59)
        (make-word #x67 #x47 #xd2 #x6b)
        (make-word #x45 #x8c #x55 #x3e)
        (make-word #xa7 #xe1 #x46 #x6c)
        (make-word #x94 #x11 #xf1 #xdf)
        (make-word #x82 #x1f #x75 #x0a)
        (make-word #xad #x07 #xd7 #x53)
        (make-word #xca #x40 #x05 #x38)
        (make-word #x8f #xcc #x50 #x06)
        (make-word #x28 #x2d #x16 #x6a)
        (make-word #xbc #x3c #xe7 #xb5)
        (make-word #xe9 #x8b #xa0 #x6f)
        (make-word #x44 #x8c #x77 #x3c)
        (make-word #x8e #xcc #x72 #x04)
        (make-word #x01 #x00 #x22 #x02)
        ))

(acl2::assert-equal (keyexpansion *aes-192-example-key* 6) *aes-192-example-expanded-key*)

(defconst *aes-256-example-key* '(#x60 #x3d #xeb #x10 #x15 #xca #x71 #xbe #x2b #x73 #xae #xf0 #x85 #x7d #x77 #x81 #x1f #x35 #x2c #x07 #x3b #x61 #x08 #xd7 #x2d #x98 #x10 #xa3 #x09 #x14 #xdf #xf4))

(defconst *aes-256-example-expanded-key*
  (list (make-word #x60 #x3d #xeb #x10)
        (make-word #x15 #xca #x71 #xbe)
        (make-word #x2b #x73 #xae #xf0)
        (make-word #x85 #x7d #x77 #x81)
        (make-word #x1f #x35 #x2c #x07)
        (make-word #x3b #x61 #x08 #xd7)
        (make-word #x2d #x98 #x10 #xa3)
        (make-word #x09 #x14 #xdf #xf4)
        (make-word #x9b #xa3 #x54 #x11)
        (make-word #x8e #x69 #x25 #xaf)
        (make-word #xa5 #x1a #x8b #x5f)
        (make-word #x20 #x67 #xfc #xde)
        (make-word #xa8 #xb0 #x9c #x1a)
        (make-word #x93 #xd1 #x94 #xcd)
        (make-word #xbe #x49 #x84 #x6e)
        (make-word #xb7 #x5d #x5b #x9a)
        (make-word #xd5 #x9a #xec #xb8)
        (make-word #x5b #xf3 #xc9 #x17)
        (make-word #xfe #xe9 #x42 #x48)
        (make-word #xde #x8e #xbe #x96)
        (make-word #xb5 #xa9 #x32 #x8a)
        (make-word #x26 #x78 #xa6 #x47)
        (make-word #x98 #x31 #x22 #x29)
        (make-word #x2f #x6c #x79 #xb3)
        (make-word #x81 #x2c #x81 #xad)
        (make-word #xda #xdf #x48 #xba)
        (make-word #x24 #x36 #x0a #xf2)
        (make-word #xfa #xb8 #xb4 #x64)
        (make-word #x98 #xc5 #xbf #xc9)
        (make-word #xbe #xbd #x19 #x8e)
        (make-word #x26 #x8c #x3b #xa7)
        (make-word #x09 #xe0 #x42 #x14)
        (make-word #x68 #x00 #x7b #xac)
        (make-word #xb2 #xdf #x33 #x16)
        (make-word #x96 #xe9 #x39 #xe4)
        (make-word #x6c #x51 #x8d #x80)
        (make-word #xc8 #x14 #xe2 #x04)
        (make-word #x76 #xa9 #xfb #x8a)
        (make-word #x50 #x25 #xc0 #x2d)
        (make-word #x59 #xc5 #x82 #x39)
        (make-word #xde #x13 #x69 #x67)
        (make-word #x6c #xcc #x5a #x71)
        (make-word #xfa #x25 #x63 #x95)
        (make-word #x96 #x74 #xee #x15)
        (make-word #x58 #x86 #xca #x5d)
        (make-word #x2e #x2f #x31 #xd7)
        (make-word #x7e #x0a #xf1 #xfa)
        (make-word #x27 #xcf #x73 #xc3)
        (make-word #x74 #x9c #x47 #xab)
        (make-word #x18 #x50 #x1d #xda)
        (make-word #xe2 #x75 #x7e #x4f)
        (make-word #x74 #x01 #x90 #x5a)
        (make-word #xca #xfa #xaa #xe3)
        (make-word #xe4 #xd5 #x9b #x34)
        (make-word #x9a #xdf #x6a #xce)
        (make-word #xbd #x10 #x19 #x0d)
        (make-word #xfe #x48 #x90 #xd1)
        (make-word #xe6 #x18 #x8d #x0b)
        (make-word #x04 #x6d #xf3 #x44)
        (make-word #x70 #x6c #x63 #x1e)
        ))

(acl2::assert-equal (keyexpansion *aes-256-example-key* 8) *aes-256-example-expanded-key*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tests from Appendix B (cipher example)
;;

(defconst *aes-128-example-plaintext* '(#x32 #x43 #xf6 #xa8 #x88 #x5a #x30 #x8d #x31 #x31 #x98 #xa2 #xe0 #x37 #x07 #x34))

(defconst *aes-128-example-ciphertext* '(#x39 #x25 #x84 #x1d #x02 #xdc #x09 #xfb #xdc #x11 #x85 #x97 #x19 #x6a #x0b #x32))

(acl2::assert-equal (aes-128-encrypt *aes-128-example-plaintext* *aes-128-example-key*) *aes-128-example-ciphertext*)

(acl2::assert-equal (aes-128-decrypt *aes-128-example-ciphertext* *aes-128-example-key*) *aes-128-example-plaintext*)

(acl2::assert-equal (aes-128-decrypt (aes-128-encrypt *aes-128-example-plaintext* *aes-128-example-key*) *aes-128-example-key*)
                    *aes-128-example-plaintext*)

;;
;; The round-by-round trace of the Appendix B cipher example.
;;
;; For each round, Appendix B gives the state at the start of the
;; round, after SubBytes, after ShiftRows, and after MixColumns
;; (except in the final round, which has no MixColumns), along with
;; the round key.  The 4x4 state arrays shown in the appendix are
;; listed here as 16-byte sequences in column-major order (the order
;; of the corresponding byte arrays).  The round keys are words
;; 4r..4r+3 of the expanded key, already checked in the Appendix A
;; test above.
;;

;; The state after the initial AddRoundKey (the start of round 1):

(defconst *aes-128-round1-start* '(#x19 #x3d #xe3 #xbe #xa0 #xf4 #xe2 #x2b #x9a #xc6 #x8d #x2a #xe9 #xf8 #x48 #x08))

(acl2::assert-equal
 (addroundkey (copyarraytostate *aes-128-example-plaintext*)
              (subrange 0 3 *aes-128-example-expanded-key*))
 (copyarraytostate *aes-128-round1-start*))

;; Round 1:

(defconst *aes-128-round1-after-subbytes* '(#xd4 #x27 #x11 #xae #xe0 #xbf #x98 #xf1 #xb8 #xb4 #x5d #xe5 #x1e #x41 #x52 #x30))
(defconst *aes-128-round1-after-shiftrows* '(#xd4 #xbf #x5d #x30 #xe0 #xb4 #x52 #xae #xb8 #x41 #x11 #xf1 #x1e #x27 #x98 #xe5))
(defconst *aes-128-round1-after-mixcolumns* '(#x04 #x66 #x81 #xe5 #xe0 #xcb #x19 #x9a #x48 #xf8 #xd3 #x7a #x28 #x06 #x26 #x4c))
(defconst *aes-128-round2-start* '(#xa4 #x9c #x7f #xf2 #x68 #x9f #x35 #x2b #x6b #x5b #xea #x43 #x02 #x6a #x50 #x49))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round1-start*))
                    (copyarraytostate *aes-128-round1-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round1-after-subbytes*))
                    (copyarraytostate *aes-128-round1-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round1-after-shiftrows*))
                    (copyarraytostate *aes-128-round1-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round1-after-mixcolumns*)
                                 (subrange 4 7 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round2-start*))

;; Round 2:

(defconst *aes-128-round2-after-subbytes* '(#x49 #xde #xd2 #x89 #x45 #xdb #x96 #xf1 #x7f #x39 #x87 #x1a #x77 #x02 #x53 #x3b))
(defconst *aes-128-round2-after-shiftrows* '(#x49 #xdb #x87 #x3b #x45 #x39 #x53 #x89 #x7f #x02 #xd2 #xf1 #x77 #xde #x96 #x1a))
(defconst *aes-128-round2-after-mixcolumns* '(#x58 #x4d #xca #xf1 #x1b #x4b #x5a #xac #xdb #xe7 #xca #xa8 #x1b #x6b #xb0 #xe5))
(defconst *aes-128-round3-start* '(#xaa #x8f #x5f #x03 #x61 #xdd #xe3 #xef #x82 #xd2 #x4a #xd2 #x68 #x32 #x46 #x9a))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round2-start*))
                    (copyarraytostate *aes-128-round2-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round2-after-subbytes*))
                    (copyarraytostate *aes-128-round2-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round2-after-shiftrows*))
                    (copyarraytostate *aes-128-round2-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round2-after-mixcolumns*)
                                 (subrange 8 11 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round3-start*))

;; Round 3:

(defconst *aes-128-round3-after-subbytes* '(#xac #x73 #xcf #x7b #xef #xc1 #x11 #xdf #x13 #xb5 #xd6 #xb5 #x45 #x23 #x5a #xb8))
(defconst *aes-128-round3-after-shiftrows* '(#xac #xc1 #xd6 #xb8 #xef #xb5 #x5a #x7b #x13 #x23 #xcf #xdf #x45 #x73 #x11 #xb5))
(defconst *aes-128-round3-after-mixcolumns* '(#x75 #xec #x09 #x93 #x20 #x0b #x63 #x33 #x53 #xc0 #xcf #x7c #xbb #x25 #xd0 #xdc))
(defconst *aes-128-round4-start* '(#x48 #x6c #x4e #xee #x67 #x1d #x9d #x0d #x4d #xe3 #xb1 #x38 #xd6 #x5f #x58 #xe7))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round3-start*))
                    (copyarraytostate *aes-128-round3-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round3-after-subbytes*))
                    (copyarraytostate *aes-128-round3-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round3-after-shiftrows*))
                    (copyarraytostate *aes-128-round3-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round3-after-mixcolumns*)
                                 (subrange 12 15 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round4-start*))

;; Round 4:

(defconst *aes-128-round4-after-subbytes* '(#x52 #x50 #x2f #x28 #x85 #xa4 #x5e #xd7 #xe3 #x11 #xc8 #x07 #xf6 #xcf #x6a #x94))
(defconst *aes-128-round4-after-shiftrows* '(#x52 #xa4 #xc8 #x94 #x85 #x11 #x6a #x28 #xe3 #xcf #x2f #xd7 #xf6 #x50 #x5e #x07))
(defconst *aes-128-round4-after-mixcolumns* '(#x0f #xd6 #xda #xa9 #x60 #x31 #x38 #xbf #x6f #xc0 #x10 #x6b #x5e #xb3 #x13 #x01))
(defconst *aes-128-round5-start* '(#xe0 #x92 #x7f #xe8 #xc8 #x63 #x63 #xc0 #xd9 #xb1 #x35 #x50 #x85 #xb8 #xbe #x01))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round4-start*))
                    (copyarraytostate *aes-128-round4-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round4-after-subbytes*))
                    (copyarraytostate *aes-128-round4-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round4-after-shiftrows*))
                    (copyarraytostate *aes-128-round4-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round4-after-mixcolumns*)
                                 (subrange 16 19 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round5-start*))

;; Round 5:

(defconst *aes-128-round5-after-subbytes* '(#xe1 #x4f #xd2 #x9b #xe8 #xfb #xfb #xba #x35 #xc8 #x96 #x53 #x97 #x6c #xae #x7c))
(defconst *aes-128-round5-after-shiftrows* '(#xe1 #xfb #x96 #x7c #xe8 #xc8 #xae #x9b #x35 #x6c #xd2 #xba #x97 #x4f #xfb #x53))
(defconst *aes-128-round5-after-mixcolumns* '(#x25 #xd1 #xa9 #xad #xbd #x11 #xd1 #x68 #xb6 #x3a #x33 #x8e #x4c #x4c #xc0 #xb0))
(defconst *aes-128-round6-start* '(#xf1 #x00 #x6f #x55 #xc1 #x92 #x4c #xef #x7c #xc8 #x8b #x32 #x5d #xb5 #xd5 #x0c))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round5-start*))
                    (copyarraytostate *aes-128-round5-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round5-after-subbytes*))
                    (copyarraytostate *aes-128-round5-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round5-after-shiftrows*))
                    (copyarraytostate *aes-128-round5-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round5-after-mixcolumns*)
                                 (subrange 20 23 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round6-start*))

;; Round 6:

(defconst *aes-128-round6-after-subbytes* '(#xa1 #x63 #xa8 #xfc #x78 #x4f #x29 #xdf #x10 #xe8 #x3d #x23 #x4c #xd5 #x03 #xfe))
(defconst *aes-128-round6-after-shiftrows* '(#xa1 #x4f #x3d #xfe #x78 #xe8 #x03 #xfc #x10 #xd5 #xa8 #xdf #x4c #x63 #x29 #x23))
(defconst *aes-128-round6-after-mixcolumns* '(#x4b #x86 #x8d #x6d #x2c #x4a #x89 #x80 #x33 #x9d #xf4 #xe8 #x37 #xd2 #x18 #xd8))
(defconst *aes-128-round7-start* '(#x26 #x0e #x2e #x17 #x3d #x41 #xb7 #x7d #xe8 #x64 #x72 #xa9 #xfd #xd2 #x8b #x25))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round6-start*))
                    (copyarraytostate *aes-128-round6-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round6-after-subbytes*))
                    (copyarraytostate *aes-128-round6-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round6-after-shiftrows*))
                    (copyarraytostate *aes-128-round6-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round6-after-mixcolumns*)
                                 (subrange 24 27 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round7-start*))

;; Round 7:

(defconst *aes-128-round7-after-subbytes* '(#xf7 #xab #x31 #xf0 #x27 #x83 #xa9 #xff #x9b #x43 #x40 #xd3 #x54 #xb5 #x3d #x3f))
(defconst *aes-128-round7-after-shiftrows* '(#xf7 #x83 #x40 #x3f #x27 #x43 #x3d #xf0 #x9b #xb5 #x31 #xff #x54 #xab #xa9 #xd3))
(defconst *aes-128-round7-after-mixcolumns* '(#x14 #x15 #xb5 #xbf #x46 #x16 #x15 #xec #x27 #x46 #x56 #xd7 #x34 #x2a #xd8 #x43))
(defconst *aes-128-round8-start* '(#x5a #x41 #x42 #xb1 #x19 #x49 #xdc #x1f #xa3 #xe0 #x19 #x65 #x7a #x8c #x04 #x0c))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round7-start*))
                    (copyarraytostate *aes-128-round7-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round7-after-subbytes*))
                    (copyarraytostate *aes-128-round7-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round7-after-shiftrows*))
                    (copyarraytostate *aes-128-round7-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round7-after-mixcolumns*)
                                 (subrange 28 31 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round8-start*))

;; Round 8:

(defconst *aes-128-round8-after-subbytes* '(#xbe #x83 #x2c #xc8 #xd4 #x3b #x86 #xc0 #x0a #xe1 #xd4 #x4d #xda #x64 #xf2 #xfe))
(defconst *aes-128-round8-after-shiftrows* '(#xbe #x3b #xd4 #xfe #xd4 #xe1 #xf2 #xc8 #x0a #x64 #x2c #xc0 #xda #x83 #x86 #x4d))
(defconst *aes-128-round8-after-mixcolumns* '(#x00 #x51 #x2f #xd1 #xb1 #xc8 #x89 #xff #x54 #x76 #x6d #xcd #xfa #x1b #x99 #xea))
(defconst *aes-128-round9-start* '(#xea #x83 #x5c #xf0 #x04 #x45 #x33 #x2d #x65 #x5d #x98 #xad #x85 #x96 #xb0 #xc5))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round8-start*))
                    (copyarraytostate *aes-128-round8-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round8-after-subbytes*))
                    (copyarraytostate *aes-128-round8-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round8-after-shiftrows*))
                    (copyarraytostate *aes-128-round8-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round8-after-mixcolumns*)
                                 (subrange 32 35 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round9-start*))

;; Round 9:

(defconst *aes-128-round9-after-subbytes* '(#x87 #xec #x4a #x8c #xf2 #x6e #xc3 #xd8 #x4d #x4c #x46 #x95 #x97 #x90 #xe7 #xa6))
(defconst *aes-128-round9-after-shiftrows* '(#x87 #x6e #x46 #xa6 #xf2 #x4c #xe7 #x8c #x4d #x90 #x4a #xd8 #x97 #xec #xc3 #x95))
(defconst *aes-128-round9-after-mixcolumns* '(#x47 #x37 #x94 #xed #x40 #xd4 #xe4 #xa5 #xa3 #x70 #x3a #xa6 #x4c #x9f #x42 #xbc))
(defconst *aes-128-round10-start* '(#xeb #x40 #xf2 #x1e #x59 #x2e #x38 #x84 #x8b #xa1 #x13 #xe7 #x1b #xc3 #x42 #xd2))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round9-start*))
                    (copyarraytostate *aes-128-round9-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round9-after-subbytes*))
                    (copyarraytostate *aes-128-round9-after-shiftrows*))
(acl2::assert-equal (mixcolumns (copyarraytostate *aes-128-round9-after-shiftrows*))
                    (copyarraytostate *aes-128-round9-after-mixcolumns*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round9-after-mixcolumns*)
                                 (subrange 36 39 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-round10-start*))

;; Round 10 (the final round, with no MixColumns):

(defconst *aes-128-round10-after-subbytes* '(#xe9 #x09 #x89 #x72 #xcb #x31 #x07 #x5f #x3d #x32 #x7d #x94 #xaf #x2e #x2c #xb5))
(defconst *aes-128-round10-after-shiftrows* '(#xe9 #x31 #x7d #xb5 #xcb #x32 #x2c #x72 #x3d #x2e #x89 #x5f #xaf #x09 #x07 #x94))

(acl2::assert-equal (subbytes (copyarraytostate *aes-128-round10-start*))
                    (copyarraytostate *aes-128-round10-after-subbytes*))
(acl2::assert-equal (shiftrows (copyarraytostate *aes-128-round10-after-subbytes*))
                    (copyarraytostate *aes-128-round10-after-shiftrows*))
(acl2::assert-equal (addroundkey (copyarraytostate *aes-128-round10-after-shiftrows*)
                                 (subrange 40 43 *aes-128-example-expanded-key*))
                    (copyarraytostate *aes-128-example-ciphertext*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tests from Appendix C of the original (2001) FIPS-197
;; (example vectors for all three key lengths)
;;

;The same plaintext for all key lengths.
(defconst *aes-test-plaintext* '(#x00 #x11 #x22 #x33 #x44 #x55 #x66 #x77 #x88 #x99 #xaa #xbb #xcc #xdd #xee #xff))

(defconst *aes-test-key-128* '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f))

(defconst *aes-test-ciphertext-128* '(#x69 #xc4 #xe0 #xd8 #x6a #x7b #x04 #x30 #xd8 #xcd #xb7 #x80 #x70 #xb4 #xc5 #x5a))

(acl2::assert-equal (aes-128-encrypt *aes-test-plaintext* *aes-test-key-128*) *aes-test-ciphertext-128*)

(acl2::assert-equal (aes-128-decrypt *aes-test-ciphertext-128* *aes-test-key-128*) *aes-test-plaintext*)

(acl2::assert-equal (aes-128-decrypt (aes-128-encrypt *aes-test-plaintext* *aes-test-key-128*) *aes-test-key-128*) *aes-test-plaintext*)

(defconst *aes-test-key-192* '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17))

(defconst *aes-test-ciphertext-192* '(#xdd #xa9 #x7c #xa4 #x86 #x4c #xdf #xe0 #x6e #xaf #x70 #xa0 #xec #x0d #x71 #x91))

(acl2::assert-equal (aes-192-encrypt *aes-test-plaintext* *aes-test-key-192*) *aes-test-ciphertext-192*)

(acl2::assert-equal (aes-192-decrypt *aes-test-ciphertext-192* *aes-test-key-192*) *aes-test-plaintext*)

(acl2::assert-equal (aes-192-decrypt (aes-192-encrypt *aes-test-plaintext* *aes-test-key-192*) *aes-test-key-192*) *aes-test-plaintext*)

(defconst *aes-test-key-256* '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19 #x1a #x1b #x1c #x1d #x1e #x1f))

(defconst *aes-test-ciphertext-256* '(#x8e #xa2 #xb7 #xca #x51 #x67 #x45 #xbf #xea #xfc #x49 #x90 #x4b #x49 #x60 #x89))

(acl2::assert-equal (aes-256-encrypt *aes-test-plaintext* *aes-test-key-256*) *aes-test-ciphertext-256*)

(acl2::assert-equal (aes-256-decrypt *aes-test-ciphertext-256* *aes-test-key-256*) *aes-test-plaintext*)

(acl2::assert-equal (aes-256-decrypt (aes-256-encrypt *aes-test-plaintext* *aes-test-key-256*) *aes-test-key-256*)
                    *aes-test-plaintext*)
