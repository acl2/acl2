; X86ISA Library
;
; Copyright (C) 2026 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "crc32-spec")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Standard CRC-32C check value:
;; the CRC of the ASCII string "123456789",
;; with initial CRC FFFFFFFFh and final XOR with FFFFFFFFh,
;; is E3069283h.
;; This validates the polynomial,
;; the bit reflections,
;; and the composition of updates,
;; against the published CRC-32C test vector.
(assert-event
 (let* ((crc #xFFFFFFFF)
        (crc (crc32 crc #x31 8))
        (crc (crc32 crc #x32 8))
        (crc (crc32 crc #x33 8))
        (crc (crc32 crc #x34 8))
        (crc (crc32 crc #x35 8))
        (crc (crc32 crc #x36 8))
        (crc (crc32 crc #x37 8))
        (crc (crc32 crc #x38 8))
        (crc (crc32 crc #x39 8)))
   (equal (logxor crc #xFFFFFFFF) #xE3069283)))

;; Absorbing a 32-bit value agrees with
;; absorbing its four bytes least significant first,
;; consistently with the fact that
;; CRC32 r32, r/m32 on a little-endian dword in memory
;; agrees with four CRC32 r32, r/m8 on the successive bytes.
(assert-event
 (let* ((crc0 #x12345678)
        (crc-bytes (crc32 (crc32 (crc32 (crc32 crc0 #xDE 8)
                                        #xAD 8)
                                 #xBE 8)
                          #xEF 8))
        (crc-dword (crc32 crc0 #xEFBEADDE 32)))
   (equal crc-bytes crc-dword)))
