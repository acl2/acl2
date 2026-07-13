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

;; Absorb the bytes in a list into a CRC, first byte first,
;; via repeated application of CRC32:
(define crc32-of-bytes ((crc (unsigned-byte-p 32 crc)) (bytes nat-listp))
  (if (endp bytes)
      crc
    (crc32-of-bytes (crc32 crc (car bytes) 8) (cdr bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Standard CRC-32C check value:
;; the CRC of the ASCII string "123456789",
;; with initial CRC FFFFFFFFh and final XOR with FFFFFFFFh,
;; is E3069283h.
;; This validates the polynomial,
;; the bit reflections,
;; and the composition of updates,
;; against the published CRC-32C test vector
;; (the `check' value of the CRC-32/ISCSI entry of
;; the RevEng Catalogue of Parametrised CRC Algorithms,
;; https://reveng.sourceforge.io/crc-catalogue/17plus.htm;
;; the `check' parameter is defined in
;; https://reveng.sourceforge.io/crc-catalogue/legend.htm).
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following test patterns and CRC values are
;; the CRC examples in the iSCSI specification,
;; RFC 7143, Appendix A.4 (formerly RFC 3720, Appendix B.4).
;; The RFC lists each CRC as the bytes transmitted on the wire,
;; i.e. the bytes of the 32-bit CRC value in little-endian order;
;; the values below are the corresponding 32-bit CRC values.
;; The initial CRC FFFFFFFFh and the final XOR with FFFFFFFFh
;; are as prescribed for iSCSI.

;; 32 bytes of zeroes; CRC bytes aa 36 91 8a:
(assert-event
 (let* ((crc #xFFFFFFFF)
        (crc (crc32-of-bytes crc (make-list 32 :initial-element #x00))))
   (equal (logxor crc #xFFFFFFFF) #x8A9136AA)))

;; 32 bytes of ones (FFh); CRC bytes 43 ab a8 62:
(assert-event
 (let* ((crc #xFFFFFFFF)
        (crc (crc32-of-bytes crc (make-list 32 :initial-element #xFF))))
   (equal (logxor crc #xFFFFFFFF) #x62A8AB43)))

;; 32 bytes of incrementing 00h to 1Fh; CRC bytes 4e 79 dd 46:
(assert-event
 (let* ((bytes '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07
                 #x08 #x09 #x0A #x0B #x0C #x0D #x0E #x0F
                 #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17
                 #x18 #x19 #x1A #x1B #x1C #x1D #x1E #x1F))
        (crc #xFFFFFFFF)
        (crc (crc32-of-bytes crc bytes)))
   (equal (logxor crc #xFFFFFFFF) #x46DD794E)))

;; 32 bytes of decrementing 1Fh to 00h; CRC bytes 5c db 3f 11:
(assert-event
 (let* ((bytes '(#x1F #x1E #x1D #x1C #x1B #x1A #x19 #x18
                 #x17 #x16 #x15 #x14 #x13 #x12 #x11 #x10
                 #x0F #x0E #x0D #x0C #x0B #x0A #x09 #x08
                 #x07 #x06 #x05 #x04 #x03 #x02 #x01 #x00))
        (crc #xFFFFFFFF)
        (crc (crc32-of-bytes crc bytes)))
   (equal (logxor crc #xFFFFFFFF) #x113FDB5C)))
