; Formal spec of the SHA-384 hash function
;
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA2")

;A formal spec for the SHA-384 hash function, which is standardized
;; in FIPS PUB 180-4.  See:
;; http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

;; See tests in sha-384-tests.lisp.

(include-book "sha-512")
(local (include-book "../../lists-light/append"))

(local (in-theory (disable mv-nth)))

(local
 (defthm integerp-when-unsigned-byte-p-64
   (implies (unsigned-byte-p 64 x)
            (integerp x))))

;; See Figure 1
(defconst *sha-384-max-message-bits*
  (+ -1 (expt 2 128)))

;; 2^125 bytes would be 2^128 bits, which would be too long
(defconst *sha-384-max-message-bytes*
  (+ -1 (expt 2 125)))

;; Takes as input the message (a list of bits) to be hashed (the number of bits
;; need not be a multiple of 8).  Returns the 384-bit hash, as a list of 48
;; bytes. The length of MSG-BITS must be less than 2^128 (a limit that is
;; unlikely to be of practical importance). This formalizes Section 6.5.
(defun sha-384 (msg-bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (<= (len msg-bits) *sha-384-max-message-bits*) ; from Figure 1
                              )))
  (let ( ;; Initial values of H^{0}_0 through H^{0}_7 (Sec 5.3.4):
        (h0_0 #xcbbb9d5dc1059ed8)
        (h0_1 #x629a292a367cd507)
        (h0_2 #x9159015a3070dd17)
        (h0_3 #x152fecd8f70e5939)
        (h0_4 #x67332667ffc00b31)
        (h0_5 #x8eb44a8768581511)
        (h0_6 #xdb0c2e0d64f98fa7)
        (h0_7 #x47b5481dbefa4fa4)
        (blocks (sha-512-pad-and-parse-message msg-bits)))
    (mv-let (hn_0 hn_1 hn_2 hn_3 hn_4 hn_5 hn_6 hn_7)
      (sha-512-process-blocks blocks
                              h0_0
                              h0_1
                              h0_2
                              h0_3
                              h0_4
                              h0_5
                              h0_6
                              h0_7)
      (declare (ignore hn_6 hn_7))
      ;;final hash value:
      (append (unpackbv 8 8 hn_0)
              (unpackbv 8 8 hn_1)
              (unpackbv 8 8 hn_2)
              (unpackbv 8 8 hn_3)
              (unpackbv 8 8 hn_4)
              (unpackbv 8 8 hn_5)))))

;; Apply SHA-384 to a sequence of bytes, where the bytes are converted to a
;; sequence of bits in big-endian fashion.
(defund sha-384-bytes (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (<= (len bytes) *sha-384-max-message-bytes*))))
  (sha-384 (bytes-to-bits bytes)))

(defthm all-unsigned-byte-p-of-sha-384-bytes
  (all-unsigned-byte-p 8 (sha-384-bytes bytes))
  :hints (("Goal" :in-theory (enable sha-384-bytes))))

(defthm all-integerp-of-sha-384-bytes
  (all-integerp (sha-384-bytes bytes))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-384-bytes)
           :in-theory (disable all-unsigned-byte-p-of-sha-384-bytes))))

(defthm len-of-sha-384-bytes
  (equal (len (sha-384-bytes bytes))
         48)
  :hints (("Goal" :in-theory (enable sha-384-bytes))))
