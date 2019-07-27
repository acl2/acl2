; Formal spec of the SHA-224 hash function
;
; Copyright (C) 2018-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA2")

;A formal spec for the SHA-224 hash function, which is standardized
;; in FIPS PUB 180-4.  See:
;; http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

;; See tests in sha-224-tests.lisp.

(include-book "sha-256")
(local (include-book "../../lists-light/append"))

(local (in-theory (disable mv-nth)))

(local
 (defthm integerp-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 x)
            (integerp x))))

;; See Figure 1
(defconst *sha-224-max-message-bits*
  (+ -1 (expt 2 64)))

;; 2^61 bytes would be 2^64 bits, which would be too long
(defconst *sha-224-max-message-bytes*
  (+ -1 (expt 2 61)))

;; Takes as input the message (a list of bits) to be hashed (the number of bits
;; need not be a multiple of 8).  Returns the 224-bit hash, as a list of 28
;; bytes. The length of MSG-BITS must be less than 2^64 (a limit that is
;; unlikely to be of practical importance). This formalizes Section 6.3.
(defun sha-224 (msg-bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (<= (len msg-bits) *sha-224-max-message-bits*) ; from Figure 1
                              )))
  (let ( ;; Initial values of H^{0}_0 through H^{0}_7 (Sec 5.3.2):
        (h0_0 #xc1059ed8)
        (h0_1 #x367cd507)
        (h0_2 #x3070dd17)
        (h0_3 #xf70e5939)
        (h0_4 #xffc00b31)
        (h0_5 #x68581511)
        (h0_6 #x64f98fa7)
        (h0_7 #xbefa4fa4)
        (blocks (sha-256-pad-and-parse-message msg-bits)))
    (mv-let (hn_0 hn_1 hn_2 hn_3 hn_4 hn_5 hn_6 hn_7)
      (sha-256-process-blocks blocks
                              h0_0
                              h0_1
                              h0_2
                              h0_3
                              h0_4
                              h0_5
                              h0_6
                              h0_7)
      (declare (ignore hn_7))
      ;;final hash value:
      (append (unpackbv 4 8 hn_0)
              (unpackbv 4 8 hn_1)
              (unpackbv 4 8 hn_2)
              (unpackbv 4 8 hn_3)
              (unpackbv 4 8 hn_4)
              (unpackbv 4 8 hn_5)
              (unpackbv 4 8 hn_6)))))

;; Apply SHA-224 to a sequence of bytes, where the bytes are converted to a
;; sequence of bits in big-endian fashion.
(defund sha-224-bytes (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (<= (len bytes) *sha-224-max-message-bytes*))))
  (sha-224 (bytes-to-bits bytes)))

(defthm all-unsigned-byte-p-of-sha-224-bytes
  (all-unsigned-byte-p 8 (sha-224-bytes bytes))
  :hints (("Goal" :in-theory (enable sha-224-bytes))))

(defthm all-integerp-of-sha-224-bytes
  (all-integerp (sha-224-bytes bytes))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-224-bytes)
           :in-theory (disable all-unsigned-byte-p-of-sha-224-bytes))))

(defthm len-of-sha-224-bytes
  (equal (len (sha-224-bytes bytes))
         28)
  :hints (("Goal" :in-theory (enable sha-224-bytes))))
