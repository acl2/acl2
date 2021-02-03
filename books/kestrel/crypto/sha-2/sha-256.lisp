; Formal spec of the SHA-256 hash function
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA2")

;; A formal specification for of SHA-256 hash function, which is standardized
;; in FIPS PUB 180-4.  See:
;; http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

;; See tests in sha-256-tests.lisp.

(include-book "../../bv/ops32")
(include-book "../../bv/rightrotate32")
(include-book "../../bv/defs-shifts")
(include-book "../../bv-lists/packbv")
(include-book "../../bv-lists/unpackbv")
(include-book "../../bv-lists/bytes-to-bits")
(include-book "../padding/pad-to-448")
(local (include-book "../../arithmetic-light/times"))
(local (include-book "../../arithmetic-light/floor"))
(local (include-book "../../arithmetic-light/mod"))
(local (include-book "../../lists-light/nthcdr"))
(local (include-book "../../lists-light/take"))
(local (include-book "../../lists-light/append"))
(local (include-book "../../lists-light/len"))
(local (include-book "../../bv/bvplus"))

(local (in-theory (disable mv-nth)))

(local
 (defthm mod-of-floor-32-16
   (implies (rationalp x)
            (equal (mod (floor x 32) 16)
                   (floor (mod x 512) 32)))
   :hints (("Goal" :in-theory (enable mod)))))

(local
 (defthm integerp-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 x)
            (integerp x))))

;; See Figure 1
(defconst *sha-256-max-message-bits*
  (+ -1 (expt 2 64)))

;; 2^61 bytes would be 2^64 bits, which would be too long
(defconst *sha-256-max-message-bytes*
  (+ -1 (expt 2 61)))

;; Right rotate for w = 32.  Section 3.2.  See also sha-256-validation.lisp.
(defun rotr32 (n x)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (natp n)
                              (< n 32))))
  (rightrotate32 n x))

;; Right shift for w = 32.  Section 3.2.
(defun shr32 (n x)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (natp n)
                              (< n 32))))
  ;; Note the order of the arguments here:
  (bvshr 32 x n))

;; Equation (4.2)
(defun ch32 (x y z)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z))))
  (xor32 (and32 x y)
         (and32 (not32 x)
                z)))

;; Equation (4.3)
(defun maj32 (x y z)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z))))
  (xor32 (and32 x y)
         (xor32 (and32 x z)
                (and32 y z))))

;; Equation (4.4)
(defun big-sigma-256-0 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (xor32 (rotr32 2 x)
         (xor32 (rotr32 13 x)
                (rotr32 22 x))))

;; Equation (4.5)
(defun big-sigma-256-1 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (xor32 (rotr32 6 x)
         (xor32 (rotr32 11 x)
                (rotr32 25 x))))

;; Equation (4.6)
(defun little-sigma-256-0 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (xor32 (rotr32 7 x)
         (xor32 (rotr32 18 x)
                (shr32 3 x))))

;; Equation (4.7)
(defun little-sigma-256-1 (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)))
  (xor32 (rotr32 17 x)
         (xor32 (rotr32 19 x)
                (shr32 10 x))))

;; Section 4.2.2
;; Given n, return K^{256}_n.
(defun k-256 (n)
  (declare (xargs :guard (and (natp n)
                              (<= n 63))))
  (nth n
       '(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5 #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
         #xd807aa98 #x12835b01 #x243185be #x550c7dc3 #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
         #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
         #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7 #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
         #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13 #x650a7354 #x766a0abb #x81c2c92e #x92722c85
         #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3 #xd192e819 #xd6990624 #xf40e3585 #x106aa070
         #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5 #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
         #x748f82ee #x78a5636f #x84c87814 #x8cc70208 #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2)))

;; Section 5.1.1
(defund sha-256-pad-message (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (append (padding::pad-to-448 msg)
          (unpackbv 64 1 (len msg))))

(defthm all-unsigned-byte-p-of-sha-256-pad-message
  (implies (all-unsigned-byte-p 1 msg)
           (all-unsigned-byte-p 1 (sha-256-pad-message msg)))
  :hints (("Goal" :in-theory (enable sha-256-pad-message))))

(defthm mod-of-len-of-sha-256-pad-message-and-512
  (equal (mod (len (sha-256-pad-message msg)) 512)
         0)
  :hints (("Goal" :in-theory (enable sha-256-pad-message
                                     acl2::mod-sum-cases))))

(defthm mod-of-len-of-sha-256-pad-message-and-32
  (equal (mod (len (sha-256-pad-message msg)) 32)
         0)
  :hints (("Goal" :in-theory (enable sha-256-pad-message
                                     acl2::mod-sum-cases))))

;; Divide MSG (a sequence of bits) into a sequence of 32-bit words.  See
;; Section 5.2.1.
(defund sha-256-message-words (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg)
                              (= 0 (mod (len msg) 32)))))
  (if (endp msg)
      nil
    (cons (packbv 32 1 (take 32 msg))
          (sha-256-message-words (nthcdr 32 msg)))))

(defthm all-unsigned-byte-p-of-sha-256-message-words
  (all-unsigned-byte-p 32 (sha-256-message-words msg))
  :hints (("Goal" :in-theory (enable sha-256-message-words))))

(defthm len-of-sha-256-message-words
  (implies (force (equal (mod (len msg) 32) 0))
           (equal (len (sha-256-message-words msg))
                  (floor (len msg) 32)))
  :hints (("Goal" :in-theory (enable sha-256-message-words))))

;; Recognize a block (a list of 16 32-bit words)
(defun sha-256-blockp (block)
  (declare (xargs :guard t))
  (and (true-listp block)
       (all-unsigned-byte-p 32 block)
       (= 16 (len block))))

;; Recognize a list of blocks
(defun all-sha-256-blockp (blocks)
  (declare (xargs :guard t))
  (if (not (consp blocks))
      t
    (and (sha-256-blockp (first blocks))
         (all-sha-256-blockp (rest blocks)))))

;; Divide WORDS into a sequence of 512-bit blocks.  See Section 5.2.1.
(defund sha-256-message-blocks (words)
  (declare (xargs :guard (and (all-unsigned-byte-p 32 words)
                              (true-listp words)
                              (= 0 (mod (len words) 16)))))
  (if (endp words)
      nil
    (cons (take 16 words)
          (sha-256-message-blocks (nthcdr 16 words)))))

(defthm all-sha-256-blockp-of-sha-256-message-blocks
  (implies (and (all-unsigned-byte-p 32 words)
                (true-listp words)
                (= 0 (mod (len words) 16)))
           (all-sha-256-blockp (sha-256-message-blocks words)))
  :hints (("Goal" :in-theory (enable sha-256-message-blocks))))

;; Pad and parse the message.  Returns a list of blocks.  See Sections 5.1.1
;; and 5.2.1.
(defund sha-256-pad-and-parse-message (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (sha-256-message-blocks (sha-256-message-words (sha-256-pad-message msg))))

(defthm all-sha-256-blockp-of-sha-256-pad-and-parse-message
  (all-sha-256-blockp (sha-256-pad-and-parse-message msg))
  :hints (("Goal" :in-theory (enable sha-256-pad-and-parse-message))))

;; Prepare words T-VAR (initially 16) through 63 of the message schedule. See
;; Section 6.2.2.
(defun sha-256-prepare-message-schedule-aux (t-var w)
  (declare (xargs :measure (+ 1 (nfix (- 64 t-var)))
                  :guard (and (equal t-var (len w))
                              (<= 16 t-var)
                              (<= t-var 64)
                              (all-unsigned-byte-p 32 w)
                              (true-listp w))))
  (if (or (>= t-var 64)
          (not (mbt (natp t-var))))
      w
    (let ((current-item (plus32 (little-sigma-256-1 (nth (- t-var 2) w))
                                (plus32 (nth (- t-var 7) w)
                                        (plus32 (little-sigma-256-0 (nth (- t-var 15) w))
                                                (nth (- t-var 16) w))))))
      (sha-256-prepare-message-schedule-aux (+ 1 t-var)
                                            ;; inefficient but clear:
                                            (append w (list current-item))))))

(defthm all-unsigned-byte-p-of-sha-256-prepare-message-schedule-aux
  (implies (all-unsigned-byte-p 32 w)
           (all-unsigned-byte-p 32 (sha-256-prepare-message-schedule-aux t-var w)))
  :hints (("Goal" :induct (sha-256-prepare-message-schedule-aux t-var w))))

(defthm len-of-sha-256-prepare-message-schedule-aux
  (implies (and (equal (len w) t-var)
                (<= t-var 64))
           (equal (len (sha-256-prepare-message-schedule-aux t-var w))
                  64))
  :hints (("Goal" :induct (sha-256-prepare-message-schedule-aux t-var w))))

;; Section 6.2.2, Step 1.
(defun sha-256-prepare-message-schedule (m)
  (declare (xargs :guard (sha-256-blockp m)))
  (let ((w m)) ;; the first 16 words of the message schedule are simply the words in the block
    (sha-256-prepare-message-schedule-aux 16 w)))

;; Step 3 in Sec 6.2.2.
(defund sha-256-inner-loop (t-var a b c d e f g h w)
  (declare (xargs :measure (+ 1 (nfix (- 80 t-var)))
                  :guard (and (natp t-var)
                              (<= t-var 64)
                              (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b)
                              (unsigned-byte-p 32 c)
                              (unsigned-byte-p 32 d)
                              (unsigned-byte-p 32 e)
                              (unsigned-byte-p 32 f)
                              (unsigned-byte-p 32 g)
                              (unsigned-byte-p 32 h)
                              (all-unsigned-byte-p 32 w)
                              (true-listp w)
                              (= 64 (len w)))))
  (if (or (>= t-var 64)
          (not (mbt (natp t-var))))
      (mv a b c d e f g h)
    (let* ((t1 (plus32 h
                       (plus32 (big-sigma-256-1 e)
                               (plus32 (ch32 e f g)
                                       (plus32 (k-256 t-var)
                                               (nth t-var w))))))
           (t2 (plus32 (big-sigma-256-0 a)
                       (maj32 a b c)))
           (h g)
           (g f)
           (f e)
           (e (plus32 d t1))
           (d c)
           (c b)
           (b a)
           (a (plus32 t1 t2)))
      (sha-256-inner-loop (+ 1 t-var) a b c d e f g h w))))

;; This is the body of the main loop in Section 6.2.2.
;; Returns H^{i} as (mv hi_0 hi_1 hi_2 hi_3 hi_4 hi_5 hi_6 hi_7).
(defund sha-256-process-block (mi h0 h1 h2 h3 h4 h5 h6 h7)
  (declare (xargs :guard (and (sha-256-blockp mi)
                              (unsigned-byte-p 32 h0)
                              (unsigned-byte-p 32 h1)
                              (unsigned-byte-p 32 h2)
                              (unsigned-byte-p 32 h3)
                              (unsigned-byte-p 32 h4)
                              (unsigned-byte-p 32 h5)
                              (unsigned-byte-p 32 h6)
                              (unsigned-byte-p 32 h7))))
  (let* (;; Step 1:
         (w (sha-256-prepare-message-schedule mi))
         ;; Step 2:
         (a h0)
         (b h1)
         (c h2)
         (d h3)
         (e h4)
         (f h5)
         (g h6)
         (h h7))
    ;; Step 3:
    (mv-let (a b c d e f g h)
      (sha-256-inner-loop 0 a b c d e f g h w)
      ;; Step 4:
      (mv (plus32 a h0)
          (plus32 b h1)
          (plus32 c h2)
          (plus32 d h3)
          (plus32 e h4)
          (plus32 f h5)
          (plus32 g h6)
          (plus32 h h7)))))

(defthm sha-256-process-block-type
  (and (unsigned-byte-p 32 (mv-nth 0 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 1 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 2 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 3 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 4 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 5 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 6 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 32 (mv-nth 7 (sha-256-process-block mi h0 h1 h2 h3 h4 h5 h6 h7))))
  :hints (("Goal" :in-theory (enable sha-256-process-block))))

;; Returns the final hash value, H^{n}, as (mv hn_0 hn_1 hn_2 hn_3 hn_4 hn_5 hn_6 hn_7).
(defund sha-256-process-blocks (blocks h0 h1 h2 h3 h4 h5 h6 h7)
  (declare (xargs :guard (and (all-sha-256-blockp blocks)
                              (true-listp blocks)
                              (unsigned-byte-p 32 h0)
                              (unsigned-byte-p 32 h1)
                              (unsigned-byte-p 32 h2)
                              (unsigned-byte-p 32 h3)
                              (unsigned-byte-p 32 h4)
                              (unsigned-byte-p 32 h5)
                              (unsigned-byte-p 32 h6)
                              (unsigned-byte-p 32 h7))))
  (if (endp blocks)
      (mv h0 h1 h2 h3 h4 h5 h6 h7)
    (mv-let (h0 h1 h2 h3 h4 h5 h6 h7)
      (sha-256-process-block (first blocks) h0 h1 h2 h3 h4 h5 h6 h7)
      (sha-256-process-blocks (rest blocks) h0 h1 h2 h3 h4 h5 h6 h7))))

(defthm sha-256-process-blocks-return-type
  (implies (and (unsigned-byte-p 32 h0)
                (unsigned-byte-p 32 h1)
                (unsigned-byte-p 32 h2)
                (unsigned-byte-p 32 h3)
                (unsigned-byte-p 32 h4)
                (unsigned-byte-p 32 h5)
                (unsigned-byte-p 32 h6)
                (unsigned-byte-p 32 h7))
           (and (unsigned-byte-p 32 (mv-nth 0 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 1 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 2 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 3 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 4 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 5 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 6 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 32 (mv-nth 7 (sha-256-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))))
  :hints (("Goal" :in-theory (enable sha-256-process-blocks))))

;; Takes as input the message (a list of bits) to be hashed (the number of bits
;; need not be a multiple of 8).  Returns the 256-bit hash, as a list of 32
;; bytes. The length of MSG-BITS must be less than 2^64 (a limit that is
;; unlikely to be of practical importance). This formalizes Section 6.2.
(defund sha-256 (msg-bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (<= (len msg-bits) *sha-256-max-message-bits*))))
  (let ( ;; Initial values of H^{0}_0 through H^{0}_7 (Sec 5.3.3):
        (h0_0 #x6a09e667)
        (h0_1 #xbb67ae85)
        (h0_2 #x3c6ef372)
        (h0_3 #xa54ff53a)
        (h0_4 #x510e527f)
        (h0_5 #x9b05688c)
        (h0_6 #x1f83d9ab)
        (h0_7 #x5be0cd19)
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
      ;;final hash value:
      (append (unpackbv 4 8 hn_0)
              (unpackbv 4 8 hn_1)
              (unpackbv 4 8 hn_2)
              (unpackbv 4 8 hn_3)
              (unpackbv 4 8 hn_4)
              (unpackbv 4 8 hn_5)
              (unpackbv 4 8 hn_6)
              (unpackbv 4 8 hn_7)))))

(defthm all-unsigned-byte-p-of-sha-256
  (all-unsigned-byte-p 8 (sha-256 msg-bits))
  :hints (("Goal" :in-theory (enable sha-256))))

(defthm all-integerp-of-sha-256
  (all-integerp (sha-256 msg-bits))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-256)
           :in-theory (disable all-unsigned-byte-p-of-sha-256))))

(defthm len-of-sha-256
  (equal (len (sha-256 msg-bits))
         32)
  :hints (("Goal" :in-theory (enable sha-256))))

;; Apply SHA-256 to a sequence of bytes, where the bytes are converted to a
;; sequence of bits in big-endian fashion.
(defund sha-256-bytes (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (<= (len bytes) *sha-256-max-message-bytes*))))
  (sha-256 (bytes-to-bits bytes)))

(defthm all-unsigned-byte-p-of-sha-256-bytes
  (all-unsigned-byte-p 8 (sha-256-bytes bytes))
  :hints (("Goal" :in-theory (enable sha-256-bytes))))

(defthm all-integerp-of-sha-256-bytes
  (all-integerp (sha-256-bytes bytes))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-256-bytes)
           :in-theory (disable all-unsigned-byte-p-of-sha-256-bytes))))

(defthm len-of-sha-256-bytes
  (equal (len (sha-256-bytes bytes))
         32)
  :hints (("Goal" :in-theory (enable sha-256-bytes))))
