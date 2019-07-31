; Formal spec of the SHA-512 hash function
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA2")

;; A formal specification for of SHA-512 hash function, which is standardized
;; in FIPS PUB 180-4.  See:
;; http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf

;; See tests in sha-512-tests.lisp.

(include-book "../../bv/ops64")
(include-book "../../bv/rightrotate")
(include-book "../../bv/defs-shifts")
(include-book "../../bv-lists/packbv")
(include-book "../../bv-lists/unpackbv")
(include-book "../../bv-lists/bytes-to-bits")
(include-book "../padding/pad-to-896")
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
 (defthm mod-of-floor-64-16
   (implies (rationalp x)
            (equal (mod (floor x 64) 16)
                   (floor (mod x 1024) 64)))
   :hints (("Goal" :in-theory (enable mod)))))

(local
 (defthm integerp-when-unsigned-byte-p-64
   (implies (unsigned-byte-p 64 x)
            (integerp x))))

;; See Figure 1
(defconst *sha-512-max-message-bits*
  (+ -1 (expt 2 128)))

;; 2^125 bytes would be 2^128 bits, which would be too long
(defconst *sha-512-max-message-bytes*
  (+ -1 (expt 2 125)))

;; Right rotate for w = 64.  Section 3.2.  See also sha-512-validation.lisp.
(defun rotr64 (n x)
  (declare (xargs :guard (and (unsigned-byte-p 64 x)
                              (natp n)
                              (< n 64))))
  (rightrotate64 n x))

;; Right shift for w = 64.  Section 3.2.
(defun shr64 (n x)
  (declare (xargs :guard (and (unsigned-byte-p 64 x)
                              (natp n)
                              (< n 64))))
  ;; Note the order of the arguments here:
  (shr 64 x n))

;; Equation (4.8)
(defun ch64 (x y z)
  (declare (xargs :guard (and (unsigned-byte-p 64 x)
                              (unsigned-byte-p 64 y)
                              (unsigned-byte-p 64 z))))
  (xor64 (and64 x y)
         (and64 (not64 x)
                z)))

;; Equation (4.9)
(defun maj64 (x y z)
  (declare (xargs :guard (and (unsigned-byte-p 64 x)
                              (unsigned-byte-p 64 y)
                              (unsigned-byte-p 64 z))))
  (xor64 (and64 x y)
         (xor64 (and64 x z)
                (and64 y z))))

;; Equation (4.10)
(defun big-sigma-512-0 (x)
  (declare (xargs :guard (unsigned-byte-p 64 x)))
  (xor64 (rotr64 28 x)
         (xor64 (rotr64 34 x)
                (rotr64 39 x))))

;; Equation (4.11)
(defun big-sigma-512-1 (x)
  (declare (xargs :guard (unsigned-byte-p 64 x)))
  (xor64 (rotr64 14 x)
         (xor64 (rotr64 18 x)
                (rotr64 41 x))))

;; Equation (4.12)
(defun little-sigma-512-0 (x)
  (declare (xargs :guard (unsigned-byte-p 64 x)))
  (xor64 (rotr64 1 x)
         (xor64 (rotr64 8 x)
                (shr64 7 x))))

;; Equation (4.13)
(defun little-sigma-512-1 (x)
  (declare (xargs :guard (unsigned-byte-p 64 x)))
  (xor64 (rotr64 19 x)
         (xor64 (rotr64 61 x)
                (shr64 6 x))))

;; Section 4.2.3
;; Given n, return K^{512}_n.
(defun k-512 (n)
  (declare (xargs :guard (and (natp n)
                              (<= n 79))))
  (nth n
       '(#x428a2f98d728ae22 #x7137449123ef65cd #xb5c0fbcfec4d3b2f #xe9b5dba58189dbbc
         #x3956c25bf348b538 #x59f111f1b605d019 #x923f82a4af194f9b #xab1c5ed5da6d8118
         #xd807aa98a3030242 #x12835b0145706fbe #x243185be4ee4b28c #x550c7dc3d5ffb4e2
         #x72be5d74f27b896f #x80deb1fe3b1696b1 #x9bdc06a725c71235 #xc19bf174cf692694
         #xe49b69c19ef14ad2 #xefbe4786384f25e3 #x0fc19dc68b8cd5b5 #x240ca1cc77ac9c65
         #x2de92c6f592b0275 #x4a7484aa6ea6e483 #x5cb0a9dcbd41fbd4 #x76f988da831153b5
         #x983e5152ee66dfab #xa831c66d2db43210 #xb00327c898fb213f #xbf597fc7beef0ee4
         #xc6e00bf33da88fc2 #xd5a79147930aa725 #x06ca6351e003826f #x142929670a0e6e70
         #x27b70a8546d22ffc #x2e1b21385c26c926 #x4d2c6dfc5ac42aed #x53380d139d95b3df
         #x650a73548baf63de #x766a0abb3c77b2a8 #x81c2c92e47edaee6 #x92722c851482353b
         #xa2bfe8a14cf10364 #xa81a664bbc423001 #xc24b8b70d0f89791 #xc76c51a30654be30
         #xd192e819d6ef5218 #xd69906245565a910 #xf40e35855771202a #x106aa07032bbd1b8
         #x19a4c116b8d2d0c8 #x1e376c085141ab53 #x2748774cdf8eeb99 #x34b0bcb5e19b48a8
         #x391c0cb3c5c95a63 #x4ed8aa4ae3418acb #x5b9cca4f7763e373 #x682e6ff3d6b2b8a3
         #x748f82ee5defb2fc #x78a5636f43172f60 #x84c87814a1f0ab72 #x8cc702081a6439ec
         #x90befffa23631e28 #xa4506cebde82bde9 #xbef9a3f7b2c67915 #xc67178f2e372532b
         #xca273eceea26619c #xd186b8c721c0c207 #xeada7dd6cde0eb1e #xf57d4f7fee6ed178
         #x06f067aa72176fba #x0a637dc5a2c898a6 #x113f9804bef90dae #x1b710b35131c471b
         #x28db77f523047d84 #x32caab7b40c72493 #x3c9ebe0a15c9bebc #x431d67c49c100d4c
         #x4cc5d4becb3e42b6 #x597f299cfc657e2a #x5fcb6fab3ad6faec #x6c44198c4a475817)))

;; Section 5.1.2
(defund sha-512-pad-message (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (append (padding::pad-to-896 msg)
          (unpackbv 128 1 (len msg))))

(defthm all-unsigned-byte-p-of-sha-512-pad-message
  (implies (all-unsigned-byte-p 1 msg)
           (all-unsigned-byte-p 1 (sha-512-pad-message msg)))
  :hints (("Goal" :in-theory (enable sha-512-pad-message))))

(defthm mod-of-len-of-sha-512-pad-message-and-1024
  (equal (mod (len (sha-512-pad-message msg)) 1024)
         0)
  :hints (("Goal" :in-theory (enable sha-512-pad-message))))

(defthm mod-of-len-of-sha-512-pad-message-and-64
  (equal (mod (len (sha-512-pad-message msg)) 64)
         0)
  :hints (("Goal" :in-theory (enable sha-512-pad-message))))

;; Divide MSG (a sequence of bits) into a sequence of 64-bit words.  See
;; Section 5.2.2.
(defund sha-512-message-words (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg)
                              (= 0 (mod (len msg) 64)))))
  (if (endp msg)
      nil
    (cons (packbv 64 1 (take 64 msg))
          (sha-512-message-words (nthcdr 64 msg)))))

(defthm all-unsigned-byte-p-of-sha-512-message-words
  (all-unsigned-byte-p 64 (sha-512-message-words msg))
  :hints (("Goal" :in-theory (enable sha-512-message-words))))

(defthm len-of-sha-512-message-words
  (implies (force (equal (mod (len msg) 64) 0))
           (equal (len (sha-512-message-words msg))
                  (floor (len msg) 64)))
  :hints (("Goal" :in-theory (enable sha-512-message-words))))

;; Recognize a block (a list of 16 64-bit words)
(defun sha-512-blockp (block)
  (declare (xargs :guard t))
  (and (true-listp block)
       (all-unsigned-byte-p 64 block)
       (= 16 (len block))))

;; Recognize a list of blocks
(defun all-sha-512-blockp (blocks)
  (declare (xargs :guard t))
  (if (not (consp blocks))
      t
    (and (sha-512-blockp (first blocks))
         (all-sha-512-blockp (rest blocks)))))

;; Divide WORDS into a sequence of 1024-bit blocks.  See Section 5.2.2.
(defund sha-512-message-blocks (words)
  (declare (xargs :guard (and (all-unsigned-byte-p 64 words)
                              (true-listp words)
                              (= 0 (mod (len words) 16)))))
  (if (endp words)
      nil
    (cons (take 16 words)
          (sha-512-message-blocks (nthcdr 16 words)))))

(defthm all-sha-512-blockp-of-sha-512-message-blocks
  (implies (and (all-unsigned-byte-p 64 words)
                (true-listp words)
                (= 0 (mod (len words) 16)))
           (all-sha-512-blockp (sha-512-message-blocks words)))
  :hints (("Goal" :in-theory (enable sha-512-message-blocks))))

;; Pad and parse the message.  Returns a list of blocks.  See Sections 5.1.2
;; and 5.2.2.
(defund sha-512-pad-and-parse-message (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (sha-512-message-blocks (sha-512-message-words (sha-512-pad-message msg))))

(defthm all-sha-512-blockp-of-sha-512-pad-and-parse-message
  (all-sha-512-blockp (sha-512-pad-and-parse-message msg))
  :hints (("Goal" :in-theory (enable sha-512-pad-and-parse-message))))

;; Prepare words T-VAR (initially 16) through 79 of the message schedule. See
;; Section 6.4.2.
(defun sha-512-prepare-message-schedule-aux (t-var w)
  (declare (xargs :measure (+ 1 (nfix (- 80 t-var)))
                  :guard (and (equal t-var (len w))
                              (<= 16 t-var)
                              (<= t-var 80)
                              (all-unsigned-byte-p 64 w)
                              (true-listp w))))
  (if (or (>= t-var 80)
          (not (mbt (natp t-var))))
      w
    (let ((current-item (plus64 (little-sigma-512-1 (nth (- t-var 2) w))
                                (plus64 (nth (- t-var 7) w)
                                        (plus64 (little-sigma-512-0 (nth (- t-var 15) w))
                                                (nth (- t-var 16) w))))))
      (sha-512-prepare-message-schedule-aux (+ 1 t-var)
                                            ;; inefficient but clear:
                                            (append w (list current-item))))))

(defthm all-unsigned-byte-p-of-sha-512-prepare-message-schedule-aux
  (implies (all-unsigned-byte-p 64 w)
           (all-unsigned-byte-p 64 (sha-512-prepare-message-schedule-aux t-var w)))
  :hints (("Goal" :induct (sha-512-prepare-message-schedule-aux t-var w))))

(defthm len-of-sha-512-prepare-message-schedule-aux
  (implies (and (equal (len w) t-var)
                (<= t-var 80))
           (equal (len (sha-512-prepare-message-schedule-aux t-var w))
                  80))
  :hints (("Goal" :induct (sha-512-prepare-message-schedule-aux t-var w))))

;; Section 6.4.2, Step 1.
(defun sha-512-prepare-message-schedule (m)
  (declare (xargs :guard (sha-512-blockp m)))
  (let ((w m)) ;; the first 16 words of the message schedule are simply the words in the block
    (sha-512-prepare-message-schedule-aux 16 w)))

;; Step 3 in Sec 6.4.2.
(defund sha-512-inner-loop (t-var a b c d e f g h w)
  (declare (xargs :measure (+ 1 (nfix (- 80 t-var)))
                  :guard (and (natp t-var)
                              (<= t-var 80)
                              (unsigned-byte-p 64 a)
                              (unsigned-byte-p 64 b)
                              (unsigned-byte-p 64 c)
                              (unsigned-byte-p 64 d)
                              (unsigned-byte-p 64 e)
                              (unsigned-byte-p 64 f)
                              (unsigned-byte-p 64 g)
                              (unsigned-byte-p 64 h)
                              (all-unsigned-byte-p 64 w)
                              (true-listp w)
                              (= 80 (len w)))))
  (if (or (>= t-var 80)
          (not (mbt (natp t-var))))
      (mv a b c d e f g h)
    (let* ((t1 (plus64 h
                       (plus64 (big-sigma-512-1 e)
                               (plus64 (ch64 e f g)
                                       (plus64 (k-512 t-var)
                                               (nth t-var w))))))
           (t2 (plus64 (big-sigma-512-0 a)
                       (maj64 a b c)))
           (h g)
           (g f)
           (f e)
           (e (plus64 d t1))
           (d c)
           (c b)
           (b a)
           (a (plus64 t1 t2)))
      (sha-512-inner-loop (+ 1 t-var) a b c d e f g h w))))

;; This is the body of the main loop in Section 6.4.2.
;; Returns H^{i} as (mv hi_0 hi_1 hi_2 hi_3 hi_4 hi_5 hi_6 hi_7).
(defund sha-512-process-block (mi h0 h1 h2 h3 h4 h5 h6 h7)
  (declare (xargs :guard (and (sha-512-blockp mi)
                              (unsigned-byte-p 64 h0)
                              (unsigned-byte-p 64 h1)
                              (unsigned-byte-p 64 h2)
                              (unsigned-byte-p 64 h3)
                              (unsigned-byte-p 64 h4)
                              (unsigned-byte-p 64 h5)
                              (unsigned-byte-p 64 h6)
                              (unsigned-byte-p 64 h7))))
  (let* (;; Step 1:
         (w (sha-512-prepare-message-schedule mi))
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
      (sha-512-inner-loop 0 a b c d e f g h w)
      ;; Step 4:
      (mv (plus64 a h0)
          (plus64 b h1)
          (plus64 c h2)
          (plus64 d h3)
          (plus64 e h4)
          (plus64 f h5)
          (plus64 g h6)
          (plus64 h h7)))))

(defthm sha-512-process-block-type
  (and (unsigned-byte-p 64 (mv-nth 0 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 1 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 2 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 3 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 4 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 5 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 6 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7)))
       (unsigned-byte-p 64 (mv-nth 7 (sha-512-process-block mi h0 h1 h2 h3 h4 h5 h6 h7))))
  :hints (("Goal" :in-theory (enable sha-512-process-block))))

;; Returns the final hash value, H^{n}, as (mv hn_0 hn_1 hn_2 hn_3 hn_4 hn_5 hn_6 hn_7).
(defund sha-512-process-blocks (blocks h0 h1 h2 h3 h4 h5 h6 h7)
  (declare (xargs :guard (and (all-sha-512-blockp blocks)
                              (true-listp blocks)
                              (unsigned-byte-p 64 h0)
                              (unsigned-byte-p 64 h1)
                              (unsigned-byte-p 64 h2)
                              (unsigned-byte-p 64 h3)
                              (unsigned-byte-p 64 h4)
                              (unsigned-byte-p 64 h5)
                              (unsigned-byte-p 64 h6)
                              (unsigned-byte-p 64 h7))))
  (if (endp blocks)
      (mv h0 h1 h2 h3 h4 h5 h6 h7)
  (mv-let (h0 h1 h2 h3 h4 h5 h6 h7)
    (sha-512-process-block (first blocks) h0 h1 h2 h3 h4 h5 h6 h7)
    (sha-512-process-blocks (rest blocks) h0 h1 h2 h3 h4 h5 h6 h7))))

(defthm sha-512-process-blocks-return-type
  (implies (and (unsigned-byte-p 64 h0)
                (unsigned-byte-p 64 h1)
                (unsigned-byte-p 64 h2)
                (unsigned-byte-p 64 h3)
                (unsigned-byte-p 64 h4)
                (unsigned-byte-p 64 h5)
                (unsigned-byte-p 64 h6)
                (unsigned-byte-p 64 h7))
           (and (unsigned-byte-p 64 (mv-nth 0 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 1 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 2 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 3 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 4 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 5 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 6 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))
                (unsigned-byte-p 64 (mv-nth 7 (sha-512-process-blocks blocks h0 h1 h2 h3 h4 h5 h6 h7)))))
  :hints (("Goal" :in-theory (enable sha-512-process-blocks))))

;; Takes as input the message (a list of bits) to be hashed (the number of bits
;; need not be a multiple of 8).  Returns the 512-bit hash, as a list of 64
;; bytes. The length of MSG-BITS must be less than 2^128 (a limit that is
;; unlikely to be of practical importance). This formalizes Section 6.4.
(defund sha-512 (msg-bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (<= (len msg-bits) *sha-512-max-message-bits*))))
  (let ( ;; Initial values of H^{0}_0 through H^{0}_7 (Sec 5.3.5):
        (h0_0 #x6a09e667f3bcc908)
        (h0_1 #xbb67ae8584caa73b)
        (h0_2 #x3c6ef372fe94f82b)
        (h0_3 #xa54ff53a5f1d36f1)
        (h0_4 #x510e527fade682d1)
        (h0_5 #x9b05688c2b3e6c1f)
        (h0_6 #x1f83d9abfb41bd6b)
        (h0_7 #x5be0cd19137e2179)
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
      ;;final hash value:
      (append (unpackbv 8 8 hn_0)
              (unpackbv 8 8 hn_1)
              (unpackbv 8 8 hn_2)
              (unpackbv 8 8 hn_3)
              (unpackbv 8 8 hn_4)
              (unpackbv 8 8 hn_5)
              (unpackbv 8 8 hn_6)
              (unpackbv 8 8 hn_7)))))

(defthm all-unsigned-byte-p-of-sha-512
  (all-unsigned-byte-p 8 (sha-512 msg-bits))
  :hints (("Goal" :in-theory (enable sha-512))))

(defthm all-integerp-of-sha-512
  (all-integerp (sha-512 msg-bits))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-512)
           :in-theory (disable all-unsigned-byte-p-of-sha-512))))

(defthm len-of-sha-512
  (equal (len (sha-512 msg-bits))
         64)
  :hints (("Goal" :in-theory (enable sha-512))))

;; Apply SHA-512 to a sequence of bytes, where the bytes are converted to a
;; sequence of bits in big-endian fashion.
(defund sha-512-bytes (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (<= (len bytes) *sha-512-max-message-bytes*))))
  (sha-512 (bytes-to-bits bytes)))

(defthm all-unsigned-byte-p-of-sha-512-bytes
  (all-unsigned-byte-p 8 (sha-512-bytes bytes))
  :hints (("Goal" :in-theory (enable sha-512-bytes))))

(defthm all-integerp-of-sha-512-bytes
  (all-integerp (sha-512-bytes bytes))
  :hints (("Goal" :use (:instance all-unsigned-byte-p-of-sha-512-bytes)
           :in-theory (disable all-unsigned-byte-p-of-sha-512-bytes))))

(defthm len-of-sha-512-bytes
  (equal (len (sha-512-bytes bytes))
         64)
  :hints (("Goal" :in-theory (enable sha-512-bytes))))
