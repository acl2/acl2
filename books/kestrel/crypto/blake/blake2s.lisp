; Formal specification of BLAKE2s
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; Written from https://tools.ietf.org/rfc/rfc7693.txt.

;; TODO: Add more tests

(include-book "blake-common-32")
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/bv/bvshl-def" :dir :system)
(include-book "kestrel/bv/bvshr-def" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
;(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

(local (in-theory (disable len true-listp nth update-nth expt))) ;; prevent inductions

(local (in-theory (disable acl2::mod-sum-cases nth-update-nth))) ;; prevent case splits

;move
(local
 (DEFTHM
   INTEGERP-OF-SMALL-HELPER-2
   (IMPLIES (AND (< X N) (NATP X) (POSP N))
            (EQUAL (INTEGERP (* (/ N) X))
                   (EQUAL 0 (* (/ N) X))))
   :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST (0 NIL NIL)))
   :HINTS (("Goal" :IN-THEORY (ENABLE acl2::INTEGERP-SQUEEZE)
            :CASES ((< (* (/ N) X) 0)
                    (<= 1 (* (/ N) X)))))))

;move
(defthm all-unsigned-byte-p-of-repeat
  (implies (unsigned-byte-p size x)
           (all-unsigned-byte-p size (repeat n x)))
  :hints (("Goal" :in-theory (enable repeat))))

(defconst *blake2s-max-data-byte-length* (expt 2 64))

(defconst *bb* ;; number of bytes in a block
  64)

(defconst *r* 10) ;; number of rounds

;; G rotation constants:
(defconst *r1* 16)
(defconst *r2* 12)
(defconst *r3* 8)
(defconst *r4* 7)

;; Needed since the mod of + in the spec gets turned into bvplus
(defthm wordp-of-bvplus
  (wordp (bvplus *w* x y))
  :hints (("Goal" :in-theory (enable wordp))))

(defthm wordp-of-mod
  (implies (integerp x)
           (wordp (mod x 4294967296)))
  :hints (("Goal" :in-theory (enable wordp unsigned-byte-p))))

(defthm wordp-of-bvshl
  (implies (and (integerp x)
                (natp amt)
                (<= amt 32))
           (wordp (acl2::bvshl 32 x amt)))
  :hints (("Goal" :in-theory (enable wordp acl2::bvshl natp))))

(defthm wordp-of-bvshr-special
  (implies (unsigned-byte-p (* 2 *w*) x)
           (wordp (bvshr 64 x 32)))
  :hints (("Goal" :in-theory (enable wordp bvshr))))

;; Convert a list of 4 bytes into a word, in little endian fashion.
(defund bytes-to-word (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (= 4 (len bytes))
                              (all-unsigned-byte-p 8 bytes))))
  (acl2::bvcat2 8 (nth 3 bytes) ;most significant byte
                8 (nth 2 bytes)
                8 (nth 1 bytes)
                8 (nth 0 bytes)))

(defthm wordp-of-bytes-to-word
  (wordp (bytes-to-word bytes))
  :hints (("Goal" :in-theory (enable bytes-to-word wordp))))

(local (in-theory (disable acl2::mod-by-4-becomes-bvchop)))

;; Convert a list of bytes into a list of words, in little endian fashion.
(defund bytes-to-words (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (acl2::all-unsigned-byte-p 8 bytes)
                              (equal 0 (mod (len bytes) 4)) ;; we have an integral number of words
                              )))
  (if (endp bytes)
      nil
    (cons (bytes-to-word (take 4 bytes))
          (bytes-to-words (nthcdr 4 bytes)))))

(defthm len-of-bytes-to-words
  (implies (equal 0 (mod (len bytes) 4))
           (equal (len (bytes-to-words bytes))
                  (/ (len bytes) 4)))
  :hints (("Goal" :in-theory (enable bytes-to-words))))

(defthm all-wordp-of-bytes-to-words
  (all-wordp (bytes-to-words bytes))
  :hints (("Goal" :in-theory (enable bytes-to-words))))

;; Convert a list of 64 bytes into a block
(defund bytes-to-block (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (= *bb* (len bytes))
                              (all-unsigned-byte-p 8 bytes))))
  (bytes-to-words bytes))

(defthm blockp-of-bytes-to-block
  (implies (= 64 (len bytes))
           (blockp (bytes-to-block bytes)))
  :hints (("Goal" :in-theory (enable blockp bytes-to-block))))

;; Convert a list of bytes into a list of blocks
(defund bytes-to-blocks (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (equal 0 (mod (len bytes) *bb*)) ;; we have an integral number of blocks
                              (all-unsigned-byte-p 8 bytes))))
  (if (endp bytes)
      nil
    (cons (bytes-to-block (take *bb* bytes))
          (bytes-to-blocks (nthcdr *bb* bytes)))))

(defthm all-blockp-of-bytes-to-blocks
  (all-blockp (bytes-to-blocks data-bytes))
  :hints (("Goal" :in-theory (enable blockp bytes-to-blocks all-blockp))))

(defthm len-of-bytes-to-blocks
  (implies (equal 0 (mod (len bytes) *bb*))
           (equal (len (bytes-to-blocks bytes))
                  (/ (len bytes) *bb*)))
  :hints (("Goal" :in-theory (enable bytes-to-blocks))))

;; Returns a list of bytes
(defund pad-data-bytes (data-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 data-bytes)
                              (true-listp data-bytes))))
  (let* ((ll (len data-bytes))
         (bytes-in-last-block (mod ll *bb*))
         (num-padding-bytes (if (= 0 bytes-in-last-block)
                                0 ;; ll is an exact multiple of the block size
                              (- *bb* bytes-in-last-block))))
    (append data-bytes (acl2::repeat num-padding-bytes 0))))

(defthm all-unsigned-byte-p-of-pad-data-bytes
  (implies (all-unsigned-byte-p 8 data-bytes)
           (all-unsigned-byte-p 8 (pad-data-bytes data-bytes)))
  :hints (("Goal" :in-theory (enable pad-data-bytes))))

(defthm len-of-data-bytes
  (equal (len (pad-data-bytes data-bytes))
         (let ((ll (len data-bytes)))
           (* *bb* (ceiling ll *bb*))))
  :hints (("Goal" :use (:instance mod
                                  (x (len data-bytes))
                                  (y *bb*))
           :in-theory (enable acl2::ceiling-in-terms-of-floor
                              acl2::floor-of---arg1
                              pad-data-bytes))))

;; Pad a non-empty key up to 64 bytes and convert into a block
(defund padded-key-block (key-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (consp key-bytes)
                              (<= (len key-bytes) 32))))
  (let* ((kk (len key-bytes))
         (num-padding-bytes (- *bb* kk))
         (padded-key-bytes (append key-bytes (acl2::repeat num-padding-bytes 0))))
    (bytes-to-block padded-key-bytes)))

(defthm blockp-of-padded-key-block
  (implies (<= (len key-bytes) 32)
           (blockp (padded-key-block key-bytes)))
  :hints (("Goal" :in-theory (enable padded-key-block blockp))))

;; See RFC 7693 Sec 3.3 (Padding Data ...)
(defund d-blocks (data-bytes key-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 data-bytes)
                              (true-listp data-bytes)
                              (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (<= (len key-bytes) 32))))
  (if (and (not (consp data-bytes))
           (not (consp key-bytes)))
      ;; special case for unkeyed empty message: d contains a single block of
      ;; all 0s:
      (list (repeat (/ *bb* 4) 0))
    (let* ((padded-data-bytes (pad-data-bytes data-bytes)))
      (if (consp key-bytes)
          (cons (padded-key-block key-bytes)
                (bytes-to-blocks padded-data-bytes))
        (bytes-to-blocks padded-data-bytes)))))

(defthm consp-of-d-blocks
  (consp (d-blocks data-bytes key-bytes))
  :hints (("Goal" :in-theory (e/d (d-blocks) (len-of-bytes-to-blocks))
           :use (:instance len-of-bytes-to-blocks (bytes (PAD-DATA-BYTES DATA-BYTES)))
           )))

;; dd = ceil(kk / bb) + ceil(ll / bb)
(defthm len-of-d-blocks
  (implies (<= (len key-bytes) 32)
           (equal (len (d-blocks data-bytes key-bytes))
                  (if (consp data-bytes) ;;exclude special case
                      (let ((ll (len data-bytes))
                            (kk (len key-bytes)))
                        (+ (ceiling kk *bb*)
                           (ceiling ll *bb*)))
                    1)))
  :hints (("Goal" :in-theory (enable d-blocks
                                     acl2::ceiling-in-terms-of-floor
                                     acl2::floor-of---arg1))))

(defthm all-blockp-of-d-blocks
  (implies (<= (len key-bytes) 32)
           (all-blockp (d-blocks data-bytes key-bytes)))
  :hints (("Goal" :in-theory (enable d-blocks))))

(local
 (defthm bvplus-intro
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (+ x y) 4294967296)
                  (bvplus *w* x y)))
  :hints (("Goal" :in-theory (enable bvplus bvchop)))))

;; See RFC 7693 Sec 3.1 (Mixing Function G)
(defund g (v a b c d x y)
  (declare (xargs :guard (and (blockp v)
                              (natp a)
                              (< a 16)
                              (natp b)
                              (< b 16)
                              (natp c)
                              (< c 16)
                              (natp d)
                              (< d 16)
                              (wordp x)
                              (wordp y))))
  (let* ((v (update-nth a (mod (+ (nth a v) (nth b v) x) (expt 2 *w*)) v))
         (v (update-nth d (rot-word *r1* (wordxor (nth d v) (nth a v))) v))
         (v (update-nth c (mod (+ (nth c v) (nth d v)) (expt 2 *w*)) v))
         (v (update-nth b (rot-word *r2* (wordxor (nth b v) (nth c v))) v))
         (v (update-nth a (mod (+ (nth a v) (nth b v) y) (expt 2 *w*)) v))
         (v (update-nth d (rot-word *r3* (wordxor (nth d v) (nth a v))) v))
         (v (update-nth c (mod (+ (nth c v) (nth d v)) (expt 2 *w*)) v))
         (v (update-nth b (rot-word *r4* (wordxor (nth b v) (nth c v))) v)))
    v))

(defthm blockp-of-g
  (implies (and (blockp v)
                (natp a)
                (< a 16)
                (natp b)
                (< b 16)
                (natp c)
                (< c 16)
                (natp d)
                (< d 16)
                (wordp x)
                (wordp y))
           (blockp (g v a b c d x y)))
  :hints (("Goal" :in-theory (enable g
                                     ACL2::INTEGERP-OF-+))))

(local (in-theory (disable natp)))

;; Formalization of the first FOR loop in the compression function F (RFC 7693
;; Sec 3.2).
(defund f-loop-1 (i v m)
  (declare (xargs :guard (and (natp i)
                              (<= i *r*)
                              (blockp v)
                              (blockp m))
                  :measure (nfix (- *r* i))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (> i (- *r* 1))
          (not (mbt (natp i))))
      v
    (let* ((s (nth (mod i 10) (sigma)))
           (v (g v 0 4  8 12 (nth (nth 0 s) m) (nth (nth 1 s) m)))
           (v (g v 1 5  9 13 (nth (nth 2 s) m) (nth (nth 3 s) m)))
           (v (g v 2 6 10 14 (nth (nth 4 s) m) (nth (nth 5 s) m)))
           (v (g v 3 7 11 15 (nth (nth 6 s) m) (nth (nth 7 s) m)))

           (v (g v 0 5 10 15 (nth (nth  8 s) m) (nth (nth  9 s) m)))
           (v (g v 1 6 11 12 (nth (nth 10 s) m) (nth (nth 11 s) m)))
           (v (g v 2 7  8 13 (nth (nth 12 s) m) (nth (nth 13 s) m)))
           (v (g v 3 4  9 14 (nth (nth 14 s) m) (nth (nth 15 s) m))))
      (f-loop-1 (+ 1 i) v m))))

(defthm blockp-of-f-loop-1
  (implies (and (blockp v)
                (blockp m))
           (blockp (f-loop-1 i v m)))
  :hints (("Goal" :in-theory (enable f-loop-1))))

;; Formalization of the second FOR loop in the compression function F (RFC 7693
;; Sec 3.2).
(defund f-loop-2 (i h v)
  (declare (xargs :guard (and (natp i)
                              (<= i 8)
                              (true-listp h)
                              (all-wordp h)
                              (= 8 (len h))
                              (blockp v))
                  :measure (nfix (- 8 i))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (> i 7)
          (not (mbt (natp i))))
      h
    (let ((h (update-nth i (wordxor (nth i h) (wordxor (nth i v) (nth (+ i 8) v))) h)))
      (f-loop-2 (+ i 1) h v))))

(defthm len-of-f-loop-2
  (implies (equal 8 (len h))
           (equal (len (f-loop-2 i h v))
                  8))
  :hints (("Goal" :in-theory (enable f-loop-2))))

(defthm all-wordp-of-f-loop-2
  (implies (and (equal 8 (len h))
                (all-wordp h))
           (all-wordp (f-loop-2 i h v)))
  :hints (("Goal" :in-theory (enable f-loop-2))))

(defthm true-listp-of-f-loop-2
  (implies (true-listp h)
           (true-listp (f-loop-2 i h v)))
  :hints (("Goal" :in-theory (enable f-loop-2))))

;; See RFC 7693 Sec 3.2 (Compression Function F)
(defund f (h m tvar f)
  (declare (xargs :guard (and (true-listp h)
                              (all-wordp h)
                              (= 8 (len h))
                              (blockp m)
                              (unsigned-byte-p (* 2 *w*) tvar)
                              (booleanp f))))
  (let* ((v (append h (iv)))
         (v (update-nth 12 (wordxor (nth 12 v) (mod tvar (expt 2 *w*))) v))
         (v (update-nth 13 (wordxor (nth 13 v) (bvshr (* 2 *w*) tvar *w*)) v))
         (v (if f
                (update-nth 14
                            (wordxor (nth 14 v) #xFFFFFFFF) ;todo: use bvnot, or update for blake2b
                            v)
              v))
         (v (f-loop-1 0 v m))
         (h (f-loop-2 0 h v)))
    h))

(defthm len-of-f
  (implies (equal 8 (len h))
           (equal (len (f h m tvar f))
                  8))
  :hints (("Goal" :in-theory (enable f))))

(defthm true-listp-of-f
  (implies (true-listp h)
           (true-listp (f h m tvar f)))
  :hints (("Goal" :in-theory (enable f))))

(defthm all-wordp-of-f
  (implies (and (all-wordp h)
                (equal 8 (len h)))
           (all-wordp (f h m tvar f)))
  :hints (("Goal" :in-theory (enable f))))

;; Formalization of the FOR loop in function BLAKE2 (RFC 7693 Sec 3.3).
(defund loop1 (i bound h d)
  (declare (xargs :guard (and (natp i)
                              (natp bound)
                              (<= i (+ 1 bound))
                              (equal bound (- (len d) 2))
                              (true-listp h)
                              (all-wordp h)
                              (= 8 (len h))
                              (true-listp d)
                              (all-blockp d)
                              (<= (len d) (/ *blake2s-max-data-byte-length* 64)) ;todo: think about this
                              )
                  :measure (nfix (+ 1 (- bound i)))
                  :hints (("Goal" :in-theory (enable natp)))
                  :guard-hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P)))
                  ))
  (if (or (> i bound)
          (not (mbt (natp i)))
          (not (mbt (natp bound))))
      h
    (let ((h (f h (nth i d) (* (+ i 1) *bb*) nil)))
      (loop1 (+ 1 i) bound h d))))

(defthm len-of-loop1
  (implies (= 8 (len h))
           (equal (len (loop1 i bound h d))
                  8))
  :hints (("Goal" :in-theory (enable loop1))))

(defthm all-wordp-of-loop1
  (implies (and (all-wordp h)
                (equal 8 (len h)))
           (all-wordp (loop1 i bound h d)))
  :hints (("Goal" :in-theory (enable loop1))))

(defthm true-listp-of-loop1
  (implies (true-listp h)
           (true-listp (loop1 i bound h d)))
  :hints (("Goal" :in-theory (enable loop1))))

;; Convert a 32-bit word into a list of 4 bytes, in little endian fashion.
;; todo: prove inversion
(defund word-to-bytes (word)
  (declare (xargs :guard (wordp word)))
  (list (slice 7 0 word)
        (slice 15 8 word)
        (slice 23 16 word)
        (slice 31 24 word) ;; most significant byte
        ))

(defthm len-of-word-to-bytes
  (equal (len (word-to-bytes word))
         4)
  :hints (("Goal" :in-theory (enable word-to-bytes))))

(defthm all-unsigned-byte-p-of-word-to-bytes
  (all-unsigned-byte-p 8 (word-to-bytes word))
  :hints (("Goal" :in-theory (enable word-to-bytes))))

;; Convert a list of 32-bit words into a list of bytes, in little endian fashion.
(defund words-to-bytes (words)
  (declare (xargs :guard (and (true-listp words)
                              (all-wordp words))))
  (if (endp words)
      nil
    (append (word-to-bytes (first words))
            (words-to-bytes (rest words)))))

(defthm len-of-words-to-bytes
  (equal (len (words-to-bytes words))
         (* 4 (len words)))
  :hints (("Goal" :in-theory (enable words-to-bytes))))

(defthm all-unsigned-byte-p-of-words-to-bytes
  (all-unsigned-byte-p 8 (words-to-bytes words))
  :hints (("Goal" :in-theory (enable words-to-bytes))))

;; See the function BLAKE2 in RFC 7693 Sec 3.3.
;;TODO: Consider the case when ll is the max.  Then (+ ll *bb*) is > 2^64, contrary to the documentation of f.
(defund blake2s-main (d ll kk nn)
  (declare (xargs :guard (and (true-listp d)
                              (all-blockp d)
                              (< 0 (len d))
                              (<= (len d) (/ *blake2s-max-data-byte-length* 64)) ;think about this
                              (natp ll)
                              ;; (< ll (- *blake2s-max-data-byte-length* 64))
                              (< ll *blake2s-max-data-byte-length*)
                              (natp kk)
                              (posp nn)
                              (<= nn 32))
                  :guard-hints (("Goal" :expand ((wordp nn)
                                                 (unsigned-byte-p 64 (+ 64 ll)))
                                 :in-theory (e/d (natp) ((:e expt)))))))
  (let* ((h (iv))
         (h (update-nth 0
                        (wordxor (nth 0 h)
                                 (wordxor #x01010000
                                          (wordxor (acl2::bvshl 32 kk 8)
                                                   nn)))
                        h))
         (dd (len d))
         (h (if (> dd 1)
                (loop1 0 (- dd 2) h d)
              h))
         (h (if (= kk 0)
                (f h (nth (- dd 1) d) ll t)
              (f h
                 (nth (- dd 1) d)
                 (mod (+ ll *bb*) (expt 2 (* 2 *w*)))
                 t))))
    (take nn (words-to-bytes h))))

(defthm len-of-blake2s-main
  (implies (and (posp nn)
                (<= nn 32))
           (equal (len (blake2s-main d ll kk nn))
                  nn))
  :hints (("Goal" :in-theory (enable blake2s-main))))

(defthm all-unsigned-byte-p-of-blake2s-main
  (implies (<= nn 32)
           (all-unsigned-byte-p 8 (blake2s-main d ll kk nn)))
  :hints (("Goal" :in-theory (enable blake2s-main))))

;; TODO: Think about the case where we have a max length message and a key

;; Returns the hash, as list of bytes of length NN.
(defund blake2s (data-bytes
                 key-bytes
                 nn ;; number of hash bytes to produce
                 )
  (declare (xargs :guard (and (all-unsigned-byte-p 8 data-bytes)
                              (true-listp data-bytes)
                              ;; TODO I want to say this:
                              ;; (< (len data-bytes) *blake2s-max-data-byte-length*)
                              ;; But there are two potential issues related to
                              ;; very long messages: Adding the key block can
                              ;; make the length of d greater than expected,
                              ;; and the expression (+ ll *bb*) in blake2s-main
                              ;; can overflow.
                              (< (len data-bytes) (- *blake2s-max-data-byte-length* 64))
                              (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (<= (len key-bytes) 32)
                              (posp nn)
                              (<= nn 32))))
  (let* ((d (d-blocks data-bytes key-bytes))
         (ll (len data-bytes))
         (kk (len key-bytes)))
    (blake2s-main d ll kk nn)))

(defthm len-of-blake2s
  (implies (and (posp nn)
                (<= nn 32))
           (equal (len (blake2s data-bytes key-bytes nn))
                  nn))
  :hints (("Goal" :in-theory (enable blake2s))))

(defthm all-unsigned-byte-p-of-blake2s
  (implies (<= nn 32)
           (all-unsigned-byte-p 8 (blake2s data-bytes key-bytes nn)))
  :hints (("Goal" :in-theory (enable blake2s))))

;; (assert-equal (blake2s (list (char-code #\a) (char-code #\b) (char-code #\c)) 32) '(#x50 #x8C #x5E #x8C #x32 #x7C #x14 #xE2 #xE1 #xA7 #x2B #xA3 #x4E #xEB #x45 #x2F #x37 #x45 #x8B #x20 #x9E #xD6 #x3A #x29 #x4D #x99 #x9B #x4C #x86 #x67 #x59 #x82))
