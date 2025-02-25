; Formal specification of BLAKE2b
;
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; Written from https://tools.ietf.org/rfc/rfc7693.txt.  Section references
;; below refer to that document.

;; See blake2b-tests.lisp

(include-book "blake-common-64")
(include-book "kestrel/lists-light/repeat-def" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/bv/bvshl-def" :dir :system)
(include-book "kestrel/bv/bvshr-def" :dir :system)
(include-book "kestrel/bv/bvplus-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/bvplus" :dir :system))
(local (include-book "kestrel/bv/bvshl" :dir :system))

(local (in-theory (disable len true-listp nth update-nth expt ;; prevent inductions
                           acl2::mod-sum-cases nth-update-nth ;; prevent case splits
                           acl2::mod-by-4-becomes-bvchop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.1

;; Note that *w* (bits in word) is defined in blake-common-64.lisp.

(defconst *r* 12) ;; number of rounds in F

(defconst *bb* 128)  ;; number of bytes in a block

(defconst *max-hash-bytes* 64)

(defconst *max-key-bytes* 64)

;; Since ll < 2^128
(defconst *max-input-bytes* (+ -1 (expt 2 128)))

;; G rotation constants:
(defconst *r1* 32)
(defconst *r2* 24)
(defconst *r3* 16)
(defconst *r4* 63)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Needed since the mod of + in the spec gets turned into bvplus
(defthm wordp-of-bvplus
  (wordp (bvplus *w* x y))
  :hints (("Goal" :in-theory (enable wordp))))

(defconst *word-limit* (expt 2 *w*))

(defconst *max-word* (+ -1 (expt 2 *w*)))

(defthm wordp-of-mod
  (implies (integerp x)
           (wordp (mod x *word-limit*)))
  :hints (("Goal" :in-theory (enable wordp unsigned-byte-p))))

(defthm wordp-of-bvshl
  (implies (and (integerp x)
                (natp amt)
                (<= amt *w*))
           (wordp (bvshl *w* x amt)))
  :hints (("Goal" :in-theory (enable wordp bvshl natp))))

(defthm wordp-of-bvshr-special
  (implies (unsigned-byte-p (* 2 *w*) x)
           (wordp (bvshr (* 2 *w*) x *w*)))
  :hints (("Goal" :in-theory (enable wordp bvshr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *bytes-per-word* (/ *w* 8)) ; since *w* is bits-per-word

;; Convert a list of 8 bytes into a word, in little endian fashion.
(defund bytes-to-word (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (= *bytes-per-word* (len bytes))
                              (all-unsigned-byte-p 8 bytes))))
  (acl2::bvcat2 8 (nth 7 bytes) ;most significant byte
                8 (nth 6 bytes)
                8 (nth 5 bytes)
                8 (nth 4 bytes)
                8 (nth 3 bytes)
                8 (nth 2 bytes)
                8 (nth 1 bytes)
                8 (nth 0 bytes)))

(defthm wordp-of-bytes-to-word
  (wordp (bytes-to-word bytes))
  :hints (("Goal" :in-theory (enable bytes-to-word wordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert a list of bytes into a list of words, in little endian fashion.
(defund bytes-to-words (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (acl2::all-unsigned-byte-p 8 bytes)
                              (equal 0 (mod (len bytes) *bytes-per-word*)) ;; we have an integral number of words
                              )))
  (if (endp bytes)
      nil
    (cons (bytes-to-word (take *bytes-per-word* bytes))
          (bytes-to-words (nthcdr *bytes-per-word* bytes)))))

(defthm len-of-bytes-to-words
  (implies (equal 0 (mod (len bytes) *bytes-per-word*))
           (equal (len (bytes-to-words bytes))
                  (/ (len bytes) *bytes-per-word*)))
  :hints (("Goal" :in-theory (enable bytes-to-words))))

(defthm all-wordp-of-bytes-to-words
  (all-wordp (bytes-to-words bytes))
  :hints (("Goal" :in-theory (enable bytes-to-words))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert a list of 128 bytes into a block
(defund bytes-to-block (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (= *bb* (len bytes))
                              (all-unsigned-byte-p 8 bytes))))
  (bytes-to-words bytes))

(defthm blockp-of-bytes-to-block
  (implies (= *bb* (len bytes))
           (blockp (bytes-to-block bytes)))
  :hints (("Goal" :in-theory (enable blockp bytes-to-block))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (all-blockp (bytes-to-blocks bytes))
  :hints (("Goal" :in-theory (enable blockp bytes-to-blocks all-blockp))))

(defthm len-of-bytes-to-blocks
  (implies (equal 0 (mod (len bytes) *bb*))
           (equal (len (bytes-to-blocks bytes))
                  (/ (len bytes) *bb*)))
  :hints (("Goal" :in-theory (enable bytes-to-blocks))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of bytes
(defund pad-input-bytes (input-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 input-bytes)
                              (true-listp input-bytes))))
  (let* ((ll (len input-bytes))
         (bytes-in-last-block (mod ll *bb*))
         (num-padding-bytes (if (= 0 bytes-in-last-block)
                                0 ;; ll is an exact multiple of the block size
                              (- *bb* bytes-in-last-block))))
    (append input-bytes (acl2::repeat num-padding-bytes 0))))

(defthm all-unsigned-byte-p-of-pad-input-bytes
  (implies (all-unsigned-byte-p 8 input-bytes)
           (all-unsigned-byte-p 8 (pad-input-bytes input-bytes)))
  :hints (("Goal" :in-theory (enable pad-input-bytes))))

(defthm len-of-pad-input-bytes
  (equal (len (pad-input-bytes input-bytes))
         (let ((ll (len input-bytes)))
           (* *bb* (ceiling ll *bb*))))
  :hints (("Goal" :use (:instance mod
                                  (x (len input-bytes))
                                  (y *bb*))
           :in-theory (enable acl2::ceiling-in-terms-of-floor
                              acl2::floor-of---arg1
                              pad-input-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Pad a non-empty key up to 128 bytes and convert into a block
(defund padded-key-block (key-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (consp key-bytes)
                              (<= (len key-bytes) *max-key-bytes*))))
  (let* ((kk (len key-bytes))
         (num-padding-bytes (- *bb* kk))
         (padded-key-bytes (append key-bytes (acl2::repeat num-padding-bytes 0))))
    (bytes-to-block padded-key-bytes)))

(defthm blockp-of-padded-key-block
  (implies (<= (len key-bytes) *max-key-bytes*)
           (blockp (padded-key-block key-bytes)))
  :hints (("Goal" :in-theory (enable padded-key-block blockp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See Sec 3.3 (Padding Data ...)
(defund d-blocks (input-bytes key-bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 input-bytes)
                              (true-listp input-bytes)
                              (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (<= (len key-bytes) *max-key-bytes*))))
  (if (and (not (consp input-bytes))
           (not (consp key-bytes)))
      ;; special case for unkeyed empty message: d contains a single block of
      ;; all 0s:
      (list (repeat 16 0)) ; a block is 16 words
    (let* ((padded-input-bytes (pad-input-bytes input-bytes)))
      (if (consp key-bytes)
          (cons (padded-key-block key-bytes)
                (bytes-to-blocks padded-input-bytes))
        (bytes-to-blocks padded-input-bytes)))))

(defthm consp-of-d-blocks
  (consp (d-blocks input-bytes key-bytes))
  :hints (("Goal" :in-theory (e/d (d-blocks) (len-of-bytes-to-blocks))
           :use (:instance len-of-bytes-to-blocks (bytes (pad-input-bytes input-bytes))))))

(defthm all-blockp-of-d-blocks
  (implies (<= (len key-bytes) *max-key-bytes*)
           (all-blockp (d-blocks input-bytes key-bytes)))
  :hints (("Goal" :in-theory (enable d-blocks))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; number of blocks (see Sec 3.3)
(defun dd (kk ll)
  (declare (xargs :guard (and (natp kk)
                              (<= kk *max-key-bytes*)
                              (natp ll)
                              (<= ll *max-input-bytes*))))
  (if (and (= kk 0)
           (= ll 0))
      1 ; special case for unkeyed empty message
    (+ (ceiling kk *bb*)
       (ceiling ll *bb*))))

;; Shows that dd is correct
(defthm len-of-d-blocks
  (implies (<= (len key-bytes) *max-key-bytes*)
           (equal (len (d-blocks input-bytes key-bytes))
                  (dd (len key-bytes) (len input-bytes))))
  :hints (("Goal" :in-theory (enable d-blocks
                                     acl2::ceiling-in-terms-of-floor
                                     acl2::floor-of---arg1))))

;; Not actually allowed (see NOTES below).
(defconst *max-number-of-blocks*
  ;; Calls dd with maximum values for both arguments:
  (dd *max-key-bytes* *max-input-bytes*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 ;; This speeds up the guard proof for g
 (defthm bvplus-intro
   (implies (and (integerp x)
                 (integerp y))
            (equal (mod (+ x y) *word-limit*)
                   (bvplus *w* x y)))
   :hints (("Goal" :in-theory (enable bvplus bvchop)))))

;; Mixing Function G (See Sec 3.1)
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
  :hints (("Goal" :in-theory (enable g acl2::integerp-of-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Formalization of the first FOR loop in the compression function F (see Sec
;; 3.2).
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Formalization of the second FOR loop in the compression function F (see Sec
;; 3.2).
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compression Function F (see Sec 3.2)
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
                            (wordxor (nth 14 v) *max-word*)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Formalization of the FOR loop in function BLAKE2 (see Sec 3.3).
(defund loop1 (i bound h d)
  (declare (xargs :guard (and (natp i)
                              (natp bound) ; always dd - 2
                              (<= i (+ 1 bound))
                              (equal bound (- (len d) 2))
                              (true-listp h)
                              (all-wordp h)
                              (= 8 (len h))
                              (true-listp d)
                              (all-blockp d)
                              ;; NOTE: We must exclude d = *max-number-of-blocks*,
                              ;; since then the third agument of the call to f here
                              ;; would be too large.
                              (< (len d) *max-number-of-blocks*))
                  :measure (nfix (+ 1 (- bound i)))
                  :hints (("Goal" :in-theory (enable natp)))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert a 64-bit word into a list of 8 bytes, in little endian fashion.
;; todo: prove inversion
(defund word-to-bytes (word)
  (declare (xargs :guard (wordp word)))
  (list (slice 7 0 word)
        (slice 15 8 word)
        (slice 23 16 word)
        (slice 31 24 word)
        (slice 39 32 word)
        (slice 47 40 word)
        (slice 55 48 word)
        (slice 63 56 word) ;; most significant byte
        ))

(defthm len-of-word-to-bytes
  (equal (len (word-to-bytes word))
         *bytes-per-word*)
  :hints (("Goal" :in-theory (enable word-to-bytes))))

(defthm all-unsigned-byte-p-of-word-to-bytes
  (all-unsigned-byte-p 8 (word-to-bytes word))
  :hints (("Goal" :in-theory (enable word-to-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Convert a list of 64-bit words into a list of bytes, in little endian fashion.
(defund words-to-bytes (words)
  (declare (xargs :guard (and (true-listp words)
                              (all-wordp words))))
  (if (endp words)
      nil
    (append (word-to-bytes (first words))
            (words-to-bytes (rest words)))))

(defthm len-of-words-to-bytes
  (equal (len (words-to-bytes words))
         (* *bytes-per-word* (len words)))
  :hints (("Goal" :in-theory (enable words-to-bytes))))

(defthm all-unsigned-byte-p-of-words-to-bytes
  (all-unsigned-byte-p 8 (words-to-bytes words))
  :hints (("Goal" :in-theory (enable words-to-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The function BLAKE2 (see Sec 3.3).
;; Returns the hash, as list of bytes of length NN.
(defund blake2b (input-bytes
                 key-bytes
                 nn ;; number of hash bytes to produce
                 )
  (declare (xargs :guard (and (all-unsigned-byte-p 8 input-bytes)
                              (true-listp input-bytes)
                              ;; NOTE: We would like to say:
                              ;; (<= (len input-bytes) *max-input-bytes*)
                              ;; but that would allow potential overflows in
                              ;; the second call of F below and in the call of
                              ;; F in LOOP1 above.
                              (<= (len input-bytes)
                                  (if (= 0 (len key-bytes))
                                      *max-input-bytes*
                                    ;; Prevents overflows in the calls of f
                                    ;; below:
                                    (- *max-input-bytes* *bb*)))
                              (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (<= (len key-bytes) *max-key-bytes*)
                              (posp nn)
                              (<= nn *max-hash-bytes*))
                  :guard-hints (("Goal" :in-theory (enable wordp natp unsigned-byte-p)))))
  (let* ((ll (len input-bytes))
         (kk (len key-bytes))
         (d (d-blocks input-bytes key-bytes))
         (dd (len d))
         (h (iv)) ; initialization vector
         ;; XOR in the parameter block:
         (h (update-nth 0
                        (wordxor (nth 0 h)
                                 (wordxor #x01010000
                                          (wordxor (bvshl *w* kk 8)
                                                   nn)))
                        h))
         ;; Process padded key and data blocks:
         (h (if (> dd 1)
                ;; The FOR loop:
                (loop1 0 (- dd 2) h d)
              h))
         ;; Final block:
         (h (if (= kk 0)
                (f h (nth (- dd 1) d) ll t)
              (f h
                 (nth (- dd 1) d)
                 (+ ll *bb*)
                 t))))
    ;; Extract first nn bytes to form the returned hash:
    (take nn (words-to-bytes h))))

(defthm len-of-blake2b
  (implies (and (posp nn)
                (<= nn *max-hash-bytes*))
           (equal (len (blake2b input-bytes key-bytes nn))
                  nn))
  :hints (("Goal" :in-theory (enable blake2b))))

(defthm all-unsigned-byte-p-of-blake2b
  (implies (<= nn *max-hash-bytes*)
           (all-unsigned-byte-p 8 (blake2b input-bytes key-bytes nn)))
  :hints (("Goal" :in-theory (enable blake2b))))
