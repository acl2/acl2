; Common material for versions of BLAKE that use 32-bit words.
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; Written from https://tools.ietf.org/rfc/rfc7693.txt.

(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/rightrotate" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

(local (in-theory (disable nth update-nth)))

;; number of bits in a word
(defconst *w* 32)

;; A word is a BV of size w.
(defund wordp (word)
  (declare (xargs :guard t))
  (unsigned-byte-p *w* word))

(defthm wordp-forward-to-natp
  (implies (wordp x)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable wordp))))

;; Recognize a list of words
(defund all-wordp (words)
  (declare (xargs :guard t))
  (if (atom words)
      t
    (and (wordp (first words))
         (all-wordp (rest words)))))

(defthm all-wordp-of-cons
  (equal (all-wordp (cons x y))
         (and (wordp x)
              (all-wordp y)))
  :hints (("Goal" :in-theory (enable all-wordp))))

(defthm all-wordp-of-update-nth
  (implies (and (wordp word)
                (all-wordp words)
                (natp n)
                (< n (len words)))
           (all-wordp (update-nth n word words)))
  :hints (("Goal" :in-theory (enable all-wordp UPDATE-NTH))))

(defthm wordp-of-nth-when-all-wordp
  (implies (and (all-wordp words)
                (natp n)
                (< n (len words)))
           (wordp (nth n words)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm integerp-of-nth-when-all-wordp
  (implies (and (all-wordp words)
                (natp n)
                (< n (len words)))
           (integerp (nth n words)))
  :hints (("Goal" :in-theory (enable nth all-wordp))))

(defthm acl2-numberp-of-nth-when-all-wordp
  (implies (and (all-wordp words)
                (natp n)
                (< n (len words)))
           (acl2-numberp (nth n words)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm rationalp-of-nth-when-all-wordp
  (implies (and (all-wordp words)
                (natp n)
                (< n (len words)))
           (rationalp (nth n words)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm all-wordp-of-append
  (implies (and (all-wordp x)
                (all-wordp y))
           (all-wordp (append x y)))
  :hints (("Goal" :in-theory (enable all-wordp))))

;; A block is a list of 16 words.
(defund blockp (block)
  (declare (xargs :guard t))
  (and (true-listp block)
       (= 16 (len block))
       (all-wordp block)))

(defthm blockp-forward-to-true-listp
  (implies (blockp block)
           (true-listp block))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable blockp))))

(defthm blockp-forward-to-equal-of-len
  (implies (blockp block)
           (equal 16 (len block)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable blockp))))

(defthm acl2-numberp-of-nth-when-blockp
  (implies (and (blockp block)
                (natp n)
                (< n 16))
           (acl2-numberp (nth n block)))
  :hints (("Goal" :in-theory (enable blockp))))

(defthm integerp-of-nth-when-blockp
  (implies (and (blockp block)
                (natp n)
                (< n 16))
           (integerp (nth n block)))
  :hints (("Goal" :in-theory (enable blockp))))

(defthm rationalp-of-nth-when-blockp
  (implies (and (blockp block)
                (natp n)
                (< n 16))
           (rationalp (nth n block)))
  :hints (("Goal" :in-theory (enable blockp))))

(defthm wordp-of-nth-when-blockp
  (implies (and (blockp block)
                (natp n)
                (< n 16))
           (wordp (nth n block)))
  :hints (("Goal" :in-theory (enable blockp))))

(defthm blockp-of-update-nth
  (implies (and (blockp block)
                (wordp word)
                (natp n)
                (< n 16))
           (blockp (update-nth n word block)))
  :hints (("Goal" :in-theory (enable blockp))))

(defthm blockp-of-append
  (implies (and (all-wordp x)
                (all-wordp y)
                (true-listp y)
                (equal 16 (+ (len x) (len y))))
           (blockp (append x y)))
  :hints (("Goal" :in-theory (enable blockp))))

;; Recognize a list of blocks
(defund all-blockp (blocks)
  (declare (xargs :guard t))
  (if (atom blocks)
      t
    (and (blockp (first blocks))
         (all-blockp (rest blocks)))))

(defthm all-blockp-of-cons
  (equal (all-blockp (cons block blocks))
         (and (blockp block)
              (all-blockp blocks)))
  :hints (("Goal" :in-theory (enable all-blockp))))

(defthm blockp-of-nth-when-all-blockp
  (implies (and (all-blockp blocks)
                (natp n)
                (< n (len blocks)))
           (blockp (nth n blocks)))
  :hints (("Goal" :in-theory (enable all-blockp nth))))

;; initialization vector, a list of 8 words
(defun iv ()
  (declare (xargs :guard t))
  '(#x6A09E667
    #xBB67AE85
    #x3C6EF372
    #xA54FF53A
    #x510E527F
    #x9B05688C
    #x1F83D9AB
    #x5BE0CD19))

(defund sigma ()
  (declare (xargs :guard t))
  '(( 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15)
    (14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3)
    (11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4)
    ( 7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8)
    ( 9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13)
    ( 2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9)
    (12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11)
    (13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10)
    ( 6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5)
    (10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0)))

(in-theory (disable (:e sigma)))

(defthm len-of-sigma
  (equal (len (sigma))
         10)
  :hints (("Goal" :in-theory (enable sigma))))

(defthm items-have-len-of-sigma
  (acl2::items-have-len 16 (sigma))
  :hints (("Goal" :in-theory (enable sigma))))

(defthm all-true-listp-of-sigma
  (acl2::all-true-listp (sigma))
  :hints (("Goal" :in-theory (enable sigma))))

(defthm len-of-nth-of-sigma
  (implies (and (natp n)
                (< n 10))
           (equal (len (nth n (sigma)))
                  16))
  :hints (("Goal" :use (:instance items-have-len-of-sigma)
           :in-theory (disable items-have-len-of-sigma))))

(defun all-nat16 (items)
  (if (endp items)
      t
    (and (natp (first items))
         (< (first items) 16)
         (all-nat16 (rest items)))))

(defthm <-of-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (< (nth n x) 16))
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm <=-of-0-and-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (<= 0 (nth n x)))
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-of-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (natp (nth n x)))
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm integerp-of-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (integerp (nth n x)))
    :hints (("Goal" :in-theory (e/d (nth) ()))))

(defun all-all-nat16 (items)
  (if (endp items)
      t
    (and (all-nat16 (first items))
         (all-all-nat16 (rest items)))))

(defthm all-all-nat16-of-sigma
  (all-all-nat16 (sigma))
  :hints (("Goal" :in-theory (enable sigma))))

(defthm all-nat16-of-nth-when-all-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-all-nat16 x))
           (all-nat16 (nth n x)))
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defund rot-word (amt word)
  (declare (xargs :guard (and (wordp word)
                              (natp amt)
                              (<= amt *w*))))
  (acl2::rightrotate *w* amt word))

(defthm wordp-of-rot-word
  (wordp (rot-word amt word))
  :hints (("Goal" :in-theory (enable rot-word acl2::rightrotate wordp))))

(defund wordxor (x y)
  (declare (xargs :guard (and (wordp x)
                              (wordp y))))
  (bvxor *w* x y))

(defthm wordp-of-wordxor
  (wordp (wordxor x y))
  :hints (("Goal" :in-theory (enable wordxor wordp))))
