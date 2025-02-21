; Common material for versions of BLAKE that use 64-bit words.
;
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; Written from https://tools.ietf.org/rfc/rfc7693.txt.

(include-book "blake-common")
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/rightrotate" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

(local (in-theory (disable nth update-nth)))

;; number of bits in a word
(defconst *w* 64)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A word is a BV of size w.
(defund wordp (word)
  (declare (xargs :guard t))
  (unsigned-byte-p *w* word))

(defthm wordp-forward-to-natp
  (implies (wordp x)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable wordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a list of words
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; initialization vector, a list of 8 words
(defun iv ()
  (declare (xargs :guard t))
  '(#x6a09e667f3bcc908
    #xbb67ae8584caa73b
    #x3c6ef372fe94f82b
    #xa54ff53a5f1d36f1
    #x510e527fade682d1
    #x9b05688c2b3e6c1f
    #x1f83d9abfb41bd6b
    #x5be0cd19137e2179))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rot-word (amt word)
  (declare (xargs :guard (and (wordp word)
                              (natp amt)
                              (<= amt *w*))))
  (acl2::rightrotate *w* amt word))

(defthm wordp-of-rot-word
  (wordp (rot-word amt word))
  :hints (("Goal" :in-theory (enable rot-word acl2::rightrotate wordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund wordxor (x y)
  (declare (xargs :guard (and (wordp x)
                              (wordp y))))
  (bvxor *w* x y))

(defthm wordp-of-wordxor
  (wordp (wordxor x y))
  :hints (("Goal" :in-theory (enable wordxor wordp))))
