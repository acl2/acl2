; A formal specification of the Salsa20 hash function
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SALSA")

;; Written from https://cr.yp.to/snuffle/spec.pdf.
;; See tests (from the specification) in salsa20-tests.lisp.

(include-book "portcullis")
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/packbv-little" :dir :system)
(include-book "kestrel/bv-lists/unpackbv-little" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(local (include-book "kestrel/bv-lists/packbv-little-and-unpackbv-little" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a word (32-bits, according to the spec)
(defund wordp (word)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 word))

(defthm wordp-forward-to-natp
  (implies (wordp word)
           (natp word))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable wordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Modular sum of two words
(defund word+ (u v)
  (declare (xargs :guard (and (wordp u)
                              (wordp v))))
  (bvplus 32 u v))

(defthm wordp-of-word+
  (wordp (word+ u v))
  :hints (("Goal" :in-theory (enable wordp word+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XOR of two words
(defund wordxor (u v)
  (declare (xargs :guard (and (wordp u)
                              (wordp v))))
  (bvxor 32 u v))

(defthm wordp-of-wordxor
  (wordp (wordxor u v))
  :hints (("Goal" :in-theory (enable wordp wordxor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leftrotation of word U by C places (chops C to 32 bits).
(defund wordrot (u c)
  (declare (xargs :guard (and (wordp u)
                              (natp c))))
  (leftrotate 32 (bvchop 32 c) u))

(defthm wordp-of-wordrot
  (wordp (wordrot c u))
  :hints (("Goal" :in-theory (enable wordp wordrot))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a list of words.
(defund word-listp (words)
  (declare (xargs :guard t))
  (if (atom words)
      (null words)
    (and (wordp (first words))
         (word-listp (rest words)))))

(defthm word-listp-forward-to-true-listp
  (implies (word-listp words)
           (true-listp words))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable word-listp))))

(defthm wordp-of-nth
  (implies (and (word-listp words)
                (natp n)
                (< n (len words)))
           (wordp (nth n words)))
  :hints (("Goal" :in-theory (enable word-listp nth))))

(defthm word-listp-of-cons
  (equal (word-listp (cons word words))
         (and (wordp word)
              (word-listp words)))
  :hints (("Goal" :in-theory (enable word-listp))))

(defthm word-listp-of-append
  (equal (word-listp (append words1 words2))
         (and (word-listp (true-list-fix words1))
              (word-listp words2)))
  :hints (("Goal" :in-theory (enable word-listp append))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper function to support naming the elements of a list.
;; Returns (mv val0 val1 val2 val3).
(defun split-list4 (l)
  (declare (xargs :guard (and (word-listp l)
                              (equal (len l) 4))))
  (mv (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l)))

;; Helper function to support naming the elements of a list.
;; Returns (mv val0 val1 ... val15).
(defun split-list16 (l)
  (declare (xargs :guard (and (word-listp l)
                              (equal (len l) 16))))
  (mv (nth 0 l) (nth 1 l) (nth 2 l) (nth 3 l)
      (nth 4 l) (nth 5 l) (nth 6 l) (nth 7 l)
      (nth 8 l) (nth 9 l) (nth 10 l) (nth 11 l)
      (nth 12 l) (nth 13 l) (nth 14 l) (nth 15 l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The quarterround operation from the spec.
(defund quarterround (y)
  (declare (xargs :guard (and (word-listp y)
                              (equal (len y) 4))))
  (mv-let (y0 y1 y2 y3)
    (split-list4 y)
    (let* ((z1 (wordxor y1 (wordrot (word+ y0 y3) 7)))
           (z2 (wordxor y2 (wordrot (word+ z1 y0) 9)))
           (z3 (wordxor y3 (wordrot (word+ z2 z1) 13)))
           (z0 (wordxor y0 (wordrot (word+ z3 z2) 18))))
      (list z0 z1 z2 z3))))

(defthm quarterround-type
  (implies (and (word-listp y)
                (equal (len y) 4))
           (and (word-listp (quarterround y))
                (equal (len (quarterround y)) 4)))
  :hints (("Goal" :in-theory (enable quarterround))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The rowround operation from the spec.
(defund rowround (y)
  (declare (xargs :guard (and (word-listp y)
                              (equal (len y) 16))))
  (mv-let (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)
    (split-list16 y)
    (mv-let (z0 z1 z2 z3)
      (split-list4 (quarterround (list y0 y1 y2 y3)))
      (mv-let (z5 z6 z7 z4)
        (split-list4 (quarterround (list y5 y6 y7 y4)))
        (mv-let (z10 z11 z8 z9)
          (split-list4 (quarterround (list y10 y11 y8 y9)))
          (mv-let (z15 z12 z13 z14)
            (split-list4 (quarterround (list y15 y12 y13 y14)))
            (list z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15)))))))

(defthm rowround-type
  (implies (and (word-listp y)
                (equal (len y) 16))
           (and (word-listp (rowround y))
                (equal (len (rowround y)) 16)))
  :hints (("Goal" :in-theory (enable rowround))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The columnround operation from the spec.
(defund columnround (x)
  (declare (xargs :guard (and (word-listp x)
                              (equal (len x) 16))))
  (mv-let (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
    (split-list16 x)
    (mv-let (y0 y4 y8 y12)
      (split-list4 (quarterround (list x0 x4 x8 x12)))
      (mv-let (y5 y9 y13 y1)
        (split-list4 (quarterround (list x5 x9 x13 x1)))
        (mv-let (y10 y14 y2 y6)
          (split-list4 (quarterround (list x10 x14 x2 x6)))
          (mv-let (y15 y3 y7 y11)
            (split-list4 (quarterround (list x15 x3 x7 x11)))
            (list y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)))))))

(defthm columnround-type
  (implies (and (word-listp x)
                (equal (len x) 16))
           (and (word-listp (columnround x))
                (equal (len (columnround x)) 16)))
  :hints (("Goal" :in-theory (enable columnround))))

;; Proof of the "equivalent formula" from the spec:
(defthm columnround-equivalent-formula
  (mv-let (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15)
    (split-list16 (columnround (list x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)))
    (equal (list y0 y4 y8 y12 y1 y5 y9 y13 y2 y6 y10 y14 y3 y7 y11 y15)
           (rowround (list x0 x4 x8 x12 x1 x5 x9 x13 x2 x6 x10 x14 x3 x7 x11 x15))))
  :hints (("Goal" :in-theory (enable rowround columnround))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The doubleround operation from the spec.
(defund doubleround (x)
  (declare (xargs :guard (and (word-listp x)
                              (equal (len x) 16))))
  (rowround (columnround x)))

(defthm doubleround-type
  (implies (and (word-listp x)
                (equal (len x) 16))
           (and (word-listp (doubleround x))
                (equal (len (doubleround x)) 16)))
  :hints (("Goal" :in-theory (enable doubleround))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The littleendian packing function from the spec.
(defund littleendian (b)
  (declare (xargs :guard (and (byte-listp b)
                              (equal (len b) 4))))
  (packbv-little 4 8 b))

;; Ensures that our definition of littleendian matches the spec:
(defthmd littleendian-alt-def
  (implies (and (unsigned-byte-p 8 b0)
                (unsigned-byte-p 8 b1)
                (unsigned-byte-p 8 b2)
                (unsigned-byte-p 8 b3))
           (equal (littleendian (list b0 b1 b2 b3))
                  (+ b0
                     (* (expt 2 8) b1)
                     (* (expt 2 16) b2)
                     (* (expt 2 24) b3))))
  :hints (("Goal" :in-theory (enable littleendian
                                     packbv-little
                                     acl2::packbv
                                     acl2::bvcat
                                     unsigned-byte-p
                                     acl2::reverse-list))))

(defthm wordp-of-littleendian
  (wordp (littleendian p))
  :hints (("Goal" :in-theory (enable wordp littleendian
                                     packbv-little))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inverse of littleendian (does unpacking).
(defund littleendian-inverse (word)
  (declare (xargs :guard (wordp word)))
  (unpackbv-little 4 8 word))

(defthm littleendian-inverse-type
  (implies (wordp word)
           (and (byte-listp (littleendian-inverse word))
                (equal (len (littleendian-inverse word))
                       4)))
  :hints (("Goal" :in-theory (enable wordp littleendian-inverse))))

;; Inversion proof 1
(defthm littleendian-inverse-of-littleendian
  (implies (and (byte-listp b)
                (equal (len b) 4))
           (equal (littleendian-inverse (littleendian b))
                  b))
  :hints (("Goal" :in-theory (enable littleendian littleendian-inverse))))

;; Inversion proof 2
(defthm littleendian-of-littleendian-inverse
  (implies (wordp word)
           (equal (littleendian (littleendian-inverse word))
                  word))
  :hints (("Goal" :in-theory (enable littleendian littleendian-inverse wordp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Applies doubleround N times, starting with X.
(defund doubleround-n-times (n x)
  (declare (xargs :guard (and (natp n)
                              (word-listp x)
                              (equal (len x) 16))))
  (if (zp n)
      x
    (doubleround-n-times (+ -1 n) (doubleround x))))

(defthm doubleround-n-times-type
  (implies (and (word-listp x)
                (equal (len x) 16))
           (and (word-listp (doubleround-n-times n x))
                (equal (len (doubleround-n-times n x)) 16)))
  :hints (("Goal" :in-theory (enable doubleround-n-times))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Salsa20 hash function
(defund salsa20 (x)
  (declare (xargs :guard (and (byte-listp x)
                              (equal (len x) 64))))
  (let ((x0 (littleendian (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x))))
        (x1 (littleendian (list (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x))))
        (x2 (littleendian (list (nth 8 x) (nth 9 x) (nth 10 x) (nth 11 x))))
        (x3 (littleendian (list (nth 12 x) (nth 13 x) (nth 14 x) (nth 15 x))))
        (x4 (littleendian (list (nth 16 x) (nth 17 x) (nth 18 x) (nth 19 x))))
        (x5 (littleendian (list (nth 20 x) (nth 21 x) (nth 22 x) (nth 23 x))))
        (x6 (littleendian (list (nth 24 x) (nth 25 x) (nth 26 x) (nth 27 x))))
        (x7 (littleendian (list (nth 28 x) (nth 29 x) (nth 30 x) (nth 31 x))))
        (x8 (littleendian (list (nth 32 x) (nth 33 x) (nth 34 x) (nth 35 x))))
        (x9 (littleendian (list (nth 36 x) (nth 37 x) (nth 38 x) (nth 39 x))))
        (x10 (littleendian (list (nth 40 x) (nth 41 x) (nth 42 x) (nth 43 x))))
        (x11 (littleendian (list (nth 44 x) (nth 45 x) (nth 46 x) (nth 47 x))))
        (x12 (littleendian (list (nth 48 x) (nth 49 x) (nth 50 x) (nth 51 x))))
        (x13 (littleendian (list (nth 52 x) (nth 53 x) (nth 54 x) (nth 55 x))))
        (x14 (littleendian (list (nth 56 x) (nth 57 x) (nth 58 x) (nth 59 x))))
        (x15 (littleendian (list (nth 60 x) (nth 61 x) (nth 62 x) (nth 63 x)))))
    (mv-let (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15)
      (split-list16 (doubleround-n-times 10 (list x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)))
      (append (littleendian-inverse (word+ z0 x0))
              (littleendian-inverse (word+ z1 x1))
              (littleendian-inverse (word+ z2 x2))
              (littleendian-inverse (word+ z3 x3))
              (littleendian-inverse (word+ z4 x4))
              (littleendian-inverse (word+ z5 x5))
              (littleendian-inverse (word+ z6 x6))
              (littleendian-inverse (word+ z7 x7))
              (littleendian-inverse (word+ z8 x8))
              (littleendian-inverse (word+ z9 x9))
              (littleendian-inverse (word+ z10 x10))
              (littleendian-inverse (word+ z11 x11))
              (littleendian-inverse (word+ z12 x12))
              (littleendian-inverse (word+ z13 x13))
              (littleendian-inverse (word+ z14 x14))
              (littleendian-inverse (word+ z15 x15))))))

(defthm salsa20-type
  (implies (and (byte-listp x)
                (equal (len x) 64))
           (and (byte-listp (salsa20 x))
                (equal (len (salsa20 x)) 64)))
  :hints (("Goal" :in-theory (enable salsa20))))
