; Common material for versions of BLAKE that use 64-bit words.
;
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)

;; No need to extend this for blake2s, because row indices above 10 are reduced
;; mod 10.
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
  (implies (and ;; (natp n)
                (< n 10))
           (equal (len (nth n (sigma)))
                  16))
  :hints (("Goal" :use (:instance items-have-len-of-sigma)
           :in-theory (disable items-have-len-of-sigma))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a list of naturals, each less than 16.  For example, a row of
;; sigma.
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
  :hints (("Goal" :in-theory (enable nth))))

(defthm <=-of-0-and-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (<= 0 (nth n x)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm natp-of-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (natp (nth n x)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm integerp-of-nth-when-all-nat16
  (implies (and (natp n)
                (< n (len x))
                (all-nat16 x))
           (integerp (nth n x)))
  :hints (("Goal" :in-theory (enable nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a list of lists of naturals, each less than 16.  For example,
;; sigma.
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
  :hints (("Goal" :in-theory (enable nth))))
