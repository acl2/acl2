; Crypto Library: Padding to make the length congruent to 448 mod 512.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PADDING")

;; This book formalizes a padding operation used in several hash functions.
;; Note that it does not include appending the 64-bit length field (because
;; algorithms differ in how exactly the length is represented, e.g., whether
;; the low-order half comes first).  See Section 5.1.1 of FIPS PUB 180-4.

;; See pad-to-448-tests.lisp and pad-to-448-validation.lisp

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))

(defund pad-to-448-number-of-zeros (l)
  (declare (xargs :guard (natp l)))
  (mod (- 448 (+ 1 l)) 512))

;; The number of zeros (k) is non-negative
(defthm pad-to-448-number-of-zeros-type
  (implies (natp l)
           (natp (pad-to-448-number-of-zeros l)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable pad-to-448-number-of-zeros))))

;; MSG is a list of any number of bits.  Add a single 1 bit, followed by enough
;; 0 bits to make the message length be congruent to 448 modulo 512.
(defund pad-to-448 (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (let* ((msg-len (len msg))
         (number-of-zeros (pad-to-448-number-of-zeros msg-len)))
    (append msg (cons 1 (repeat number-of-zeros 0)))))

;; Padding makes the message longer.
(defthm pad-to-448-correct-1
  (<= (len msg)
      (len (pad-to-448 msg)))
  :hints (("Goal" :in-theory (enable pad-to-448))))

;; The padded result always starts with the message.
(defthm pad-to-448-correct-2
  (implies (true-listp msg)
           (equal (take (len msg) (pad-to-448 msg))
                  msg))
  :hints (("Goal" :in-theory (enable pad-to-448))))

;; Padding gives a result whose length is congruent to 448 (mod 512).
(defthm pad-to-448-correct-3
  (equal (mod (len (pad-to-448 msg)) 512)
         448)
  :hints (("Goal" :in-theory (enable pad-to-448
                                     pad-to-448-number-of-zeros
                                     acl2::mod-sum-cases))))

;; Padding adds no more bits than necessary (adds at most 512 bits).  Note that
;; it can't add 0 bits, because it must always at least add a single 1.
(defthm pad-to-448-correct-4
  (<= (- (len (pad-to-448 msg))
         (len msg))
      512)
  :hints (("Goal" :in-theory (enable pad-to-448
                                     pad-to-448-number-of-zeros))))

(defthm all-unsigned-byte-p-of-pad-to-448
  (implies (all-unsigned-byte-p 1 msg)
           (all-unsigned-byte-p 1 (pad-to-448 msg)))
  :hints (("Goal" :in-theory (enable pad-to-448))))

;; The padded message can be split into a whole number of 32-bit blocks.
(defthm mod-of-len-of-pad-to-448-and-32
  (equal (mod (len (pad-to-448 msg)) 32)
         0)
  :hints (("Goal" :in-theory (enable pad-to-448
                                     pad-to-448-number-of-zeros
                                     acl2::mod-sum-cases))))
