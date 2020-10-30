; Crypto Library: BLAKE-256 padding
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; This book formalizes the padding operation used in BLAKE-256.

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/bv-lists/unpackbv-def" :dir :system)
(local (include-book "kestrel/bv-lists/unpackbv" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defund pad-to-447-number-of-zeros (l)
  (declare (xargs :guard (natp l)))
  (mod (- 447 (+ 1 l)) 512))

;; The number of zeros is non-negative
(defthm pad-to-447-number-of-zeros-type
  (implies (natp l)
           (natp (pad-to-447-number-of-zeros l)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable pad-to-447-number-of-zeros))))

;; Extends the message so that its length is congruent to 447 mod 512.
(defund pad-to-447 (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (append msg
          (list 1)
          (repeat (pad-to-447-number-of-zeros (len msg)) 0)))

;; Padding gives a result whose length is congruent to 447 (mod 512).
(defthm pad-to-447-correct-1
  (equal (mod (len (pad-to-447 msg)) 512)
         447)
  :hints (("Goal" :in-theory (enable pad-to-447
                                     pad-to-447-number-of-zeros
                                     acl2::mod-sum-cases))))

;; At least 1 bit is added
(defthm pad-to-447-correct-2
  (<= 1
      (- (len (pad-to-447 msg))
         (len msg)))
  :hints (("Goal" :in-theory (enable pad-to-447 pad-to-447-number-of-zeros))))

;; At most 512 bits are added
(defthm pad-to-447-correct-3
  (<= (- (len (pad-to-447 msg))
         (len msg))
      512)
  :hints (("Goal" :in-theory (enable pad-to-447
                                     pad-to-447-number-of-zeros))))

;; MSG is a list of bits.  Add a single 1 bit, followed by enough 0 bits to
;; make the message length be congruent to 447 modulo 512, followed by a single
;; 1 bit, followed by the message length (big endian).
(defund pad (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg)
                              (< (len msg) (expt 2 64)))))
  (let* ((msg-len (len msg)))
    (append (pad-to-447 msg)
            (list 1)
            (unpackbv 64 1 msg-len))))

;; Padding makes the message longer.
(defthm pad-correct-1
  (<= (len msg)
      (len (pad msg)))
  :hints (("Goal" :in-theory (enable pad pad-to-447))))

;; The padded result always starts with the message.
(defthm pad-correct-2
  (implies (true-listp msg)
           (equal (take (len msg) (pad msg))
                  msg))
  :hints (("Goal" :in-theory (enable pad pad-to-447))))

;; Padding gives a result whose length is congruent to 0 (mod 512).
(defthm pad-correct-3
  (equal (mod (len (pad msg)) 512)
         0)
  :hints (("Goal" :in-theory (enable pad pad-to-447
                                     pad-to-447-number-of-zeros
                                     acl2::mod-sum-cases))))

;; ;; ;; Padding adds no more bits than necessary (adds at most 512 bits).  Note that
;; ;; ;; it can't add 0 bits, because it must always at least add a single 1.
;; (defthm pad-to-447-number-of-zeros-correct-4
;;   (<= (+ 1 (pad-to-447-number-of-zeros msg-len)) ;number of bits added (a 1 followed by 0s)
;;       512)
;;   :hints (("Goal" :in-theory (enable pad-to-447-number-of-zeros))))

(defthm all-unsigned-byte-p-of-pad
  (implies (all-unsigned-byte-p 1 msg)
           (all-unsigned-byte-p 1 (pad msg)))
  :hints (("Goal" :in-theory (enable pad pad-to-447))))

;; the padded message can be split into a whole number of 32-bit blocks.
(defthm mod-of-len-of-pad-and-32
  (equal (mod (len (pad msg)) 32)
         0)
  :hints (("Goal" :in-theory (enable pad pad-to-447
                                     pad-to-447-number-of-zeros
                                     acl2::mod-sum-cases))))

(defthm mod-of-floor-of-len-of-pad
  (equal (mod (floor (len (pad msg-bits)) 32)
              16)
         0)
  :hints (("Goal" :in-theory (e/d (pad PAD-TO-447
                                       pad-to-447-number-of-zeros
                                       mod
                                       acl2::mod-sum-cases)
                                  (floor)))))
