; Crypto Library: Padding to make the length congruent to 896 mod 1024.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PADDING")

;; This book formalizes a padding operation used in several hash functions

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p-of-repeat" :dir :system))

;; MSG is a list of any number of bits.  Add a single 1 bit, followed by enough
;; zero bits to make the message length be congruent to 896 modulo 1024.
(defund pad-to-896 (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg))))
  (let* ((msg-len (len msg))
         (number-of-zeros (mod (- 896 (+ 1 msg-len)) 1024)))
    (append msg (cons 1 (repeat number-of-zeros 0)))))

;; Padding makes the message longer.
(defthm pad-to-896-correct-1
  (<= (len msg)
      (len (pad-to-896 msg)))
  :hints (("Goal" :in-theory (enable pad-to-896))))

;; The padded result always starts with the message.
(defthm pad-to-896-correct-2
  (implies (true-listp msg)
           (equal (take (len msg) (pad-to-896 msg))
                  msg))
  :hints (("Goal" :in-theory (enable pad-to-896))))

;; Padding gives a result whose length is congruent to 896 (mod 1024).
(defthm pad-to-896-correct-3
  (equal (mod (len (pad-to-896 msg)) 1024)
         896)
  :hints (("Goal" :in-theory (enable pad-to-896))))

;; Padding adds no more bits than necessary (adds at most 1024 bits).  Note that
;; it can't add 0 bits, because it must always at least add a single 1.
(defthm pad-to-896-correct-4
  (<= (- (len (pad-to-896 msg))
         (len msg))
      1024)
  :hints (("Goal" :in-theory (enable pad-to-896))))

(defthm all-unsigned-byte-p-of-pad-to-896
  (implies (all-unsigned-byte-p 1 msg)
           (all-unsigned-byte-p 1 (pad-to-896 msg)))
  :hints (("Goal" :in-theory (enable pad-to-896))))

;; The padded message can be split into a whole number of 64-bit blocks.
(defthm mod-of-len-of-pad-to-896-and-64
  (equal (mod (len (pad-to-896 msg)) 64)
         0)
  :hints (("Goal" :in-theory (enable pad-to-896))))
