; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top" :dir :system))

; extra-defs.lisp
;
; These are some functions I wanted when writing specs for integer and
; packed-integer instructions.

; BOZO consider using RDB instead?

(defun nth-slice2 (n x)
  "Extract the Nth 2-bit slice of the integer X."
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -2)) (1- (expt 2 2)))
       :exec
       (logand (ash x (* n -2)) #x3)))

(defun nth-slice8 (n x)
  "Extract the Nth 8-bit slice of the integer X."
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -8)) (1- (expt 2 8)))
       :exec
       (logand (ash x (* n -8)) #xFF)))

(defun nth-slice16 (n x)
  "Extract the Nth 16-bit slice of the integer X."
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -16)) (1- (expt 2 16)))
       :exec
       (logand (ash x (* n -16)) #xFFFF)))

(defun nth-slice32 (n x)
  "Extract the Nth 32-bit slice of the integer X."
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -32)) (1- (expt 2 32)))
       :exec
       (logand (ash x (* n -32)) #ux_FFFF_FFFF)))

(defun nth-slice64 (n x)
  "Extract the Nth 64-bit slice of the integer X."
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -64)) (1- (expt 2 64)))
       :exec
       (logand (ash x (* n -64)) #ux_FFFF_FFFF_FFFF_FFFF)))


(defthm natp-of-nth-slice2
  (natp (nth-slice2 n x))
  :rule-classes :type-prescription)

(defthm natp-of-nth-slice8
  (natp (nth-slice8 n x))
  :rule-classes :type-prescription)

(defthm natp-of-nth-slice16
  (natp (nth-slice16 n x))
  :rule-classes :type-prescription)

(defthm natp-of-nth-slice32
  (natp (nth-slice32 n x))
  :rule-classes :type-prescription)

(defthm natp-of-nth-slice64
  (natp (nth-slice64 n x))
  :rule-classes :type-prescription)




(defun negate-slice8 (x)
  "X is an 8-bit natural.  Treat it as a signed, 8-bit value.  Compute the
two's complement negation of X, and return it as an 8-bit natural.  For
instance, (negate-slice8 3) = 253."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 8)))
       :exec
       (logand (+ 1 (lognot x)) #xFF)))

(defun negate-slice16 (x)
  "X is a 16-bit natural.  Treat it as a signed, 16-bit value.  Compute the
   two's complement negation of X and return it as a 16-bit natural."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 16)))
       :exec
       (logand (+ 1 (lognot x)) #xFFFF)))

(defun negate-slice32 (x)
  "X is a 32-bit natural.  Treat it as a signed, 32-bit value.  Compute the
two's complement negation of X and return it as a 32-bit natural."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 32)))
       :exec
       (logand (+ 1 (lognot x)) #ux_FFFF_FFFF)))

(defun negate-slice64 (x)
  "X is a 64-bit natural.  Treat it as a signed, 64-bit value.  Compute the
two's complement negation of X and return it as a 64-bit natural."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 64)))
       :exec
       (logand (+ 1 (lognot x)) #ux_FFFF_FFFF_FFFF_FFFF)))

(defthm natp-of-negate-slice8
  (natp (negate-slice8 x))
  :rule-classes :type-prescription)

(defthm natp-of-negate-slice16
  (natp (negate-slice16 x))
  :rule-classes :type-prescription)

(defthm natp-of-negate-slice32
  (natp (negate-slice32 x))
  :rule-classes :type-prescription)

(defthm natp-of-negate-slice64
  (natp (negate-slice64 x))
  :rule-classes :type-prescription)


; BOZO consider extending ihsext-basics with stuff about expt-2.
(local (defthm posp-expt-2
         (<= 0 (expt 2 width))
         :rule-classes ((:rewrite)
                        (:linear)
                        (:type-prescription))
         :hints(("Goal" :in-theory (enable expt)))))

(local (defthm integerp-expt-2
         (implies (<= 0 width)
                  (integerp (expt 2 width)))
         :rule-classes ((:rewrite)
                        (:type-prescription))
         :hints(("Goal" :in-theory (enable expt)))))

(defun signed-val-of-nat (width x)
  "X is a natural number; it may be of any size because we only consider the
bits of X[WIDTH-1:0].  We interpret these bits as a WIDTH-bit 2's complement
integer.  The resulting value is an integer in [-2^{width-1}, 2^{width-1}-1]."
  (declare (xargs :guard (and (posp width)
                              (natp x))))
  (mbe :logic
       (let* ((width (nfix width))
              (x     (nfix x))
              (mask  (1- (expt 2 width)))
              (x     (logand x mask)))
         (if (logbitp (- width 1) x)
             (- (logand (+ 1 (lognot x)) mask))
           x))
       :exec
       (let* ((mask (1- (expt 2 width)))
              (x    (logand x mask)))
         (if (logbitp (- width 1) x)
             (- (logand (+ 1 (lognot x)) mask))
           x))))

(defthm integerp-of-signed-val-of-nat
  (integerp (signed-val-of-nat width x))
  :rule-classes :type-prescription)


(defun signed-val-of-slice8 (x)
  "X is an 8-bit natural.  Interpret it as a signed, 8-bit value and return
this value as an ACL2 integer.  The answer is in [-128, 127]."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (let ((x (nfix x)))
         (if (logbitp 7 x)
             (- (logand (+ 1 (lognot x)) (1- (expt 2 8))))
           x))
       :exec
       (if (logbitp 7 x)
           (- (logand (+ 1 (lognot x)) #xFF))
         x)))

(defun signed-val-of-slice16 (x)
  "X is a 16-bit natural.  Interpret it as a signed, 16-bit value and return
this value as an ACL2 integer.  The answer is in [-32768, 32767]."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (let ((x (nfix x)))
         (if (logbitp 15 x)
             (- (logand (+ 1 (lognot x)) (1- (expt 2 16))))
           x))
       :exec
       (if (logbitp 15 x)
           (- (logand (+ 1 (lognot x)) #xFFFF))
         x)))

(defun signed-val-of-slice32 (x)
  "X is a 32-bit natural.  Interpret it as a signed, 32-bit value and return
this value as an ACL2 integer.  The answer is in [-2^31, 2^31-1]."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (let ((x (nfix x)))
         (if (logbitp 31 x)
             (- (logand (+ 1 (lognot x)) (1- (expt 2 32))))
           x))
       :exec
       (if (logbitp 31 x)
           (- (logand (+ 1 (lognot x)) #ux_FFFF_FFFF))
         x)))

(defun signed-val-of-slice64 (x)
  "X is a 64-bit natural.  Interpret it as a signed, 64-bit value and return
this value as an ACL2 integer.  The answer is in [-2^63, 2^63-1]."
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (let ((x (nfix x)))
         (if (logbitp 63 x)
             (- (logand (+ 1 (lognot x)) (1- (expt 2 64))))
           x))
       :exec
       (if (logbitp 63 x)
           (- (logand (+ 1 (lognot x)) #ux_FFFF_FFFF_FFFF_FFFF))
         x)))

(defthm integerp-of-signed-val-of-slice8
  (integerp (signed-val-of-slice8 x))
  :rule-classes :type-prescription)

(defthm integerp-of-signed-val-of-slice16
  (integerp (signed-val-of-slice16 x))
  :rule-classes :type-prescription)

(defthm integerp-of-signed-val-of-slice32
  (integerp (signed-val-of-slice32 x))
  :rule-classes :type-prescription)

(defthm integerp-of-signed-val-of-slice64
  (integerp (signed-val-of-slice64 x))
  :rule-classes :type-prescription)






(defun abs-diff (a b)
  "(ABS-DIFF A B) is provably equal to (ABS (- (IFIX A) (IFIX B))).

ABS-DIFF performs better than (ABS (- A B)) for symbolic simulation with GL: it
decides whether the subtraction will be necessary by looking at the arguments,
which tend to be simple and nicely interleaved, instead of by looking at the
result, which tend to be complex since they are the combined arguments.

For an AIG-CERT-MODE proof of the 64-bit PSADBW instruction, using ABS-DIFF
instead of (ABS (- A B)) reduced the proof time from 56.2 seconds to 37.44
seconds."
    (declare (xargs :guard (and (integerp a)
                                (integerp b))))
    (mbe :logic
         (let ((a (ifix a))
               (b (ifix b)))
           (if (<= b a)
               (- a b)
             (- b a)))
         :exec
         (if (<= b a)
             (- a b)
           (- b a))))

(defthm abs-diff-correct
  (equal (abs-diff a b)
         (abs (- (ifix a) (ifix b)))))

(defthm natp-of-abs-diff
  (natp (abs-diff a b))
  :rule-classes :type-prescription)



(defun setbit (n x)
  "Set X[n] := 1"
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (let ((n (nfix n))
             (x (ifix x)))
         (logior (ash 1 n) x))
       :exec
       (logior (ash 1 n) x)))

(defthm integerp-of-setbit
  (integerp (setbit n x))
  :rule-classes :type-prescription)


(defun clearbit (n x)
  "Set X[n] := 0"
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (mbe :logic
       (let ((n (nfix n))
             (x (ifix x)))
         (logand (lognot (ash 1 n)) x))
       :exec
       (logand (lognot (ash 1 n)) x)))

(defthm integerp-of-clearbit
  (integerp (clearbit n x))
  :rule-classes :type-prescription)


(defun copybit (n from to)
  "Set To[n] := From[n]"
  (declare (xargs :guard (and (natp n)
                              (integerp from)
                              (integerp to))))
  (if (logbitp n from)
      (setbit n to)
    (clearbit n to)))

(defthm integerp-of-copybit
  (integerp (copybit n from to))
  :rule-classes :type-prescription)


(defun notbit (n x)
  "Set X[n] := ~X[n]"
  (declare (xargs :guard (and (natp n)
                              (integerp x))))
  (if (logbitp n x)
      (clearbit n x)
    (setbit n x)))

(defthm integerp-of-notbit
  (integerp (notbit n x))
  :rule-classes :type-prescription)



(local
 (encapsulate
   ()
   (local (defun my-induct (x n)
            (if (zp n)
                x
              (my-induct (logcdr x) (- n 1)))))

   (local (defthm ash-to-logtail
            (implies (natp n)
                     (equal (ash x (- n))
                            (logtail n x)))
            :hints(("Goal"
                    :induct (my-induct x n)
                    :in-theory (e/d* (logtail** ash*)
                                     (logtail))))))

   (defthm shift-right-smaller
     (implies (not (zp src))
              (< (ash src -1) src))
     :hints(("Goal" :in-theory (disable logtail))))))

(defun bitscan-fwd (src)
  "(BITSCAN-FWD SRC) returns the bit position of the least significant bit in
SRC that is set, or 0 when SRC is zero (and hence has no such bit)."
  (declare (xargs :guard (natp src)
                  :measure (nfix src)))
  (cond ((zp src)         0)
        ((logbitp 0 src)  0)
        (t                (+ 1 (bitscan-fwd (ash src -1))))))

(local (defthmd bitscan-fwd-examples
         ;; This is just to try to "validate the spec" by showing it produces the
         ;; values we want for some examples.
         (and
          ;; Some basic examples...
          (equal (bitscan-fwd #ub_0000_0000_0001) 0)
          (equal (bitscan-fwd #ub_0000_0000_0010) 1)
          (equal (bitscan-fwd #ub_0000_0000_0100) 2)
          (equal (bitscan-fwd #ub_0000_0000_1000) 3)
          (equal (bitscan-fwd #ub_0000_0001_0000) 4)
          (equal (bitscan-fwd #ub_0000_0010_0000) 5)
          (equal (bitscan-fwd #ub_0000_0100_0000) 6)
          ;; Same examples, but with upper bits changed to 1s...
          (equal (bitscan-fwd #ub_0100_0101_0001) 0)
          (equal (bitscan-fwd #ub_0110_0110_1010) 1)
          (equal (bitscan-fwd #ub_1010_0101_0100) 2)
          (equal (bitscan-fwd #ub_1010_1110_1000) 3)
          (equal (bitscan-fwd #ub_1111_1111_0000) 4)
          (equal (bitscan-fwd #ub_1010_1010_0000) 5)
          (equal (bitscan-fwd #ub_0011_1100_0000) 6))))

(defthm natp-of-bitscan-fwd
  (natp (bitscan-fwd src))
  :rule-classes :type-prescription)


(defund bitscan-rev (src)
  "(BITSCAN-REV SRC) returns the bit position of the most significant bit in
SRC that is set, or 0 when SRC is zero (and hence has no such bit)."
  (declare (xargs :guard (natp src)
                  :measure (nfix src)))
  (if (zp src)
      0
    (let ((next (ash src -1)))
      (if (= next 0)
          0
        (+ 1 (bitscan-rev next))))))

(local (defthmd bitscan-rev-examples
         ;; This is just to try to "validate the spec" by showing it produces the
         ;; values we want for some examples.
         (and
          ;; Some basic examples... just like bsf since only one bit is set
          (equal (bitscan-rev #ub_0000_0000_0001) 0)
          (equal (bitscan-rev #ub_0000_0000_0010) 1)
          (equal (bitscan-rev #ub_0000_0000_0100) 2)
          (equal (bitscan-rev #ub_0000_0000_1000) 3)
          (equal (bitscan-rev #ub_0000_0001_0000) 4)
          (equal (bitscan-rev #ub_0000_0010_0000) 5)
          (equal (bitscan-rev #ub_0000_0100_0000) 6)
          (equal (bitscan-rev #ub_0000_1000_0000) 7)
          (equal (bitscan-rev #ub_0001_0000_0000) 8)
          (equal (bitscan-rev #ub_0010_0000_0000) 9)
          (equal (bitscan-rev #ub_0100_0000_0000) 10)
          (equal (bitscan-rev #ub_1000_0000_0000) 11)
          ;; Same examples, but with some low bits flipped to one.
          (equal (bitscan-rev #ub_0000_0000_0001) 0)
          (equal (bitscan-rev #ub_0000_0000_0011) 1)
          (equal (bitscan-rev #ub_0000_0000_0101) 2)
          (equal (bitscan-rev #ub_0000_0000_1101) 3)
          (equal (bitscan-rev #ub_0000_0001_0101) 4)
          (equal (bitscan-rev #ub_0000_0011_0101) 5)
          (equal (bitscan-rev #ub_0000_0101_0111) 6)
          (equal (bitscan-rev #ub_0000_1101_1111) 7)
          (equal (bitscan-rev #ub_0001_1111_1111) 8)
          (equal (bitscan-rev #ub_0010_0100_0101) 9)
          (equal (bitscan-rev #ub_0101_0100_0001) 10)
          (equal (bitscan-rev #ub_1010_0101_0110) 11))))

(defthm natp-of-bitscan-rev
  (natp (bitscan-rev src))
  :rule-classes :type-prescription)

