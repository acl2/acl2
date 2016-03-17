; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "signed-byte-p"))

(defsection bitops/extra-defs
  :parents (bitops)
  :short "Additional bitwise operations."
  :long "<p>This is just an ad-hoc collection of low-level bit operations,
mostly developed in support of specifying various integer and packed-integer
instructions.</p>")

(local (in-theory (enable* arith-equiv-forwarding)))


(define nth-slice2 ((n natp)
                    (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 2-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -2)) (1- (expt 2 2)))
       :exec
       (the (unsigned-byte 2)
         (logand (ash x (the (integer * 0) (* n -2))) #x3)))
  ///
  (defcong nat-equiv equal (nth-slice2 n x) 1)
  (defcong int-equiv equal (nth-slice2 n x) 2)
  (defthm unsigned-byte-p-2-of-nth-slice2
    (unsigned-byte-p 2 (nth-slice2 n x))))


(define nth-slice4 ((n natp)
                    (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 4-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -4)) (1- (expt 2 4)))
       :exec
       (the (unsigned-byte 4)
         (logand (ash x (the (integer * 0) (* n -4))) #xF)))
  ///
  (defcong nat-equiv equal (nth-slice4 n x) 1)
  (defcong int-equiv equal (nth-slice4 n x) 2)
  (defthm unsigned-byte-p-4-of-nth-slice4
    (unsigned-byte-p 4 (nth-slice4 n x))))



(define nth-slice8 ((n natp)
                    (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 8-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -8)) (1- (expt 2 8)))
       :exec
       (the (unsigned-byte 8)
         (logand (ash x (* n -8)) #xFF)))
  ///
  (defcong nat-equiv equal (nth-slice8 n x) 1)
  (defcong int-equiv equal (nth-slice8 n x) 2)
  (defthm unsigned-byte-p-8-of-nth-slice8
    (unsigned-byte-p 8 (nth-slice8 n x))))


(define nth-slice16 ((n natp)
                     (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 16-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -16)) (1- (expt 2 16)))
       :exec
       (the (unsigned-byte 16)
         (logand (ash x (* n -16)) #xFFFF)))
  ///
  (defcong nat-equiv equal (nth-slice16 n x) 1)
  (defcong int-equiv equal (nth-slice16 n x) 2)
  (defthm unsigned-byte-p-16-of-nth-slice16
    (unsigned-byte-p 16 (nth-slice16 n x))))


(define nth-slice32 ((n natp)
                     (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 32-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -32)) (1- (expt 2 32)))
       :exec
       (the (unsigned-byte 32)
         (logand (ash x (* n -32)) #ux_FFFF_FFFF)))
  ///
  (defcong nat-equiv equal (nth-slice32 n x) 1)
  (defcong int-equiv equal (nth-slice32 n x) 2)
  (defthm unsigned-byte-p-32-of-nth-slice32
    (unsigned-byte-p 32 (nth-slice32 n x))))


(define nth-slice64 ((n natp)
                     (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 64-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -64)) (1- (expt 2 64)))
       :exec
       (the (unsigned-byte 64)
         (logand (ash x (* n -64)) #ux_FFFF_FFFF_FFFF_FFFF)))
  ///
  (defcong nat-equiv equal (nth-slice64 n x) 1)
  (defcong int-equiv equal (nth-slice64 n x) 2)
  (defthm unsigned-byte-p-64-of-nth-slice64
    (unsigned-byte-p 64 (nth-slice64 n x))))


(define nth-slice128 ((n natp)
                      (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 128-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -128)) (1- (expt 2 128)))
       :exec
       (the (unsigned-byte 128)
         (logand (ash x (* n -128))
                 #ux_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF)))
  ///
  (defcong nat-equiv equal (nth-slice128 n x) 1)
  (defcong int-equiv equal (nth-slice128 n x) 2)
  (defthm unsigned-byte-p-128-of-nth-slice128
    (unsigned-byte-p 128 (nth-slice128 n x))))


(define nth-slice256 ((n natp)
                      (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 256-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -256)) (1- (expt 2 256)))
       :exec
       (the (unsigned-byte 256)
         (logand (ash x (* n -256))
                 #ux_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF)))
  ///
  (defcong nat-equiv equal (nth-slice256 n x) 1)
  (defcong int-equiv equal (nth-slice256 n x) 2)
  (defthm unsigned-byte-p-256-of-nth-slice256
    (unsigned-byte-p 256 (nth-slice256 n x))))


(define nth-slice512 ((n natp)
                      (x integerp))
  :returns (slice natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Extract the @('n')th 512-bit slice of the integer @('x')."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  :inline t
  (mbe :logic
       (logand (ash (ifix x) (* (nfix n) -512)) (1- (expt 2 512)))
       :exec
       (the (unsigned-byte 512)
         (logand (ash x (* n -512))
                 #ux_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF)))
  ///
  (defcong nat-equiv equal (nth-slice512 n x) 1)
  (defcong int-equiv equal (nth-slice512 n x) 2)
  (defthm unsigned-byte-p-512-of-nth-slice512
    (unsigned-byte-p 512 (nth-slice512 n x))))



(define negate-slice8 ((x :type (unsigned-byte 8)))
  :returns (~x natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call negate-slice8) computes the 8-bit two's complement negation of
@('x') and returns it as an 8-bit natural."
  :long "<p>For example, @('(negate-slice8 3) = 253').</p>
<p>We leave this enabled; we would usually not expect to try to reason about
it.</p>"
  :inline t
  :enabled t
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 8)))
       :exec
       (the (unsigned-byte 8)
         (logand (the (signed-byte 9)
                   (+ 1 (the (signed-byte 9) (lognot x))))
                 #xFF)))
  ///
  (defcong nat-equiv equal (negate-slice8 x) 1)
  (defthm unsigned-byte-p-8-of-negate-slice8
    (unsigned-byte-p 8 (negate-slice8 x))))


(define negate-slice16 ((x :type (unsigned-byte 16)))
  :returns (~x natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call negate-slice16) computes the 16-bit two's complement negation
of @('x') and returns it as an 16-bit natural."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :inline t
  :enabled t
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 16)))
       :exec
       (the (unsigned-byte 16)
         (logand (the (signed-byte 17)
                   (+ 1 (the (signed-byte 17) (lognot x))))
                 #xFFFF)))
  ///
  (defcong nat-equiv equal (negate-slice16 x) 1)
  (defthm unsigned-byte-p-16-of-negate-slice16
    (unsigned-byte-p 16 (negate-slice16 x))))


(define negate-slice32 ((x :type (unsigned-byte 32)))
  :returns (~x natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call negate-slice32) computes the 32-bit two's complement negation
of @('x') and returns it as an 32-bit natural."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :inline t
  :enabled t
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 32)))
       :exec
       (the (unsigned-byte 32)
         (logand (the (signed-byte 33)
                   (+ 1 (the (signed-byte 33) (lognot x))))
                 #ux_FFFF_FFFF)))
  ///
  (defcong nat-equiv equal (negate-slice32 x) 1)
  (defthm unsigned-byte-p-32-of-negate-slice32
    (unsigned-byte-p 32 (negate-slice32 x))))


(define negate-slice64 ((x :type (unsigned-byte 64)))
  :returns (~x natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call negate-slice64) computes the 64-bit two's complement negation
of @('x') and returns it as an 64-bit natural."
  :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
  :enabled t
  (mbe :logic
       (logand (+ 1 (lognot (nfix x))) (1- (expt 2 64)))
       :exec
       (the (unsigned-byte 64)
         (logand (the (signed-byte 65)
                   (+ 1 (the (signed-byte 65) (lognot x))))
                 #ux_FFFF_FFFF_FFFF_FFFF)))
  ///
  (defcong nat-equiv equal (negate-slice64 x) 1)
  (defthm unsigned-byte-p-64-of-negate-slice64
    (unsigned-byte-p 64 (negate-slice64 x))))



(define abs-diff ((a integerp)
                  (b integerp))
  :returns (ans natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call abs-diff) is just @('(abs (- (ifix a) (ifix b)))'), but
optimized for @(see gl::gl)."

  :long "<p>@('abs-diff') is similar to @('(abs (- a b))') but has better
performance for symbolic simulations with GL: it decides whether the
subtraction will be necessary by looking at the arguments, which tend to be
simple and perhaps nicely interleaved, instead of by looking at the result,
which tend to be complex since they are the combined arguments.</p>

<p>For an @('aig-cert-mode') proof of the 64-bit @('PSADBW') instruction, using
@('abs-diff') instead of @('(abs (- a b))') reduced the proof time from 56.2
seconds to 37.44 seconds.</p>

<p>We disable this function, but we leave enabled the following theorem:</p>

@(thm abs-diff-correct)

<p>We therefore would not expect to ever need to reason about @('abs-diff')
directly.</p>"

  (mbe :logic
       ;; Don't be tempted to change the :logic definition to (abs (- (ifix a)
       ;; (ifix b))).  GL uses :logic definitions!
       (let ((a (ifix a))
             (b (ifix b)))
         (if (<= b a)
             (- a b)
           (- b a)))
       :exec
       (if (<= b a)
           (- a b)
         (- b a)))
  ///
  (defthm abs-diff-correct
    (equal (abs-diff a b)
           (abs (- (ifix a) (ifix b))))))


(define setbit ((n natp     "Bit position to set to 1.")
                (x integerp "Starting value."))
  :returns (ans integerp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Set X[n] := 1"
  :enabled t
  (let ((n (lnfix n))
        (x (lifix x)))
    (logior (ash 1 n) x))
  ///
  (defcong nat-equiv equal (setbit n x) 1)
  (defcong int-equiv equal (setbit n x) 2))


(define clearbit ((n natp     "Bit position to clear to 0.")
                  (x integerp "Starting value."))
  :returns (ans integerp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Set X[n] := 0"
  :enabled t
  (let ((n (lnfix n))
        (x (lifix x)))
    (logand (lognot (ash 1 n)) x))
  ///
  (defcong nat-equiv equal (clearbit n x) 1)
  (defcong int-equiv equal (clearbit n x) 2))


(define copybit ((n    natp     "Bit position to copy.")
                 (from integerp)
                 (to   integerp))
  :returns (ans integerp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Set To[n] := From[n]"
  :enabled t
  (if (logbitp n from)
      (setbit n to)
    (clearbit n to))
  ///
  (defcong nat-equiv equal (copybit n x y) 1)
  (defcong int-equiv equal (copybit n x y) 2)
  (defcong int-equiv equal (copybit n x y) 3))


(define notbit ((n natp     "Bit position to negate.")
                (x integerp "Starting value."))
  :returns (ans integerp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "Set X[n] := ~X[n]"
  :enabled t
  (if (logbitp n x)
      (clearbit n x)
    (setbit n x))
  ///
  (defcong nat-equiv equal (notbit n x) 1)
  (defcong int-equiv equal (notbit n x) 2))


(local
 (defthm shift-right-smaller
   (implies (not (zp src))
            (< (logtail 1 src) src))
   :hints(("Goal" :in-theory (e/d (logtail**))))))

(define bitscan-fwd ((src natp))
  :returns (position natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call bitscan-fwd) returns the bit position of the least significant
bit in @('src') that is set, or 0 when @('src') is zero (and hence has no such
bit)."
  :long "<p>Examples:</p>
@({
     (bitscan-fwd #b1001) = 0
     (bitscan-fwd #b1010) = 1
     (bitscan-fwd #b1100) = 2
     (bitscan-fwd #b1000) = 3
})"
  (cond ((zp src)         0)
        ((logbitp 0 src)  0)
        (t                (+ 1 (bitscan-fwd (ash src -1)))))
  ///
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

  (defcong nat-equiv equal (bitscan-fwd src) 1))


(define bitscan-rev ((src natp))
  :returns (position natp :rule-classes :type-prescription)
  :parents (bitops/extra-defs)
  :short "@(call bitscan-rev) returns the bit position of the most significant
bit in @('src') that is set, or 0 when @('src') is zero (and hence has no such
bit)."
  :long "<p>Examples:</p>
@({
    (bitscan-rev #b0001) = 0
    (bitscan-rev #b0011) = 1
    (bitscan-rev #b0101) = 2
    (bitscan-rev #b1001) = 3
})"

  (if (zp src)
      0
    (let ((next (ash src -1)))
      (if (= next 0)
          0
        (+ 1 (bitscan-rev next)))))
  ///
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

  (defcong nat-equiv equal (bitscan-rev src) 1))


