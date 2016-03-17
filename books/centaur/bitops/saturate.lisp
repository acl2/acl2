; Centaur Bitops Library
; Copyright (C) 2010-2015 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "BITOPS")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "ash-bounds"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection bitops/saturate
  :parents (bitops)
  :short "Definitions of signed and unsigned saturation operations.")

(local (xdoc::set-default-parents bitops/saturate))

(defsection unsigned-saturate
  :short "@(call unsigned-saturate) coerces the integer @('x') into an
@('n')-bit unsigned integer by unsigned saturation."

  :long "<p>By unsigned saturation, we mean:</p>
<ul>
<li>If @('x') is too small (less than 0) it becomes 0.</li>
<li>If @('x') is too big (@('2^n') or more) it becomes @('2^n - 1').</li>
<li>Otherwise @('x') is unchanged.</li>
</ul>

<p>@('unsigned-saturate') is actually a macro.  Generally it expands into a
call of @('unsigned-saturate-fn').  But, in the common cases where @('n') is
explicitly 8, 16, 32, or 64, it instead expands into a call of an optimized,
inlined function.</p>

@(def unsigned-saturate)"

  (defmacro unsigned-saturate (n x)
    (cond ((eql n 8)   `(unsigned-saturate8 ,x))
          ((eql n 16)  `(unsigned-saturate16 ,x))
          ((eql n 32)  `(unsigned-saturate32 ,x))
          ((eql n 64)  `(unsigned-saturate64 ,x))
          (t           `(unsigned-saturate-fn ,n ,x)))))

(define unsigned-saturate-fn ((n posp)
                              (x integerp))
  :parents (unsigned-saturate)
  :returns (saturated natp :rule-classes :type-prescription)
  :short "Logical definition of @(see unsigned-saturate), and also its
executable implementation in the general case."
  (b* ((n   (lnfix n))
       (x   (lifix x))
       (2^n (ash 1 n))
       (max (+ -1 2^n))
       ((when (>= x max)) max)
       ((when (<= x 0)) 0))
    x)
  ///
  (defthm unsigned-byte-p-of-unsigned-saturate-fn
    (implies (natp n)
             (unsigned-byte-p n (unsigned-saturate-fn n x)))
    :hints(("Goal" :in-theory (enable expt-2-is-ash))))

  (defcong nat-equiv equal (unsigned-saturate-fn n x) 1)
  (defcong int-equiv equal (unsigned-saturate-fn n x) 2)

  (add-macro-alias unsigned-saturate unsigned-saturate-fn))

(local (in-theory (enable unsigned-saturate-fn)))

(define unsigned-saturate8 ((x integerp))
  :parents (unsigned-saturate)
  :short "Optimized implementation of 8-bit unsigned saturation."
  :inline t
  :enabled t
  (mbe :logic (unsigned-saturate-fn 8 x)
       :exec
       (cond ((>= x #ux_FF) #ux_FF)
             ((<= x 0)      0)
             (t             x))))

(define unsigned-saturate16 ((x integerp))
  :parents (unsigned-saturate)
  :short "Optimized implementation of 16-bit unsigned saturation."
  :inline t
  :enabled t
  (mbe :logic (unsigned-saturate-fn 16 x)
       :exec
       (cond ((>= x #ux_FFFF) #ux_FFFF)
             ((<= x 0)        0)
             (t               x))))

(define unsigned-saturate32 ((x integerp))
  :parents (unsigned-saturate)
  :short "Optimized implementation of 32-bit unsigned saturation."
  :inline t
  :enabled t
  (mbe :logic (unsigned-saturate-fn 32 x)
       :exec
       (cond ((>= x #ux_FFFF_FFFF) #ux_FFFF_FFFF)
             ((<= x 0)             0)
             (t                    x))))

(define unsigned-saturate64 ((x integerp))
  :parents (unsigned-saturate)
  :short "Optimized implementation of 64-bit unsigned saturation."
  :inline t
  :enabled t
  (mbe :logic (unsigned-saturate-fn 64 x)
       :exec
       (cond ((>= x #ux_FFFF_FFFF_FFFF_FFFF) #ux_FFFF_FFFF_FFFF_FFFF)
             ((<= x 0)                       0)
             (t                              x))))



(defsection signed-saturate
  :parents (bitops/saturate)
  :short "@(call signed-saturate) coerces the integer @('x') into an @('n')-bit
signed integer by signed saturation, then returns the result as an @('n')-bit
<b>unsigned</b> number."

  :long "<p>Normally signed saturation to @('n') bits is understood as:</p>

<ul>
<li>If @('x') is too small (less than @('-2^{n-1}')) it becomes @('-2^{n-1}').</li>
<li>If @('x') is too big (@('2^{n-1}') or more) it becomes @('2^{n-1} - 1').</li>
<li>Otherwise @('x') is unchanged.</li>
</ul>

<p>This is <b>almost</b> what we compute.  The twist is: after saturating as
above, we mask the above with @('2^{n-1}') to obtain an unsigned, @('n')-bit
result.</p>

<p>@('signed-saturate') is actually a macro.  Generally it expands into a call
of @('signed-saturate-fn').  But, in the common cases where @('n') is
explicitly 8, 16, 32, or 64, it instead expands into a call of an optimized,
inlined function.</p>

@(def signed-saturate)"

  (defmacro signed-saturate (n x)
    (cond ((eql n 8)   `(signed-saturate8 ,x))
          ((eql n 16)  `(signed-saturate16 ,x))
          ((eql n 32)  `(signed-saturate32 ,x))
          ((eql n 64)  `(signed-saturate64 ,x))
          (t           `(signed-saturate-fn ,n ,x)))))

(define signed-saturate-fn ((n posp)
                            (x integerp))
  :parents (signed-saturate)
  :returns (saturated natp :rule-classes :type-prescription)
  :short "Logical definition of @(see signed-saturate), and also its executable
implementation in the general case."
  (b* ((n       (lnfix n))
       (x       (lifix x))
       ((when (mbe :logic (zp n)
                   :exec nil))
        0)
       (2^{n-1} (ash 1 (1- n)))
       (max     (+ -1 2^{n-1}))
       ((when (>= x max))
        max)
       (min     (- 2^{n-1}))
       ((when (<= x min))
        2^{n-1})
       (mask    (+ -1 (ash 1 n))))
    (logand mask x))
  ///
  (local (defthm crock
           (implies (and (integerp n)
                         (< 0 n))
                    (< (ash 1 (+ -1 n)) (ash 1 n)))
           :rule-classes :linear))

  (local (include-book "ihs-extensions")) ;; bozo
  (defthm unsigned-byte-p-of-signed-saturate-fn
    (implies (natp n)
             (unsigned-byte-p n (signed-saturate-fn n x)))
    :hints(("Goal" :in-theory (e/d (expt-2-is-ash)
                                   (ash-1-removal)))))

  (defcong nat-equiv equal (signed-saturate-fn n x) 1)
  (defcong int-equiv equal (signed-saturate-fn n x) 2)

  (add-macro-alias signed-saturate signed-saturate-fn))

(local (in-theory (enable signed-saturate-fn)))

(define signed-saturate8 ((x integerp))
  :parents (signed-saturate)
  :short "Optimized implementation of 8-bit signed saturation."
  :inline t
  :enabled t
  (mbe :logic (signed-saturate-fn 8 x)
       :exec
       (cond ((>= x #ux_+7F) #ux_7F)
             ((<= x #ux_-80) #ux_80)
             (t
              (the (unsigned-byte 8)
                (logand (the (signed-byte 8) x) #ux_FF))))))

(define signed-saturate16 ((x integerp))
  :parents (signed-saturate)
  :short "Optimized implementation of 16-bit signed saturation."
  :inline t
  :enabled t
  (mbe :logic (signed-saturate-fn 16 x)
       :exec
       (cond ((>= x #ux_+7FFF) #ux_7FFF)
             ((<= x #ux_-8000) #ux_8000)
             (t (the (unsigned-byte 16)
                  (logand (the (signed-byte 16) x) #ux_FFFF))))))

(define signed-saturate32 ((x integerp))
  :parents (signed-saturate)
  :short "Optimized implementation of 32-bit signed saturation."
  :inline t
  :enabled t
  (mbe :logic (signed-saturate-fn 32 x)
       :exec
       (cond ((>= x #ux_+7FFF_FFFF) #ux_7FFF_FFFF)
             ((<= x #ux_-8000_0000) #ux_8000_0000)
             (t (the (unsigned-byte 32)
                  (logand (the (signed-byte 32) x) #ux_FFFF_FFFF))))))

(define signed-saturate64 ((x integerp))
  :parents (signed-saturate)
  :short "Optimized implementation of 64-bit signed saturation."
  :inline t
  :enabled t
  (mbe :logic (signed-saturate-fn 64 x)
       :exec
       (cond ((>= x #ux_+7FFF_FFFF_FFFF_FFFF) #ux_7FFF_FFFF_FFFF_FFFF)
             ((<= x #ux_-8000_0000_0000_0000) #ux_8000_0000_0000_0000)
             (t (the (unsigned-byte 64)
                  (logand (the (signed-byte 64) x) #ux_FFFF_FFFF_FFFF_FFFF))))))




#||

Basic timing tests...

;; UNOPTIMIZED: this is somewhat unfair because these don't get inlined...

(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 4 i)))    ;; 13.052 sec
(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 15 i)))   ;; 12.391 sec
(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 31 i)))   ;; 23.527 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 4 i)))  ;; 11.540 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 15 i))) ;; 11.542 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 31 i))) ;; 11.807 sec

;; OPTIMIZED:

(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 8 i)))    ;; 1.338 sec
(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 16 i)))   ;; 1.338 sec
(time (loop for i fixnum from 1 to 1000000000 do (signed-saturate 32 i)))   ;; 2.006 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 8 i)))  ;; 1.338 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 16 i))) ;; 1.338 sec
(time (loop for i fixnum from 1 to 1000000000 do (unsigned-saturate 32 i))) ;; 1.338 sec


;; 100x fewer tests due to bignums:

(time (loop for i fixnum from 1 to 10000000 do (signed-saturate 63 i)))  ;; 4.218 sec, 1.44 GB
(time (loop for i fixnum from 1 to 10000000 do (signed-saturate 64 i)))  ;; 0.356 sec, 0 bytes

(time (loop for i fixnum from 1 to 10000000 do (unsigned-saturate 63 i)))  ;; 1.264 sec, 640 MB
(time (loop for i fixnum from 1 to 10000000 do (unsigned-saturate 64 i)))  ;; 0.177 sec, 0 bytes

||#
