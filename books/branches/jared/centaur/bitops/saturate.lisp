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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "ash-bounds"))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defsection unsigned-saturate
  :parents (bitops)
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
inlined function.</p>"

  (defund unsigned-saturate-fn (n x)
    (declare (xargs :guard (and (posp n)
                                (integerp x))))
    (b* ((n       (lnfix n))
         (x       (lifix x))
         (2^n     (ash 1 n))
         (max     (+ -1 2^n))
         ((when (>= x max))
          max)
         ((when (<= x 0))
          0))
      x))

  (local (in-theory (enable unsigned-saturate-fn)))

  (defthm natp-of-unsigned-saturate-fn
    (natp (unsigned-saturate-fn n x))
    :rule-classes :type-prescription)

  (defthm unsigned-byte-p-of-unsigned-saturate-fn
    (implies (natp n)
             (unsigned-byte-p n (unsigned-saturate-fn n x)))
    :hints(("Goal" :in-theory (enable expt-2-is-ash))))

  (defcong nat-equiv equal (unsigned-saturate-fn n x) 1)
  (defcong int-equiv equal (unsigned-saturate-fn n x) 2)


  (definline unsigned-saturate8 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (unsigned-saturate-fn 8 x)
         :exec
         (cond ((>= x #ux_FF) #ux_FF)
               ((<= x 0)      0)
               (t             x))))

  (definline unsigned-saturate16 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (unsigned-saturate-fn 16 x)
         :exec
         (cond ((>= x #ux_FFFF) #ux_FFFF)
               ((<= x 0)        0)
               (t               x))))

  (definline unsigned-saturate32 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (unsigned-saturate-fn 32 x)
         :exec
         (cond ((>= x #ux_FFFF_FFFF) #ux_FFFF_FFFF)
               ((<= x 0)             0)
               (t                    x))))

  (definline unsigned-saturate64 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (unsigned-saturate-fn 64 x)
         :exec
         (cond ((>= x #ux_FFFF_FFFF_FFFF_FFFF) #ux_FFFF_FFFF_FFFF_FFFF)
               ((<= x 0)                       0)
               (t                              x))))

  (defmacro unsigned-saturate (n x)
    (cond ((eql n 8)   `(unsigned-saturate8 ,x))
          ((eql n 16)  `(unsigned-saturate16 ,x))
          ((eql n 32)  `(unsigned-saturate32 ,x))
          ((eql n 64)  `(unsigned-saturate64 ,x))
          (t           `(unsigned-saturate-fn ,n ,x))))

  (add-macro-alias unsigned-saturate unsigned-saturate-fn))



(defsection signed-saturate
  :parents (bitops)
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
inlined function.</p>"

  (defund signed-saturate-fn (n x)
    (declare (xargs :guard (and (posp n)
                                (integerp x))))
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
      (logand mask x)))

  (local (in-theory (enable signed-saturate-fn)))

  (defthm natp-of-signed-saturate-fn
    (natp (signed-saturate-fn n x))
    :rule-classes :type-prescription)

  (local (defthm crock
           (implies (and (integerp n)
                         (< 0 n))
                    (< (ash 1 (+ -1 n)) (ash 1 n)))
           :rule-classes :linear))

  (defthm unsigned-byte-p-of-signed-saturate-fn
    (implies (natp n)
             (unsigned-byte-p n (signed-saturate-fn n x)))
    :hints(("Goal" :in-theory (enable expt-2-is-ash))))

  (defcong nat-equiv equal (signed-saturate-fn n x) 1)
  (defcong int-equiv equal (signed-saturate-fn n x) 2)



  (definline signed-saturate8 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (signed-saturate-fn 8 x)
         :exec
         (cond ((>= x #ux_+7F) #ux_7F)
               ((<= x #ux_-80) #ux_80)
               (t
                (the (unsigned-byte 8)
                  (logand (the (signed-byte 8) x) #ux_FF))))))

  (definline signed-saturate16 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (signed-saturate-fn 16 x)
         :exec
         (cond ((>= x #ux_+7FFF) #ux_7FFF)
               ((<= x #ux_-8000) #ux_8000)
               (t (the (unsigned-byte 16)
                    (logand (the (signed-byte 16) x) #ux_FFFF))))))

  (definline signed-saturate32 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (signed-saturate-fn 32 x)
         :exec
         (cond ((>= x #ux_+7FFF_FFFF) #ux_7FFF_FFFF)
               ((<= x #ux_-8000_0000) #ux_8000_0000)
               (t (the (unsigned-byte 32)
                    (logand (the (signed-byte 32) x) #ux_FFFF_FFFF))))))

  (definline signed-saturate64 (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (signed-saturate-fn 64 x)
         :exec
         (cond ((>= x #ux_+7FFF_FFFF_FFFF_FFFF) #ux_7FFF_FFFF_FFFF_FFFF)
               ((<= x #ux_-8000_0000_0000_0000) #ux_8000_0000_0000_0000)
               (t (the (unsigned-byte 64)
                    (logand (the (signed-byte 64) x) #ux_FFFF_FFFF_FFFF_FFFF))))))

  (defmacro signed-saturate (n x)
    (cond ((eql n 8)   `(signed-saturate8 ,x))
          ((eql n 16)  `(signed-saturate16 ,x))
          ((eql n 32)  `(signed-saturate32 ,x))
          ((eql n 64)  `(signed-saturate64 ,x))
          (t           `(signed-saturate-fn ,n ,x))))

  (add-macro-alias signed-saturate signed-saturate-fn))



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
