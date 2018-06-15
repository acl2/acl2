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
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "std/util/defrule" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "centaur/gl/gl-mbe" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "equal-by-logbitp"))
(local (include-book "ihs/quotient-remainder-lemmas" :Dir :system))
(local (in-theory (disable (force))))
(local (in-theory (enable* arith-equiv-forwarding)))
(local (acl2::enable-wizard))

(defsection bitops/rotate
  :parents (bitops)
  :short "Definitions of @(see rotate-left) and @(see rotate-right) operations,
and lemmas for reasoning about them.")

(local (xdoc::set-default-parents bitops/rotate))


(local (defthm mod-0
         (equal (mod 0 x)
                0)
         :hints(("Goal" :in-theory (enable mod floor)))))

(local (defthm rem-is-mod
         ;; (let ((places 20)
         ;;       (width 4))
         ;;   ;; REM finishes in 2.4 seconds, MOD in 2.8 seconds...
         ;;   (time (loop for i fixnum from 1 to 100000000 do
         ;;               (mod places width)))
         ;;   (time (loop for i fixnum from 1 to 100000000 do
         ;;               (rem places width))))
         (implies (and (natp places)
                       (natp width))
                  (equal (rem places width)
                         (mod places width)))
         :hints(("Goal" :in-theory (enable mod rem)))))


(define rotate-left
  ((x      integerp "The bit vector to be rotated left.")
   (width  posp     "The width of @('x').")
   (places natp     "The number of places to rotate left."))
  :returns (rotated natp :rule-classes :type-prescription)
  :short "Rotate a bit-vector some arbitrary number of places to the left."
  :long "<p>Note that @('places') can be larger than @('width').  We
automatically reduce the number of places modulo the width, which makes sense
since rotating @('width')-many times is the same as not rotating at all.</p>"

  ;; Running example to help understand the code.  Suppose X is some 16-bit
  ;; number, say 16'b AAAA_BBBB_CCCC_DDDD, so the width is 16, and suppose we
  ;; want to rotate left by 20 places.

  (let* ((width      (lnfix width))
         (places     (lnfix places))
         (wmask      (1- (ash 1 width)))
         (x          (logand x wmask))                ; chop x down to size
         (places     (mbe :logic (mod places width) ; e.g., 20 places --> 4 places
                          :exec
                          ;; REM is slightly cheaper than MOD, but in many
                          ;; cases we can probably avoid REM entirely because
                          ;; usually we'll be rotating by some amount less
                          ;; than the width...
                          (if (< places width)
                              places
                            (rem places width))))
         (places     (gl::gl-mbe places ;; logically this is a no-op
                                 ;; ensure that GL knows places is short
                                 (logand places (lognot (ash -1
                                                             (integer-length
                                                              width))))))
         (low-num    (- width places))              ; e.g., 12
         (mask       (1- (ash 1 low-num)))          ; e.g., 0000_1111_1111_1111
         (xl         (logand x mask))               ; e.g., 0000_BBBB_CCCC_DDDD
         (xh         (logand x (lognot mask)))      ; e.g., AAAA_0000_0000_0000
         (xh-shift   (ash xh (- low-num)))          ; e.g., 0000_0000_0000_AAAA
         (xl-shift   (ash xl places))               ; e.g., BBBB_CCCC_DDDD_0000
         (ans        (logior xl-shift xh-shift)))   ; e.g., BBBB_CCCC_DDDD_AAAA
    ans)
  ///
  (defcong int-equiv equal (rotate-left x width places) 1)
  (defcong nat-equiv equal (rotate-left x width places) 2)
  (defcong nat-equiv equal (rotate-left x width places) 3)

  (local (defthm rotate-left-examples
           (and (equal (rotate-left #b11110000 8 0) #b11110000)
                (equal (rotate-left #b11110000 8 1) #b11100001)
                (equal (rotate-left #b11110000 8 2) #b11000011)
                (equal (rotate-left #b11110000 8 3) #b10000111)
                (equal (rotate-left #b11110000 8 4) #b00001111)
                (equal (rotate-left #b11110000 8 5) #b00011110)
                (equal (rotate-left #b11110000 8 6) #b00111100)
                (equal (rotate-left #b11110000 8 7) #b01111000)
                (equal (rotate-left #b11110000 8 8) #b11110000)
                (equal (rotate-left #b11110000 8 9)  #b11100001)
                (equal (rotate-left #b11110000 8 10) #b11000011)
                (equal (rotate-left #b11110000 8 11) #b10000111)
                (equal (rotate-left #b11110000 8 12) #b00001111)
                (equal (rotate-left #b11110000 8 13) #b00011110)
                (equal (rotate-left #b11110000 8 14) #b00111100)
                (equal (rotate-left #b11110000 8 15) #b01111000)
                (equal (rotate-left #b11110000 8 16) #b11110000)

                (equal (rotate-left #b1111000011001010 16 0)   #b1111000011001010)
                (equal (rotate-left #b1111000011001010 16 1)   #b1110000110010101)
                (equal (rotate-left #b1111000011001010 16 2)   #b1100001100101011)
                (equal (rotate-left #b1111000011001010 16 3)   #b1000011001010111)
                (equal (rotate-left #b1111000011001010 16 4)   #b0000110010101111)
                (equal (rotate-left #b1111000011001010 16 5)   #b0001100101011110)
                (equal (rotate-left #b1111000011001010 16 6)   #b0011001010111100)
                (equal (rotate-left #b1111000011001010 16 7)   #b0110010101111000)
                (equal (rotate-left #b1111000011001010 16 8)   #b1100101011110000)
                (equal (rotate-left #b1111000011001010 16 9)   #b1001010111100001)
                (equal (rotate-left #b1111000011001010 16 10)  #b0010101111000011)
                (equal (rotate-left #b1111000011001010 16 11)  #b0101011110000110)
                (equal (rotate-left #b1111000011001010 16 12)  #b1010111100001100)
                (equal (rotate-left #b1111000011001010 16 13)  #b0101111000011001)
                (equal (rotate-left #b1111000011001010 16 14)  #b1011110000110010)
                (equal (rotate-left #b1111000011001010 16 15)  #b0111100001100101)
                (equal (rotate-left #b1111000011001010 16 16)  #b1111000011001010))
           :rule-classes nil))

  (local (defthm logbitp-of-rotate-left-1
           (implies (and (>= n width)
                         (natp n)
                         (natp width))
                    (equal (logbitp n (rotate-left x width places))
                           nil))
           :hints(("Goal" :in-theory (enable ;b-ior b-and
                                      logbitp-of-ash-split
                                      logbitp-of-loghead-split)))))

  (local (defthm logbitp-of-rotate-left-2
           (implies (and (< n width)
                         (>= n (mod places width))
                         (natp n)
                         (natp places)
                         (natp width))
                    (equal (logbitp n (rotate-left x width places))
                           (logbitp (- n (mod places width)) x)))))

  (local (defthm logbitp-of-rotate-left-3
           (implies (and (< n width)
                         (< n (mod places width))
                         (natp n)
                         (natp places)
                         (natp width))
                    (equal (logbitp n (rotate-left x width places))
                           (logbitp (+ n width (- (mod places width))) x)))))

  (defthmd logbitp-of-rotate-left-split
    (equal (logbitp n (rotate-left x width places))
           (b* ((n      (nfix n))
                (width  (nfix width))
                (places (mod (nfix places) width)))
             (cond ((>= n width)
                    nil)
                   ((>= n places)
                    (logbitp (- n places) x))
                   (t
                    (logbitp (+ n width (- places)) x)))))
    :hints(("Goal" :in-theory (e/d (nfix) (rotate-left)))))

  (local (in-theory (disable max)))

  (defthm rotate-left-zero-width
    (equal (rotate-left x 0 places) 0))

  (defthm rotate-left-by-zero
    (equal (rotate-left x width 0)
           (loghead width x))
    :hints ((equal-by-logbitp-hint)
            (and stable-under-simplificationp
                 '(:in-theory (enable logbitp-of-loghead-split
                                      logbitp-of-ash-split)))))

  (defthm rotate-left-by-width
    (equal (rotate-left x width width)
           (loghead width x))
    :hints(("Goal" :in-theory (enable logbitp-of-rotate-left-split
                                      logbitp-of-loghead-split))
           (equal-by-logbitp-hint))))



(define rotate-left-1
  ((x      integerp "The bit vector to be rotated left.")
   (width  posp     "The width of @('x')."))
  :returns (rotated natp :rule-classes :type-prescription)
  :short "Rotate a bit-vector by a single place to the left."

  (b* (((when (mbe :logic (zp width) :exec nil))
        0)
       (msb   (logbit  (- width 1) x))
       (chop  (loghead (- width 1) x)))
    (logcons msb chop))

  ///
  (defcong int-equiv equal (rotate-left-1 x width) 1)
  (defcong nat-equiv equal (rotate-left-1 x width) 2)

  (defthmd logbitp-of-rotate-left-1-split
    (equal (logbitp n (rotate-left-1 x width))
           (b* ((n      (nfix n))
                (width  (nfix width)))
             (cond ((>= n width) nil)
                   ((equal n 0)  (logbitp (+ -1 width) x))
                   (t            (logbitp (+ -1 n) x)))))
    :hints(("Goal" :in-theory (enable logbitp-of-loghead-split))))

  (defthm unsigned-byte-p-of-rotate-left-1
    (implies (natp width)
             (unsigned-byte-p width (rotate-left-1 x width)))
    :hints(("Goal"
            :in-theory (e/d* (ihsext-recursive-redefs)
                             (unsigned-byte-p))))))



(defsection case-split-mod-of-decrement

  (local (in-theory (disable acl2::mod-=-0)))

  (local (defthm lalala
           (implies (and (syntaxp (quotep c))
                         (natp n)
                         (natp m)
                         (integerp g3)
                         (equal c (- m n))
                         (< m n))
                    (equal (equal (mod (+ c g3) n) m)
                           (equal (mod g3 n) 0)))
           :hints(("Goal" :in-theory (e/d (mod) ((force)))))))

  (local (defthm case-split-mod-of-decrement-l0
           (implies (and (natp n)
                         (integerp a)
                         (equal (mod a n) 0))
                    (equal (mod (+ -1 a) n)
                           (- n 1)))
           :hints(("goal" :use ((:instance ACL2::CANCEL-MOD-+-BASIC
                                           (acl2::x n)
                                           (acl2::y (+ 1 a))
                                           (acl2::z n)))))))

  (local (defthm case-split-mod-of-decrement-l1
           (implies (and (natp n)
                         (integerp a)
                         (not (equal (mod a n) 0)))
                    (equal (mod (+ -1 a) n)
                           (- (mod a n) 1)))
           :hints(("goal" :in-theory (e/d (mod))))))

  (defthmd case-split-mod-of-decrement
    (implies (and (natp n)
                  (integerp a))
             (equal (mod (+ -1 a) n)
                    (if (equal (mod a n) 0)
                        (- n 1)
                      (- (mod a n) 1))))
    :hints(("Goal"
            :use ((:instance case-split-mod-of-decrement-l0)
                  (:instance case-split-mod-of-decrement-l1))))))


(defsection rotate-left**
  :parents (bitops/rotate rotate-left)
  :short "Alternate, recursive definitions of @(see rotate-left)."
  :long "<p>Here are both tail-recursive and non tail-recursive versions of
@(see rotate-left).  These rules are disabled by default and must be explicitly
enabled when you want to use them.</p>"

  (local (in-theory (e/d (case-split-mod-of-decrement)
                         (max natp nfix ifix acl2::floor-mod-elim))))

  (local (defthm integerp-of-/-when-posp
           (implies (posp width)
                    (equal (integerp (/ width))
                           (equal width 1)))
           :hints(("Goal"
                   :in-theory (disable inverse-of-*
                                       acl2::equal-*-/-2)
                   :use ((:instance inverse-of-* (x width)))
                   :nonlinearp t))))

  (defthmd rotate-left**
    (equal (rotate-left x width places)
           (if (zp places)
               (loghead width x)
             (rotate-left-1 (rotate-left x width (- places 1))
                            width)))
    :rule-classes ((:definition
                    :clique (rotate-left)
                    :controller-alist
                    ((rotate-left nil nil t))))
    :hints((equal-by-logbitp-hint)
           (and stable-under-simplificationp
                '(:in-theory (e/d (logbitp-of-rotate-left-1-split
                                   logbitp-of-rotate-left-split))))))

  (defthmd rotate-left**-tr
    (equal (rotate-left x width places)
           (if (zp places)
               (loghead width x)
             (rotate-left (rotate-left-1 x width)
                          width
                          (- places 1))))
    :rule-classes ((:definition
                    :clique (rotate-left)
                    :controller-alist
                    ((rotate-left nil nil t))))
    :hints((equal-by-logbitp-hint)
           (and stable-under-simplificationp
                '(:in-theory (e/d (logbitp-of-rotate-left-1-split
                                   logbitp-of-rotate-left-split)))))))


(defsection rotate-left-extra
  :extension (rotate-left)

  (local (include-book "std/basic/inductions" :dir :system))

  (defrule unsigned-byte-p-of-rotate-left
    (implies (natp width)
             (unsigned-byte-p width (rotate-left x width places)))
    :induct (acl2::dec-induct places)
    :enable rotate-left**
    :disable unsigned-byte-p)

  (defrule rotate-left-of-rotate-left
    (equal (rotate-left (rotate-left x width places1) width places2)
           (rotate-left x width (+ (nfix places1) (nfix places2))))
    :induct (acl2::dec-induct places2)
    :in-theory (e/d (rotate-left**) (loghead))
    :hints (("Subgoal *1/1" :cases ((natp width))))))



(define rotate-right
  ((x      integerp "The bit vector to be rotated right.")
   (width  posp     "The width of @('x').")
   (places natp     "The number of places to rotate right."))
  :returns (rotated natp :rule-classes :type-prescription)
  :short "Rotate a bit-vector some arbitrary number of places to the right."
  :long "<p>Note that @('places') can be larger than @('width').  We
automatically reduce the number of places modulo the width, which makes sense
since rotating @('width')-many times is the same as not rotating at all.</p>"

  :prepwork
  ((local (defthm loghead-removal-backwards
            ;; BOZO should really fix loghead's definition instead...
            (implies (natp width)
                     (equal (logand x (+ -1 (ash 1 width)))
                            (loghead width x)))
            :hints((equal-by-logbitp-hint)
                   (and stable-under-simplificationp
                        '(:in-theory (enable b-and bool->bit
                                             logbitp-of-loghead-split)))))))

  ;; Running example to help understand the code: suppose X is some 16-bit
  ;; number, say 16'b AAAA_BBBB_CCCC_DDDD, so the width is 16, and suppose we
  ;; want to rotate by 20 places.

  (let* ((width      (lnfix width))
         (x          (mbe :logic (loghead width x)
                          :exec (logand x (+ -1 (ash 1 width)))))
         (places     (lnfix places))
         (places     (mbe :logic (mod places width) ; e.g., 20 places --> 4 places
                          :exec
                          ;; As in rotate-left
                          (if (< places width)
                              places
                            (rem places width))))
         (mask       (1- (ash 1 places)))           ; e.g., 0000_0000_0000_1111
         (xl         (logand x mask))               ; e.g., 0000_0000_0000_DDDD
         (xh-shift   (ash x (- places)))            ; e.g., 0000_AAAA_BBBB_CCCC
         (high-num   (- width places))              ; e.g., 12
         (xl-shift   (ash xl high-num))             ; e.g., DDDD_0000_0000_0000
         (ans        (logior xl-shift xh-shift)))   ; e.g., DDDD_AAAA_BBBB_CCCC
    ans)
  ///
  (defcong int-equiv equal (rotate-right x width places) 1)
  (defcong nat-equiv equal (rotate-right x width places) 2)
  (defcong nat-equiv equal (rotate-right x width places) 3)

  (local (defthm rotate-right-examples
           (and (equal (rotate-right #b11110000 8 0)  #b11110000)
                (equal (rotate-right #b11110000 8 1)  #b01111000)
                (equal (rotate-right #b11110000 8 2)  #b00111100)
                (equal (rotate-right #b11110000 8 3)  #b00011110)
                (equal (rotate-right #b11110000 8 4)  #b00001111)
                (equal (rotate-right #b11110000 8 5)  #b10000111)
                (equal (rotate-right #b11110000 8 6)  #b11000011)
                (equal (rotate-right #b11110000 8 7)  #b11100001)
                (equal (rotate-right #b11110000 8 8)  #b11110000)
                (equal (rotate-right #b11110000 8 9)  #b01111000)
                (equal (rotate-right #b11110000 8 10) #b00111100)
                (equal (rotate-right #b11110000 8 11) #b00011110)
                (equal (rotate-right #b11110000 8 12) #b00001111)
                (equal (rotate-right #b11110000 8 13) #b10000111)
                (equal (rotate-right #b11110000 8 14) #b11000011)
                (equal (rotate-right #b11110000 8 15) #b11100001)

                (equal (rotate-right #b1111000011001010 16 0)   #b1111000011001010)
                (equal (rotate-right #b1111000011001010 16 1)   #b0111100001100101)
                (equal (rotate-right #b1111000011001010 16 2)   #b1011110000110010)
                (equal (rotate-right #b1111000011001010 16 3)   #b0101111000011001)
                (equal (rotate-right #b1111000011001010 16 4)   #b1010111100001100)
                (equal (rotate-right #b1111000011001010 16 5)   #b0101011110000110)
                (equal (rotate-right #b1111000011001010 16 6)   #b0010101111000011)
                (equal (rotate-right #b1111000011001010 16 7)   #b1001010111100001)
                (equal (rotate-right #b1111000011001010 16 8)   #b1100101011110000)
                (equal (rotate-right #b1111000011001010 16 9)   #b0110010101111000)
                (equal (rotate-right #b1111000011001010 16 10)  #b0011001010111100)
                (equal (rotate-right #b1111000011001010 16 11)  #b0001100101011110)
                (equal (rotate-right #b1111000011001010 16 12)  #b0000110010101111)
                (equal (rotate-right #b1111000011001010 16 13)  #b1000011001010111)
                (equal (rotate-right #b1111000011001010 16 14)  #b1100001100101011)
                (equal (rotate-right #b1111000011001010 16 15)  #b1110000110010101)
                (equal (rotate-right #b1111000011001010 16 16)  #b1111000011001010))
           :rule-classes nil))

  (local (defthm logbitp-of-rotate-right-1
           (implies (and (>= n width)
                         (natp n)
                         (natp width))
                    (equal (logbitp n (rotate-right x width places))
                           nil))
           :hints(("Goal" :in-theory (enable logbitp-of-ash-split
                                             logbitp-of-loghead-split)))))

  (local (defthm logbitp-of-rotate-right-2
           (implies (and (< n (- width (mod places width)))
                         (natp n)
                         (natp places)
                         (natp width))
                    (equal (logbitp n (rotate-right x width places))
                           (logbitp (+ n (mod places width)) x)))))

  (local (defthm logbitp-of-rotate-right-3
           (implies (and (< n width)
                         (>= n (- width (mod places width)))
                         (natp n)
                         (natp places)
                         (natp width))
                    (equal (logbitp n (rotate-right x width places))
                           (logbitp (+ n (mod places width) (- width)) x)))))

  (defthmd logbitp-of-rotate-right-split
    (let ((lhs (logbitp n (rotate-right x width places))))
      (equal lhs
             (b* ((n      (nfix n))
                  (width  (nfix width))
                  (places (mod (nfix places) width)))
               (cond ((>= n width)
                      nil)
                     ((>= n (- width places))
                      (logbitp (+ n places (- width)) x))
                     (t
                      (logbitp (+ n places) x))))))
    :hints(("Goal" :in-theory (e/d (nfix) (rotate-right)))))

  (local (in-theory (disable max)))

  (defthm rotate-right-zero-width
    (equal (rotate-right x 0 places) 0))

  (defthm rotate-right-by-zero
    (equal (rotate-right x width 0)
           (loghead width x))
    :hints ((equal-by-logbitp-hint)
            (and stable-under-simplificationp
                 '(:in-theory (enable logbitp-of-loghead-split
                                      logbitp-of-ash-split)))))

  (defthm rotate-right-by-width
    (equal (rotate-right x width width)
           (loghead width x))
    :hints(("Goal" :in-theory (enable logbitp-of-rotate-right-split
                                      logbitp-of-loghead-split))
           (equal-by-logbitp-hint))))



(define rotate-right-1
  ((x      integerp "The bit vector to be rotated right.")
   (width  posp     "The width of @('x')."))
  :returns (rotated natp :rule-classes :type-prescription)
  :short "Rotate a bit-vector by a single place to the right."

  (cond ((zp width)
         0)
        ((equal width 1)
         ;; Rotating a one-bit thing does nothing.
         (loghead 1 x))
        (t
         ;; Gaah, this is ugly
         (let ((x (loghead width x)))
           (logior (ash (logbit 0 x) (1- width))
                   (ash x -1)))))
  ///
  (defcong int-equiv equal (rotate-right-1 x width) 1)
  (defcong nat-equiv equal (rotate-right-1 x width) 2)

  (defthmd logbitp-of-rotate-right-1-split
    (equal (logbitp n (rotate-right-1 x width))
           (b* ((n      (nfix n))
                (width  (nfix width)))
             (cond ((>= n width)          nil)
                   ((equal n (- width 1)) (logbitp 0 x))
                   (t                     (logbitp (+ 1 n) x)))))
    :hints(("Goal" :in-theory (enable logbitp-of-loghead-split))))

  (defthm unsigned-byte-p-of-rotate-right-1
    (implies (natp width)
             (unsigned-byte-p width (rotate-right-1 x width)))
    :hints(("Goal"
            :in-theory (e/d* (ihsext-recursive-redefs)
                             (unsigned-byte-p))))))



(defsection rotate-right**
  :parents (bitops/rotate rotate-right)
  :short "Alternate, recursive definitions of @(see rotate-right)."
  :long "<p>Here are both tail-recursive and non tail-recursive versions of
@(see rotate-right).  These rules are disabled by default and must be
explicitly enabled when you want to use them.</p>"

  (local (in-theory (e/d (case-split-mod-of-decrement)
                         (max natp nfix ifix acl2::floor-mod-elim))))

  (local (defthm integerp-of-/-when-posp
           (implies (posp width)
                    (equal (integerp (/ width))
                           (equal width 1)))
           :hints(("Goal"
                   :in-theory (disable inverse-of-* acl2::equal-*-/-2)
                   :use ((:instance inverse-of-* (x width)))
                   :nonlinearp t))))

  (defthmd rotate-right**
    (equal (rotate-right x width places)
           (if (zp places)
               (loghead width x)
             (rotate-right-1 (rotate-right x width (- places 1))
                             width)))
    :rule-classes ((:definition
                    :clique (rotate-right)
                    :controller-alist
                    ((rotate-right nil nil t))))
    :hints((equal-by-logbitp-hint)
           (and stable-under-simplificationp
                '(:in-theory (e/d (logbitp-of-rotate-right-1-split
                                   logbitp-of-rotate-right-split
                                   logbitp-of-ash-split
                                   logbitp-of-loghead-split
                                   bool->bit b-ior))))))

  (defthmd rotate-right**-tr
    (equal (rotate-right x width places)
           (if (zp places)
               (loghead width x)
             (rotate-right (rotate-right-1 x width)
                           width
                           (- places 1))))
    :rule-classes ((:definition
                    :clique (rotate-right)
                    :controller-alist
                    ((rotate-right nil nil t))))
    :hints((equal-by-logbitp-hint)
           (and stable-under-simplificationp
                '(:in-theory (e/d* (nfix
                                    logbitp-of-rotate-right-1-split
                                    logbitp-of-rotate-right-split)))))))


(defsection rotate-right-extra
  :extension (rotate-right)

  (local (include-book "std/basic/inductions" :dir :system))

  (defrule unsigned-byte-p-of-rotate-right
    (implies (natp width)
             (unsigned-byte-p width (rotate-right x width places)))
    :induct (acl2::dec-induct places)
    :enable rotate-right**
    :disable unsigned-byte-p)

  (defrule rotate-right-of-rotate-right
    (equal (rotate-right (rotate-right x width places1) width places2)
           (rotate-right x width (+ (nfix places1) (nfix places2))))
    :induct (acl2::dec-induct places2)
    :in-theory (e/d (rotate-right**) (loghead))
    :hints (("Subgoal *1/1" :cases ((natp width))))))
