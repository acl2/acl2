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
(include-book "tools/templates" :dir :system)
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

(define nth-slice ((size natp  "size of a slice")
                   (n    natp  "which slice")
                   (x    integerp))
  :returns (slice natp :rule-classes :type-prescription)
  (loghead size (logtail (* (lnfix size) (lnfix n)) x))
  ///
  (defcong nat-equiv equal (nth-slice size n x) 1)
  (defcong nat-equiv equal (nth-slice size n x) 2)
  (defcong int-equiv equal (nth-slice size n x) 3)

  (defret unsigned-byte-p-of-nth-slice
    (implies (and (<= (nfix size) width)
                  (natp width))
             (unsigned-byte-p width (nth-slice size n x)))))


                  

(define update-nth-slice ((size natp  "size of a slice")
                          (n    natp  "which slice")
                          (v    integerp "data to insert")
                          (x    integerp))
  :returns (new-x integerp :rule-classes :type-prescription)
  (mbe :logic
       (logapp (* (nfix n) (nfix size))
               x
               (logapp size v (logtail (* (+ 1 (nfix n)) (nfix size)) x)))
       :exec (b* ((mask (1- (ash 1 size)))
                  (val (logand mask v))
                  (low (* n size)))
               (logior (logand x (lognot (ash mask low)))
                       (ash val low))))
  :prepwork ((local
              (encapsulate nil
                (local (defun logior-loghead-is-logapp-ind (w2 y x)
                         (if (zp w2)
                             (list y x)
                           (logior-loghead-is-logapp-ind (1- w2) (logcdr y) (logcdr x)))))
                (local (defthm logior-loghead-is-logapp
                         (implies (natp w2)
                                  (equal (logior (loghead w2 y)
                                                 (logand x (lognot (+ -1 (ash 1 w2)))))
                                         (logapp w2 y (logtail w2 x))))
                         :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                                          ash-minus-1-is-logmask)
                                                         (logmask
                                                          acl2::commutativity-of-logand
                                                          acl2::commutativity-of-logior))
                                 :expand ((loghead w2 y)
                                          (logtail w2 x)
                                          (:free (x) (logapp w2 y x))
                                          (logmask w2)
                                          (logand x -1)
                                          (:free (a b) (lognot (logcons a b)))
                                          (:free (a b) (logand x (logcons a b)))
                                          (:free (a b c d) (logior (logcons a b) (logcons c d))))
                                 :induct (logior-loghead-is-logapp-ind w2 y x)))))
                (local (defun part-install-logior-is-logapp-ind (x w1)
                         (if (zp w1)
                             (list x)
                           (part-install-logior-is-logapp-ind (logcdr x) (1- w1)))))
                (defthm part-install-logior-is-logapp
                  (implies (and (natp w1) (natp w2))
                           (equal (logior (ash (loghead w2 y) w1)
                                          (logand x (lognot (ash (+ -1 (ash 1 w2)) w1))))
                                  (logapp w1 x (logapp w2 y (logtail (+ w1 w2) x)))))
                  :hints (("goal" :induct (part-install-logior-is-logapp-ind x w1)
                           :expand ((:free (y) (ash y w1))
                                    (:free (a b) (lognot (logcons a b)))
                                    (:free (y) (logapp w1 x y))
                                    (:free (a b) (logand x (logcons a b)))
                                    (:free (z) (logtail (+ w1 z) x))
                                    (:free (a b c d) (logior (logcons a b) (logcons c d))))))))))
  ///
  (defcong nat-equiv equal (update-nth-slice size n v x) 1)
  (defcong nat-equiv equal (update-nth-slice size n v x) 2)
  (defcong int-equiv equal (update-nth-slice size n v x) 3)
  (defcong int-equiv equal (update-nth-slice size n v x) 4)

  (local (defthm unsigned-byte-p-natp-fwd
           (implies (unsigned-byte-p n x)
                    (and (natp n) (natp x)))
           :rule-classes :forward-chaining))

  (defret unsigned-byte-p-of-update-nth-slice
    (implies (and (<= (* (+ 1 (nfix n)) (nfix size)) width)
                  (unsigned-byte-p width x))
             (unsigned-byte-p width new-x))
    :hints(("Goal" :in-theory (disable unsigned-byte-p))))

  (defret natp-of-update-nth-slice
    (implies (natp x)
             (natp new-x))
    :rule-classes :type-prescription))

(def-ruleset nth-slices-normalize-to-nth-slice nil)
(def-ruleset nth-slice-definitions nil)

(defmacro def-nth-slice (width)
  (b* ((str-alist `(("<W>" . ,(coerce (explode-atom width 10) 'string))))
       ((mv shortstr &)
        (acl2::tmpl-str-sublis
         str-alist
         "Extract the @('n')th <W>-bit slice of the integer @('x').")))
    (acl2::template-subst
     '(define nth-slice<W> ((n natp)
                            (x integerp))
        :returns (slice natp :rule-classes :type-prescription)
        :parents (bitops/extra-defs)
        :short <SHORTSTR>
        :long "<p>We leave this enabled; we would usually not expect to try to reason
about it.</p>"
        :enabled t
        :inline t
        (mbe :logic
             (logand (ash (ifix x) (* (nfix n) <-W>)) (1- (expt 2 <W>)))
             :exec
             (the (unsigned-byte <W>)
                  (logand (ash x (the (integer * 0) (* n <-W>))) <WMASK>)))
        ///
        (add-to-ruleset nth-slice-definitions '((:d nth-slice<W>)))
        (defcong nat-equiv equal (nth-slice<W> n x) 1)
        (defcong int-equiv equal (nth-slice<W> n x) 2)
        (defthm unsigned-byte-p-<W>-of-nth-slice<W>
          (unsigned-byte-p <W> (nth-slice<W> n x)))

        (defthmd nth-slice<W>-is-nth-slice
          (equal (nth-slice<W> n x)
                 (nth-slice <W> n x))
          :hints(("Goal" :in-theory (enable nth-slice))))

        (add-to-ruleset nth-slices-normalize-to-nth-slice nth-slice<W>-is-nth-slice))
     :str-alist str-alist
     :atom-alist `((<W> . ,width)
                   (<-W> . ,(- width))
                   (<WMASK> . ,(logmask width))
                   (<SHORTSTR> . ,shortstr))
     :pkg-sym nil)))

(def-nth-slice 2  )
(def-nth-slice 4  )
(def-nth-slice 8  )
(def-nth-slice 16 )
(def-nth-slice 32 )
(def-nth-slice 64 )
(def-nth-slice 128)
(def-nth-slice 256)
(def-nth-slice 512)

(defmacro nth-slice$ (size n x)
  (case size
    (2   `(nth-slice2   ,n ,x))
    (4   `(nth-slice4   ,n ,x))
    (8   `(nth-slice8   ,n ,x))
    (16  `(nth-slice16  ,n ,x))
    (32  `(nth-slice32  ,n ,x))
    (64  `(nth-slice64  ,n ,x))
    (128 `(nth-slice128 ,n ,x))
    (256 `(nth-slice256 ,n ,x))
    (512 `(nth-slice512 ,n ,x))
    (t `(nth-slice ,size ,n ,x))))



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




(define install-bit ((n natp) (val bitp) (x integerp))
  :parents (bitops)
  :short "@(call install-bit) sets @('x[n] = val'), where @('x') is an integer,
@('n') is a bit position, and @('val') is a bit."

  (mbe :logic
       (b* ((x     (ifix x))
            (n     (nfix n))
            (val   (bfix val))
            (place (ash 1 n))
            (mask  (lognot place)))
         (logior (logand x mask)
                 (ash val n)))
       :exec
       (logior (logand x (lognot (ash 1 n)))
               (ash val n)))
  ///

  (defthmd install-bit**
    (equal (install-bit n val x)
           (if (zp n)
               (logcons val (logcdr x))
             (logcons (logcar x)
                      (install-bit (1- n) val (logcdr x)))))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))
    :rule-classes
    ((:definition
      :clique (install-bit)
      :controller-alist ((install-bit t nil nil)))))

  (add-to-ruleset ihsext-redefs install-bit**)
  (add-to-ruleset ihsext-recursive-redefs install-bit**)

  (defthm natp-install-bit
    (implies (not (and (integerp x)
                       (< x 0)))
             (natp (install-bit n val x)))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (install-bit n val x) 1)
  (defcong bit-equiv equal (install-bit n val x) 2)
  (defcong int-equiv equal (install-bit n val x) 3)

  (defthmd logbitp-of-install-bit-split
    ;; Disabled by default since it can cause case splits.
    (equal (logbitp m (install-bit n val x))
           (if (= (nfix m) (nfix n))
               (equal val 1)
             (logbitp m x)))
    :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-install-bit-split)
  (acl2::add-to-ruleset! logbitp-case-splits logbitp-of-install-bit-split)

  (local (in-theory (e/d (logbitp-of-install-bit-split)
                         (install-bit))))

  (defthm logbitp-of-install-bit-same
    (equal (logbitp m (install-bit m val x))
           (equal val 1)))

  (defthm logbitp-of-install-bit-diff
    (implies (not (equal (nfix m) (nfix n)))
             (equal (logbitp m (install-bit n val x))
                    (logbitp m x))))

  (local
   (defthm install-bit-induct
     t
     :rule-classes ((:induction
                     :pattern (install-bit pos v i)
                     :scheme (logbitp-ind pos i)))))

  (defthm install-bit-of-install-bit-same
    (equal (install-bit a v (install-bit a v2 x))
           (install-bit a v x))
    :hints(("Goal" :in-theory (enable install-bit**))))

  (defthm install-bit-of-install-bit-diff
    (implies (not (equal (nfix a) (nfix b)))
             (equal (install-bit a v (install-bit b v2 x))
                    (install-bit b v2 (install-bit a v x))))
    :hints(("Goal" :in-theory (enable install-bit**)))
    :rule-classes ((:rewrite :loop-stopper ((a b install-bit)))))

  (add-to-ruleset ihsext-basic-thms
                  '(logbitp-of-install-bit-same
                    logbitp-of-install-bit-diff
                    install-bit-of-install-bit-same
                    install-bit-of-install-bit-diff))

  (defthm install-bit-when-redundant
    (implies (equal (logbit n x) b)
             (equal (install-bit n b x)
                    (ifix x)))
    :hints(("Goal" :in-theory (enable install-bit**))))

  (defthm unsigned-byte-p-of-install-bit
    (implies (and (unsigned-byte-p n x)
                  (< (nfix i) n))
             (unsigned-byte-p n (install-bit i v x)))
    :hints(("Goal" :in-theory (e/d (install-bit** unsigned-byte-p**)
                                   (unsigned-byte-p))))))
