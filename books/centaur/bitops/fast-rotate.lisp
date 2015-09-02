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
; Original author: Shilpi Goel <shilpi@centtech.com>

(in-package "BITOPS")

(include-book "rotate")
(include-book "std/strings/cat" :dir :system)

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

(defsection bitops/fast-rotate
  :parents (bitops)
  :short "This book provides optimized rotate functions, which are
proven equivalent to @(see rotate-left) and @(see rotate-right) via
@(see mbe)."
  )

(defsection fast-rotate
  :parents (bitops/fast-rotate)
  :short "@('fast-rotate-left') is logically identical to @(see
  rotate-left) and @('fast-rotate-right') is logically identical to
  @(see rotate-right)."

  :long "<p>@('fast-rotate-left') and @('fast-rotate-right') are
actually macros.  Generally, they expand into a call of
@('rotate-left') and @('rotate-right') respectively.  But in the
common cases where @('n') is explicitly 8, 16, 32, or 64, they instead
expand into a call of a specialized, inlined function.</p>

@(def fast-rotate-left)

@(def fast-rotate-right)"

  )

(defmacro fast-rotate-left (x width places)
  (cond ((eql width 8)   `(rotate-left-8  ,x ,places))
        ((eql width 9)   `(rotate-left-9  ,x ,places))
        ((eql width 16)  `(rotate-left-16 ,x ,places))
        ((eql width 17)  `(rotate-left-17 ,x ,places))
        ((eql width 32)  `(rotate-left-32 ,x ,places))
        ((eql width 33)  `(rotate-left-33 ,x ,places))
        ((eql width 64)  `(rotate-left-64 ,x ,places))
        ((eql width 65)  `(rotate-left-65 ,x ,places))
        (t
         `(rotate-left ,x ,width ,places))))

(defmacro fast-rotate-right (x width places)
  (cond ((eql width 8)   `(rotate-right-8  ,x ,places))
        ((eql width 9)   `(rotate-right-9  ,x ,places))
        ((eql width 16)  `(rotate-right-16 ,x ,places))
        ((eql width 17)  `(rotate-right-17 ,x ,places))
        ((eql width 32)  `(rotate-right-32 ,x ,places))
        ((eql width 33)  `(rotate-right-33 ,x ,places))
        ((eql width 64)  `(rotate-right-64 ,x ,places))
        ((eql width 65)  `(rotate-right-65 ,x ,places))
        (t
         `(rotate-right ,x ,width ,places))))


;; ======================================================================
;; Rotate left:
;; ======================================================================

(local
 ;; From bitops/rotate.lisp:
 (defthm rem-is-mod
   ;; (let ((places 20)
   ;;       (width 4))
   ;;   ;; REM finishes in 2.4 seconds, MOD in 2.8 seconds...
   ;;   (time (loop for i fixnum from 1 to 100000000 do
   ;;               (mod places width)))
   ;;   (time (loop for i fixnum from 1 to 100000000 do
   ;;               (rem places width))))
   (implies (and (natp places)
                 (posp width))
            (equal (rem places width)
                   (mod places width)))
   :hints(("Goal" :in-theory (enable mod rem)))))

(local
 (defthm ash-monotonic
   (implies (and (<= m n)
                 (posp x)
                 (natp m)
                 (natp n))
            (<= (ash x m) (ash x n)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(local
 (defthm ash-1-x-non-zero
   (implies (natp x)
            (not (equal (ash 1 x) 0)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(local
 (defthm rotate-left-guard-helper-1
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (<= (mod places n) (1- n)))
   :rule-classes :linear))

(local
 (defthm rotate-left-guard-helper-2
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (<= (+ n (- (mod places n))) n))
   :rule-classes :linear))

(local
 (defthm rotate-left-guard-helper-3
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (<= (ash 1 (+ n (- (mod places n))))
                (ash 1 n)))
   :rule-classes :linear))

(local
 (defthm rotate-left-guard-helper-3-1
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (< (+ -1 (ash 1 (+ n (- (mod places n)))))
               (expt 2 n)))
   :hints (("Goal" :in-theory (e/d* (expt-2-is-ash)
                                    (unsigned-byte-p))))))

(local
 (defthm rotate-left-guard-helper-3-2
   (implies (and (unsigned-byte-p n places)
                 (unsigned-byte-p n x))
            (unsigned-byte-p n (+ -1 (ash 1 (+ n (- (mod places n)))))))))

(local
 (defthm rotate-left-guard-helper-4
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p (+ n (- (mod places n))) (+ -1 (ash 1 (+ n (- (mod places n)))))))
   :hints (("Goal" :in-theory (e/d* (expt-2-is-ash)
                                    (acl2::exponents-add
                                     acl2::expt-minus))))))

(local
 (defthm rotate-left-guard-helper-5
   (implies
    (and (unsigned-byte-p n places)
         (unsigned-byte-p n x))
    (unsigned-byte-p (+ n (- (mod places n)))
                     (logand x (+ -1 (ash 1 (+ n (- (mod places n))))))))
   :hints (("Goal" :in-theory (e/d* ()
                                    ())))))

(local
 (defthm rotate-left-guard-helper-6
   (implies
    (and (unsigned-byte-p n places)
         (unsigned-byte-p n x)
         (posp n))
    (unsigned-byte-p n (ash (logand x (+ -1 (ash 1 (+ n (- (mod places n))))))
                            (mod places n))))))


(define rotate-left-n-function-gen
  ((n natp))
  :verify-guards nil

  (let* ((n-1 (1- n))
         (n+1 (1+ n))
         (neg-n (- n))
         (fn-name-string (str::cat "ROTATE-LEFT-"
                                   (coerce (explode-nonnegative-integer
                                            n 10 '())
                                           'string)))
         (fn-name (intern$ fn-name-string "BITOPS")))

    `(define ,fn-name
       ((x      :type (unsigned-byte ,n) "The bit vector to be rotated left.")
        (places :type (unsigned-byte ,n) "The number of places to rotate left."))

       :parents (fast-rotate)
       :enabled t
       :inline t
       :prepwork ((local (in-theory (e/d (rotate-left) (unsigned-byte-p)))))

       (mbe
        :logic
        (rotate-left x ,n places)
        :exec
        (let* ((x           (mbe :logic (loghead ,n x)
                                 :exec x))
               (places      (mbe :logic (lnfix places)
                                 :exec places))

               (places
                (mbe :logic (mod places ,n)
                     :exec (if (< places ,n)
                               (the (integer 0 ,n-1) places)
                             (the (integer 0 ,n-1) (rem places ,n)))))
               (low-num    (the (integer 0 ,n) (- ,n places)))
               (mask       (the (unsigned-byte ,n) (1- (the (unsigned-byte ,n+1) (ash 1 low-num)))))
               (xl         (the (unsigned-byte ,n) (logand x mask)))
               (xh         (the (unsigned-byte ,n) (logand x (the (signed-byte ,n+1) (lognot mask)))))
               (xh-shift   (the (unsigned-byte ,n) (ash xh (the (integer ,neg-n 0) (- low-num)))))
               (xl-shift   (the (unsigned-byte ,n) (ash (the (unsigned-byte ,n) xl)
                                                        (the (integer 0 ,n) places))))
               (ans        (the (unsigned-byte ,n) (logior xl-shift xh-shift))))
          ans)))))

;; Feel free to create different versions of fast-rotate-left-<n> as
;; required.

(make-event (rotate-left-n-function-gen  8))
(make-event (rotate-left-n-function-gen 16))
(make-event (rotate-left-n-function-gen 32))
(make-event (rotate-left-n-function-gen 64))

(make-event (rotate-left-n-function-gen  9))
(make-event (rotate-left-n-function-gen 17))
(make-event (rotate-left-n-function-gen 33))
(make-event (rotate-left-n-function-gen 65))

;; ======================================================================
;; Rotate right:
;; ======================================================================

(local
 (defthm rotate-right-guard-helper-1
   (implies (and (unsigned-byte-p n places)
                 (< places n))
            (unsigned-byte-p n (ash 1 places)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(local
 (defthm rotate-right-guard-helper-2
   (implies (and (unsigned-byte-p n places)
                 (< places n))
            (unsigned-byte-p n (+ -1 (ash 1 places))))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(local
 (defthm rotate-right-guard-helper-3
   (implies (unsigned-byte-p n places)
            (unsigned-byte-p places (+ -1 (ash 1 places))))
   :hints (("Goal" :in-theory (e/d* (expt-2-is-ash)
                                    (acl2::exponents-add
                                     acl2::expt-minus))))))

(local
 (defthm rotate-right-guard-helper-4
   (implies (unsigned-byte-p n places)
            (unsigned-byte-p places (logand x (+ -1 (ash 1 places)))))
   :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))))

(local
 (defthm rotate-right-guard-helper-5
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p n
                             (ash (logand x (+ -1 (ash 1 places)))
                                  (+ n (- places)))))
   :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))))

(local
 (defthm rotate-right-guard-helper-6
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p n (ash 1 (mod places n))))))

(local
 (defthmd rotate-right-guard-helper-7
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p n (mod places n)))))

(local
 (defthm rotate-right-guard-helper-8-1
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p (mod places n)
                             (+ -1 (ash 1 (mod places n)))))
   :hints (("Goal"
            :use ((:instance rotate-right-guard-helper-7))
            :in-theory (e/d* () (unsigned-byte-p))))))

(local
 (defthm rotate-right-guard-helper-8-2
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p n
                             (+ -1 (ash 1 (mod places n)))))
   :hints (("Goal"
            :use ((:instance rotate-right-guard-helper-7))
            :in-theory (e/d* () (unsigned-byte-p))))))

(local
 (defthm rotate-right-guard-helper-9
   (implies (and (unsigned-byte-p n places)
                 (posp n))
            (unsigned-byte-p n
                             (ash (logand x (+ -1 (ash 1 (mod places n))))
                                  (+ n (- (mod places n))))))
   :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))))

(define rotate-right-n-function-gen
  ((n natp))
  :verify-guards nil

  (let* ((n-1 (1- n))
         (neg-n (- n))
         (fn-name-string (str::cat "ROTATE-RIGHT-"
                                   (coerce (explode-nonnegative-integer
                                            n 10 '())
                                           'string)))
         (fn-name (intern$ fn-name-string "BITOPS")))

    `(define ,fn-name
       ((x      :type (unsigned-byte ,n) "The bit vector to be rotated right.")
        (places :type (unsigned-byte ,n) "The number of places to rotate right."))

       :parents (fast-rotate)
       :enabled t
       :inline t
       :prepwork ((local (in-theory (e/d (rotate-right) (unsigned-byte-p)))))

       (mbe
        :logic
        (rotate-right x ,n places)
        :exec
        (let* ((x           (mbe :logic (loghead ,n x)
                                 :exec x))
               (places      (mbe :logic (lnfix places)
                                 :exec places))

               (places     (if (< places ,n)
                               (the (integer 0 ,n-1) places)
                             (the (integer 0 ,n-1) (rem places ,n))))
               (mask       (the (unsigned-byte ,n)
                             (1- (the (unsigned-byte ,n) (ash 1 places)))))
               (xl         (the (unsigned-byte ,n) (logand x mask)))
               (xh-shift   (the (unsigned-byte ,n)
                             (ash x (the (integer ,neg-n 0) (- places)))))
               (high-num   (the (integer 0 ,n) (- ,n places)))
               (xl-shift   (the (unsigned-byte ,n) (ash xl high-num)))
               (ans        (the (unsigned-byte ,n)
                             (logior xl-shift xh-shift))))
          ans)))))

;; Feel free to create different versions of fast-rotate-right-<n> as
;; required.

(make-event (rotate-right-n-function-gen  8))
(make-event (rotate-right-n-function-gen 16))
(make-event (rotate-right-n-function-gen 32))
(make-event (rotate-right-n-function-gen 64))

(make-event (rotate-right-n-function-gen  9))
(make-event (rotate-right-n-function-gen 17))
(make-event (rotate-right-n-function-gen 33))
(make-event (rotate-right-n-function-gen 65))

;; ======================================================================
