; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
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

; parity.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(local (include-book "ihsext-basics"))

(defxdoc bitops/parity
  :parents (bitops)
  :short "Parity (i.e., reduction xor) related functions.")

(local (xdoc::set-default-parents bitops/parity))

(local (defthm bitp-logxor
         (implies (and (bitp x)
                       (bitp y))
                  (bitp (logxor x y)))
         :hints(("Goal" :in-theory (enable bitp)))))

(define parity ((n natp)
                (x integerp))
  :short "@(call parity) computes the parity of the low @('n') bits of @('x'),
returning it as a @(see bitp)."

  :long "<p>This has a simple recursive definition which should be easy to
reason about.  However, it isn't particularly efficient; see @(see fast-parity)
for a more efficient, logically identical function.</p>"

  :measure (nfix n)
  :returns (p bitp :rule-classes :type-prescription)
  (cond ((zp n) 0)
        (t (logxor (logand x 1) (parity (1- n) (ash x -1)))))
  ///
  (fty::deffixequiv parity)

  (defthm parity-decomp
    (equal (logxor (parity m (logtail n x))
                   (parity n (loghead n x)))
           (parity (+ (nfix m) (nfix n)) x))
    :hints (("goal" :in-theory (enable* bitops::ihsext-inductions)
             :induct (loghead n x)
             :expand ((loghead n x)
                      (:free (x) (loghead 1 x))
                      (logtail n x)
                      (:free (x) (logtail 1 x))
                      (:free (n) (parity n x))
                      (:free (x) (parity n x))
                      (parity m (ifix x))))))

  (defthm parity-of-logxor
    (equal (parity n (logxor x y))
           (logxor (parity n x)
                   (parity n y))))

  (defthm parity-of-0
    (equal (parity n 0)
           0))

  (defthm parity-of-loghead-split
    (equal (parity m (loghead n x))
           (parity (min (nfix m) (nfix n)) x))
    :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions)
            :induct (list (loghead m x)
                          (loghead n x))
             :expand ((loghead n x)
                      (:free (x) (loghead 1 x))
                      (logtail n x)
                      (:free (x) (logtail 1 x))
                      (:free (n) (parity n x))
                      (:free (x) (parity m x))
                      (parity m (ifix x)))))))


(define parity4 ((x :type (unsigned-byte 4)))
  :short "Optimized version of @('(parity 4 x)')."
  :inline t
  :enabled t
  :verify-guards nil
  :returns (p bitp :rule-classes :type-prescription)
  :long "<p>The basic idea is from Sean Anderson's <a
href='http://graphics.stanford.edu/~seander/bithacks.html'>bit twiddling
hacks</a> page.  The number @('#x6996') acts as a lookup table for the parity
of the numbers between 0 and 15, so we can simply index into it to get the
answer.</p>

<p>It seems that using @('ash') and @('logand') is slightly faster than
@('logbit') in ccl.  Could perhaps be faster still if we found a way to get CCL
to optimize away the @('ash') function call.</p>
"

  (mbe :logic (parity 4 x)
       :exec
       (the bit (logand 1
                        (the (unsigned-byte 32)
                          (ash (the (unsigned-byte 32) #x6996)
                               (the (integer -16 0) (- (the (unsigned-byte 4) x)))))))
       ;; (the bit (logbit (the (unsigned-byte 5) x)
       ;;                  (the (unsigned-byte 16) #x6996)))
       )
  ///
  (local (fty::deffixequiv parity4 :args ((x integerp))))
  (local (defun check-parity4 (x)
           (if (zp x)
               t
             (let ((x (1- x)))
               (and (equal (parity4 x) (logbit x #x6996))
                    (check-parity4 x))))))
  (local (defthm check-parity4-correct
           (implies (and (< (ifix x) (nfix n))
                         (<= 0 (ifix x))
                         (check-parity4 n))
                    (equal (logbit x #x6996)
                           (parity4 x)))
           :hints(("Goal" :in-theory (disable parity4)))))
  (local (defthm minus-minus
           (equal (- (- x)) (fix x))))
  (verify-guards parity4$inline
    :hints (("goal" :use ((:instance check-parity4-correct (n 16)))))))


(define parity32 ((x :type (unsigned-byte 32)))
  :short "Optimized version of @('(parity 32 x)')."
  :inline t
  :enabled t
  :long "<p>The basic idea is from Sean Anderson's <a
href='http://graphics.stanford.edu/~seander/bithacks.html'>bit twiddling
hacks</a> page, except that we don't use a lookup table at the end.  See @(see
parity4) for details about why we don't do that.</p>"
:guard-hints (("goal" :expand ((:free (n x) (parity n x)))))
  (mbe :logic (parity 32 x)
       :exec
       (b* ((x (the (unsigned-byte 32) (logxor x (the (unsigned-byte 32) (ash x -16)))))
            (x (the (unsigned-byte 32) (logxor x (the (unsigned-byte 32) (ash x -8)))))
            (x (the (unsigned-byte 32) (logxor x (the (unsigned-byte 32) (ash x -4)))))
            (x (the (unsigned-byte 32) (logxor x (the (unsigned-byte 32) (ash x -2)))))
            (x (the (unsigned-byte 32) (logxor x (the (unsigned-byte 32) (ash x -1))))))
         (the (unsigned-byte 1) (logand 1 x)))))


(define fast-parity ((n natp) (x integerp))
  :returns (p bitp :rule-classes :type-prescription)
  :short "Optimized alternative to @(see parity)."
  :enabled t
  :long "<p>This is faster than @(see parity) because it computes up to 32 bits
of parity at a time using @(see parity32).</p>"
  :verify-guards nil
  (mbe :logic (parity n x)
       :exec (if (<= n 32)
                 (parity32 (logand (logmask n) x))
               (logxor (parity32 (logand #xffffffff x))
                       (fast-parity (- n 32) (ash x -32)))))
  ///
  (verify-guards fast-parity
    :hints (("goal" :in-theory (e/d (nfix)
                                    (logmask parity-decomp))
             :expand ((:free (n x) (fast-parity n x)))
             :use ((:instance parity-decomp
                    (n 32) (m (- n 32))))))))
