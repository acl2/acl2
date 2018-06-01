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

(in-package "BITSETS")
(include-book "std/util/define" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))

(local (in-theory (disable logand acl2::loghead unsigned-byte-p)))

(define bignum-extract
  :parents (ttag-bitset-members)
  :short "Extract a particular 32-bit slice of an integer."
  ((x integerp "Integer to extract from")
   (slice natp "Which 32 bit slice to extract"))
  :returns
  (extracted natp :rule-classes :type-prescription)
  :long "<p>Logically, @(call bignum-extract) is essentially:</p>

@({
   (logand (ash x (* -32 slice)) (1- (expt 2 32)))
})

<p>What does this do?  Imagine partitioning the integer @('x') into a list of
32-bit slices.  Say that the least-significant 32 bits are the 0th slice, and
so on.  The @('bignum-extract') function is just extracting the @('slice')th
slice of @('x').</p>

<p>The logical definition of @('bignum-extract') is not very efficient; when
@('x') is a bignum, the @('(ash x (* -32 slice))') term will generally require
us to create a new bignum.</p>

<p>You may <b>optionally, with a trust tag</b> load an raw Lisp replacement
which, on 64-bit CCL that takes advantage of the underlying representation of
bignums, and on other Lisps implements this function using <b>ldb</b>, which
may have or may not be more optimal.</p>"

  :verify-guards nil
  (mbe :logic (let ((x     (ifix x))
                    (slice (nfix slice)))
                (logand (1- (expt 2 32))
                        (ash x (* -32 slice))))
       :exec (the (unsigned-byte 32)
                  (logand (the (unsigned-byte 32) (1- (expt 2 32)))
                          (ash x (* -32 slice)))))
  ///
  (defthm unsigned-byte-p-of-bignum-extract
    (unsigned-byte-p 32 (bignum-extract x slice)))

  (make-event
   `(defthm upper-bound-of-bignum-extract
      (< (bignum-extract x slice) ,(expt 2 32))
      :rule-classes :linear
      :hints(("Goal" :use ((:instance unsigned-byte-p-of-bignum-extract))))))

  (verify-guards bignum-extract))
