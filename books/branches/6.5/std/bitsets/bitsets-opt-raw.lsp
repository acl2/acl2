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

#+(and Clozure x86-64)
(declaim (inline bignum-extract))

#+(and Clozure x86-64)
(defun bignum-extract (x slice)
  (cond ((not (typep slice 'fixnum))
         ;; If the slice is not even a fixnum, you have bigger problems.  We
         ;; just fall back to the logical definition.
         (bignum-extract-slow x slice))
        ((typep x 'fixnum)
         ;; Since fixnums are 60 bits, the only valid slices are 0 and 1.
         (cond ((= (the fixnum slice) 0)
                (the fixnum (logand (1- (expt 2 32))
                                    (the fixnum x))))
               ((= (the fixnum slice) 1)
                (the fixnum (logand (1- (expt 2 32))
                                    (the fixnum (ash (the fixnum x) -32)))))
               ;; For slices beyond these, we need to consider whether X is
               ;; negative since in 2's complement negative numbers have
               ;; "infinite leading 1's."
               ((< x 0)
                (1- (expt 2 32)))
               (t
                0)))
        ;; Else, a bignum.  CCL represents bignums as vectors of 32-bit numbers
        ;; with the least significant chunks coming first.
        ((< (the fixnum slice) (the fixnum (ccl::uvsize x)))
         ;; In bounds for the array -- just an array access.
         (ccl::uvref x slice))
        ;; Else, out of bounds -- like indexing beyond a fixnum, we need to
        ;; return all 0's or all 1's depending on whether X is negative.
        ((< x 0)
         (1- (expt 2 32)))
        (t
         0)))

#+(and Clozure x86-64)
(defun bitset-members (x)
  (ttag-bitset-members x))

