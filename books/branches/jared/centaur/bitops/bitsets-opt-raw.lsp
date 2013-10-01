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

