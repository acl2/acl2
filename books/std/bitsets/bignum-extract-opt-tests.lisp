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
(include-book "bignum-extract-opt")
(include-book "std/testing/assert" :dir :system)

(defund bignum-extract-slow (x slice)
  ;; For testing, we define something equivalent to the logical
  ;; definition of bignum-extract.
  (declare (xargs :guard (and (integerp x)
                              (natp slice))))
  (let ((x     (ifix x))
        (slice (nfix slice)))
    (logand (1- (expt 2 32))
            (ash x (* -32 slice)))))

(defthm bignum-extract-slow-correct
  (equal (bignum-extract-slow x slice)
         (bignum-extract x slice))
  :hints(("Goal" :in-theory (acl2::enable bignum-extract-slow
                                          bignum-extract))))

; Primitive tests to make sure it seems to be working.

(defconst *test-numbers*
  (list 1 0 -1
        100 -100
        -127 -128
        127 128

        (expt 2 60)
        (+ 1 (expt 2 60))
        (+ 2 (expt 2 60))
        (+ -1 (expt 2 60))
        (+ -2 (expt 2 60))

        (- (expt 2 60))
        (- (+ 1 (expt 2 60)))
        (- (+ 2 (expt 2 60)))
        (- (+ -1 (expt 2 60)))
        (- (+ -2 (expt 2 60)))

        (floor (expt 2 90) 3)
        (floor (expt 2 90) 5)
        (floor (expt 2 90) 7)

        (- (floor (expt 2 90) 3))
        (- (floor (expt 2 90) 5))
        (- (floor (expt 2 90) 7))
        ))

(defconst *test-slice-indices*
  (list 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
        ;; SBCL has a bug with LDB on large numbers, which we have reported.
        ;; Once it is fixed, we can remove these conditionals.
        (expt 2 51)
        (+ 1 (expt 2 52))
        (+ 7 (expt 2 53))
        (+ 9 (expt 2 54))
        (+ 2 (expt 2 55))
        (+ 3 (expt 2 56))
        (- (expt 2 57) 1)
        (expt 2 57)
        (- (expt 2 57) 2)
        (- (expt 2 57) 3)
        (expt 2 60)
        (+ 1 (expt 2 60))
        (+ 2 (expt 2 60))
        (+ 2 (expt 2 61))
        (+ 2 (expt 2 62))
        (+ 2 (expt 2 63))
        (expt 2 90)))

;; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
;; definition.
(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defun test0 (num index)
  (declare (xargs :guard (and (integerp num)
                              (natp index))))
  (or (equal (bignum-extract num index)
             (bignum-extract-slow num index))
      (cw "Oops: (bignum-extract ~x0 ~x1): spec = ~x2, impl = ~x3.~%"
          num index
          (bignum-extract-slow num index)
          (bignum-extract num index))))

(defun test1 (num indices)
  (declare (xargs :guard (and (integerp num)
                              (nat-listp indices))))
  (if (atom indices)
      t
    (and (test0 num (car indices))
         (test1 num (cdr indices)))))

(defun test2 (nums indices)
  (declare (xargs :guard (and (integer-listp nums)
                              (nat-listp indices))))
  (if (atom nums)
      t
    (and (test1 (car nums) indices)
         (test2 (cdr nums) indices))))

(assert! (test2 *test-numbers* *test-slice-indices*))
