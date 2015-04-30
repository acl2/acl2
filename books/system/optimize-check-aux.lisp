; Optimization Checking
; Copyright (C) 2015 Centaur Technology
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

(in-package "ACL2")

(defconst *length-check*
  ;; Should not stack overflow.
  (length (make-list 1000000)))

(defconst *len-check*
  ;; Should not stack overflow.
  (len (make-list 1000000)))

(defun my-len-1 (x acc)
  (declare (xargs :guard (natp acc)))
  (cond ((atom x)
         acc)
        (t
         (my-len-1 (cdr x) (+ 1 acc)))))

(comp 'my-len-1)

(defconst *my-len-1-check*
  ;; Should not stack overflow.
  (my-len-1 (make-list 1000000) 0))

;; Some functions to test inlining in the superior book.

(defun-notinline sub-f1 (x) (+ x 1))
(defun-inline    sub-f2 (x) (+ x 1))

(defun sub-g1 (x) (sub-f1 x))
(defun sub-g2 (x) (sub-f2 x))

