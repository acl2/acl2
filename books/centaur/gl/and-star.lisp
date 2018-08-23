; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")

(defun binary-and* (a b)
  (declare (xargs :guard t))
  (and a b))

(defun and*-macro (lst)
  (if (atom lst)
      t
    (if (atom (cdr lst))
        (car lst)
      (list 'binary-and* (car lst)
            (and*-macro (cdr lst))))))

(defmacro and* (&rest lst)
  (and*-macro lst))

(add-binop and* binary-and*)

(defcong iff equal (and* a b) 1)

(defcong iff iff (and* a b) 2)

(defthm and*-rem-first
  (implies a
           (equal (and* a b) b)))

(defthm and*-rem-second
  (implies b
           (iff (and* a b) a)))

(defthm and*-nil-first
  (equal (and* nil b) nil))

(defthm and*-nil-second
  (equal (and* a nil) nil))

(defthm and*-forward
  (implies (and* a b) (and a b))
  :rule-classes :forward-chaining)

(defmacro and** (&rest lst)
  `(mbe :logic (and* . ,lst)
        :exec (and . ,lst)))

(in-theory (disable and*))
