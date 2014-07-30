; Centaur Miscellaneous Books
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; tuplep.lisp
;  - tuplep: recognizer for n-tuples
;  - tuple-listp: recognizer for n-tuple lists

(in-package "ACL2")

(defun tuplep (n x)
  ;; Note: we leave this enabled and allow it to expand.
  (declare (xargs :guard t))
  (and (true-listp x)
       (eql (mbe :logic (len x)
                 :exec (length x))
            n)))

(defund tuple-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (tuplep n (car x))
         (tuple-listp n (cdr x)))))

(defthm tuple-listp-when-atom
  (implies (atom x)
           (equal (tuple-listp n x)
                  (not x)))
  :hints(("Goal" :in-theory (enable tuple-listp))))

(defthm tuple-listp-of-cons
  (equal (tuple-listp n (cons a x))
         (and (tuplep n a)
              (tuple-listp n x)))
  :hints(("Goal" :in-theory (enable tuple-listp))))

(defthm tuple-listp-of-append
  (implies (and (tuple-listp n x)
                (tuple-listp n y))
           (tuple-listp n (append x y)))
  :hints(("Goal" :induct (len x))))
