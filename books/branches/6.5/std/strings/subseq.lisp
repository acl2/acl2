; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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


; subseq.lisp
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(local (include-book "arithmetic"))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "coerce"))

;; NOTE: These get globally disabled by including this book!  This is probably
;; how things ought to be.

(in-theory (disable subseq subseq-list))

(local (in-theory (enable subseq subseq-list)))

(defthm len-of-subseq-list
  (equal (len (subseq-list x start end))
         (nfix (- end start))))

(defthm true-listp-subseq-list
  (true-listp (subseq-list x start end))
  :rule-classes :type-prescription)

(defthm stringp-of-subseq
  (equal (stringp (subseq x start end))
         (stringp x)))

(defthm length-of-subseq
  (equal (length (subseq x start end))
         (nfix (- (or end (length x)) start))))

(defthm len-of-subseq
  (equal (len (subseq x start end))
         (if (stringp x)
             0
           (nfix (- (or end (len x)) start)))))
