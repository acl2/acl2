; Centaur Miscellaneous Books
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stobj-swap")
(include-book "tools/clone-stobj" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "misc/assert" :dir :system)

; This is just a test of the stobj-swap book, which once had a bug.

(defstobj foo$
  (f1 :type integer :initially 0)
  (f2 :type string :initially "Hello")
  (f3 :type character :initially #\a))

(defstobj-clone foo$2 foo$ :suffix "2")

(def-stobj-swap foo$ foo$2)

(defun my-test (foo$ foo$2)
  (declare (xargs :stobjs (foo$ foo$2)))
  (b* ((foo$ (update-f1 5 foo$))
       (foo$ (update-f2 "Goodbye" foo$))
       (foo$ (update-f3 #\x foo$))

       (foo$2 (update-f1 7 foo$2))
       (foo$2 (update-f2 "World" foo$2))
       (foo$2 (update-f3 #\k foo$2))

       ((mv foo$ foo$2) (swap-foo$s foo$ foo$2))

       (okp (and (or (equal (f1 foo$) 7)
                     (cw "Oops, F1 of foo$ should be 7 but is ~x0~%" (f1 foo$)))
                 (or (equal (f2 foo$) "World")
                     (cw "Oops, F2 of foo$ should be \"World\" but is ~x0~%" (f2 foo$)))
                 (or (equal (f3 foo$) #\k)
                     (cw "Oops, F3 of foo$ should be #\\k but is ~x0~%" (f3 foo$)))

                 (or (equal (f1 foo$2) 5)
                     (cw "Oops, F1 of foo$2 should be 5 but is ~x0~%" (f1 foo$2)))
                 (or (equal (f2 foo$2) "Goodbye")
                     (cw "Oops, F2 of foo$2 should be \"Goodbye\" but is ~x0~%" (f2 foo$2)))
                 (or (equal (f3 foo$2) #\x)
                     (cw "Oops, F3 of foo$2 should be #\\x but is ~x0~%" (f3 foo$2))))))

    (mv okp foo$ foo$2)))

(defconsts (*ok* foo$ foo$2)
  (my-test foo$ foo$2))

(assert! *ok*)




