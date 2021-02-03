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
(include-book "std/stobjs/clone" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

; This is just a test of the stobj-swap book, which once had a bug.

(defstobj foo$
  (f1 :type integer :initially 0)
  (f2 :type string :initially "Hello")
  (f3 :type character :initially #\a)
  (f4 :type (array integer (3)) :initially 0 :resizable t))

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

(defun my-test2 ()
  (declare (xargs :guard t))
  (with-local-stobj foo$
    (mv-let (ans foo$)

      (with-local-stobj foo$2
        (mv-let (ans foo$ foo$2)
          (my-test foo$ foo$2)
          (mv ans foo$)))

      ans)))

(defun my-test3 ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj foo$
    (mv-let (ans foo$)
      (with-local-stobj foo$2
        (mv-let (ans foo$ foo$2)
          (my-test foo$ foo$2)
          (mv ans foo$)))
      ans)))

(local (in-theory (disable my-test my-test2 my-test3)))

(local
 (encapsulate ()
   (defconsts (*pre-ok* foo$ foo$2) (my-test foo$ foo$2)) (assert! *pre-ok*)
   (defconsts *pre-ok2* (my-test2)) (assert! *pre-ok2*)
   (defconst *pre-ok2b* (my-test2)) (assert! *pre-ok2b*)
   (defconsts *pre-ok3* (my-test3)) (assert! *pre-ok2*)
   (defconst *pre-ok3b* (my-test3)) (assert! *pre-ok3b*)
   (defthmd pre-crock (equal (mv-nth 0 (my-test foo$ foo$2)) t)
     :hints(("Goal" :in-theory (enable my-test))))
   (defthmd pre-crock2 (equal (my-test2) t))
   (defthmd pre-crock3 (equal (my-test3) t))))

(comp t)

(local
 (encapsulate ()
   (defconsts (*post-ok* foo$ foo$2) (my-test foo$ foo$2)) (assert! *post-ok*)
   (defconsts *post-ok2* (my-test2)) (assert! *post-ok2*)
   (defconst *post-ok2b* (my-test2)) (assert! *post-ok2b*)
   (defconsts *post-ok3* (my-test3)) (assert! *post-ok2*)
   (defconst *post-ok3b* (my-test3)) (assert! *post-ok3b*)
   (defthmd post-crock (equal (mv-nth 0 (my-test foo$ foo$2)) t)
     :hints(("Goal" :in-theory (enable my-test))))
   (defthmd post-crock2 (equal (my-test2) t))
   (defthmd post-crock3 (equal (my-test3) t))))
