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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "strline")
(include-book "std/testing/assert" :dir :system)


(acl2::assert! (equal "foo" (strline 1 "foo
bar
baz")))

(acl2::assert! (equal "bar" (strline 2 "foo
bar
baz")))

(acl2::assert! (equal "baz" (strline 3 "foo
bar
baz")))

(acl2::assert! (equal "" (strline 4 "foo
bar
baz")))


(defconst *txt* "Line 1
Line 2
Line 3
Line 4
Line 5
Line 6")

(assert! (equal (strlines 1 1 *txt*) "Line 1
"))

(assert! (equal (strlines 1 2 *txt*) "Line 1
Line 2
"))

(assert! (equal (strlines 1 3 *txt*) "Line 1
Line 2
Line 3
"))

(assert! (equal (strlines 1 100 *txt*) *txt*))

(assert! (equal (strlines 2 2 *txt*) "Line 2
"))

(assert! (equal (strlines 2 3 *txt*) "Line 2
Line 3
"))

(assert! (equal (strlines 5 6 *txt*) "Line 5
Line 6")) ;; Note: no newline after line 6, so none is returned here

(assert! (equal (strlines 5 1000 *txt*) "Line 5
Line 6")) ;; Note: no newline after line 6, so none is returned here

(assert! (equal (strlines 5 6 (concatenate 'string *txt* "
")) "Line 5
Line 6
")) ;; Newline, so it's returned

(assert! (equal (strlines 5 1000 (concatenate 'string *txt* "
")) "Line 5
Line 6
")) ;; Newline, so it's returned

(assert! (equal (strlines 7 1000 *txt*) ""))
