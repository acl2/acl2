; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "formals")
(include-book "std/testing/assert" :dir :system)


(assert! (equal (remove-macro-args 'f '(a b c) nil)
                '(a b c)))
(assert! (equal (remove-macro-args 'f '(a b c &key d e) nil)
                '(a b c d e)))
(assert! (equal (remove-macro-args 'f '(a b c &key d &optional e) nil)
                '(a b c d e)))
(assert! (equal (remove-macro-args 'f '(a b c &optional d e) nil)
                '(a b c d e)))
(assert! (equal (remove-macro-args 'f '(a b c &key (d true-listp) e) nil)
                ;; true-listp is unquoted so it's a guard
                '(a b c (d true-listp) e)))
(assert! (equal (remove-macro-args 'f '(a b c &key (d 'true-listp) e) nil)
                ;; 'true-listp is quoted so it's a default value
                '(a b c d e)))
(assert! (equal (remove-macro-args 'f '(a b c &key (d "foo") e) nil)
                ;; "foo" is unquoted so it's an xdoc string
                '(a b c (d "foo") e)))
(assert! (equal (remove-macro-args 'f '(a b c &key (d '"foo") e) nil)
                ;; '"foo" is quoted so it's a default value
                '(a b c d e)))
(assert! (equal (remove-macro-args 'f '(a b c &key ((d atom) '3) (e true-listp)) nil)
                '(a b c (d atom) (e true-listp))))


(assert! (equal (formals-for-macro 'f '(a b c) nil)
                '(a b c)))
(assert! (equal (formals-for-macro 'f '(a b c &key d e) nil)
                '(a b c &key d e)))
(assert! (equal (formals-for-macro 'f '(a b c &key d &optional e) nil)
                '(a b c &key d &optional e)))
(assert! (equal (formals-for-macro 'f '(a b c &optional d e) nil)
                '(a b c &optional d e)))
(assert! (equal (formals-for-macro 'f '(a b c &key (d true-listp) e) nil)
                ;; true-listp is unquoted so it's a guard
                '(a b c &key d e)))
(assert! (equal (formals-for-macro 'f '(a b c &key (d 'true-listp) e) nil)
                ;; 'true-listp is quoted so it's a default value
                '(a b c &key (d 'true-listp) e)))
(assert! (equal (formals-for-macro 'f '(a b c &key (d "foo") e) nil)
                ;; "foo" is unquoted so it's an xdoc string
                '(a b c &key d e)))
(assert! (equal (formals-for-macro 'f '(a b c &key (d '"foo") e) nil)
                ;; '"foo" is quoted so it's a default value
                '(a b c &key (d '"foo") e)))
(assert! (equal (formals-for-macro 'f '(a b c &key ((d atom) '3) (e true-listp)) nil)
                '(a b c &key (d '3) e)))


(assert! (equal (make-wrapper-macro 'foo 'foo-fn '(x y z))
                `(defmacro foo (x y z)
                   (list 'foo-fn x y z))))
(assert! (equal (make-wrapper-macro 'foo 'foo-fn '(x y &optional z))
                `(defmacro foo (x y &optional z)
                   (list 'foo-fn x y z))))
(assert! (equal (make-wrapper-macro 'foo 'foo-fn '(x y &optional (z '3)))
                `(defmacro foo (x y &optional (z '3))
                   (list 'foo-fn x y z))))
(assert! (equal (make-wrapper-macro 'foo 'foo-fn '(x y &key (z '3)))
                `(defmacro foo (x y &key (z '3))
                   (list 'foo-fn x y z))))
(assert! (equal (make-wrapper-macro 'foo 'foo-fn '(x y &optional (a '5) &key (z '3)))
                `(defmacro foo (x y &optional (a '5) &key (z '3))
                   (list 'foo-fn x y a z))))
