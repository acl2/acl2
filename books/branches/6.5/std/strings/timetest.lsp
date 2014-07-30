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

(in-package "ACL2")
(include-book "abbrevs")

:q

;; 10 Million Substrings, 8.1 seconds, nothing allocated
(time (loop for i from 1 to 10000000 do
            (substrp "foo" "this is a string with foo in it")))

;; 10 Million Insensitive Substrings, 13.6 seconds, nothing allocated
(time (loop for i from 1 to 10000000 do
            (isubstrp "foo" "this is a string with foo in it")))

;; 10 Million Reversals, 19.6 seconds, 1.4 GB allocated
(time (loop for i from 1 to 10000000 do
            (reverse "this is a string with foo in it")))

;; 100 Million String< Compares, 5.5 seconds, nothing allocated
(time (loop for i from 1 to 100000000 do
            (string< "this foo" "this bar")))

;; 100 Million Istr< Compares, 15.4 seconds, nothing allocated
(time (loop for i from 1 to 100000000 do
            (istr< "this foo" "this bar")))


(defparameter *foo*
  (loop for i from 1 to 1000 nconc
        (list "foo" "bar" "baz")))

;; 1000 insensitive 3000-element string sort, 6.7 seconds, 500 MB allocated
(time (loop for i from 1 to 1000 do
            (istrsort *foo*)))



