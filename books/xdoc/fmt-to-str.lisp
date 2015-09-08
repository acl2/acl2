; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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


; fmt-to-str.lisp -- alternative to fmt-to-string with narrower margins
; and downcased symbols

(in-package "XDOC")
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/pretty-program" :dir :system)
(include-book "str")
(set-state-ok t)
(program)

(defun fmt-to-str (x base-pkg)
  ;; Use ACL2's fancy new string-printing stuff to do pretty-printing
  (b* ((config (str::make-printconfig :hard-right-margin 68
                                      :print-lowercase t
                                      :home-package base-pkg)))
    (str::pretty x :config config)))

(defun fmt-and-encode-to-acc (x base-pkg acc)
  (b* ((str (fmt-to-str x base-pkg))
       (acc (simple-html-encode-str str 0 (length str) acc)))
    acc))

