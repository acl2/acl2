; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

;; compatibility.lisp
;; Macros for compatibility with old names
;;
;; bzo (jcd) - we want to eventually remove this file and switch to using the
;; standard names.

(in-package "CPATH")
(include-book "../alists/top")

(defmacro keys (x)
  `(strip-cars ,x))

(add-macro-alias keys strip-cars)

(defmacro vals (x)
  `(strip-cdrs ,x))

(add-macro-alias vals strip-cdrs)

(defmacro clr-key (k x)
  `(ALIST::clearkey ,k ,x))

(add-macro-alias clr-key ALIST::clearkey)

(defmacro remove-shadowed-pairs (x)
  `(ALIST::deshadow ,x))

(add-macro-alias remove-shadowed-pairs ALIST::deshadow)

(defmacro range (x)
  `(vals (remove-shadowed-pairs ,x)))

(defmacro pre-image-aux (k x)
  `(ALIST::preimage-aux ,k ,x))

(add-macro-alias pre-image-aux ALIST::preimage-aux)

(defmacro pre-image (k x)
  `(ALIST::preimage ,k ,x))

(add-macro-alias pre-image ALIST::preimage)
