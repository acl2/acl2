; Utility for including various arithmetic books.
; Copyright (C) 2015, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc include-an-arithmetic-book
  :parents (arithmetic)
  :short "Macros for including arithmetic books"
  :long "<table>
 <tr><th>Primitive</th><th>Book and Config</th></tr>
 <tr><td>@('arithmetic')</td><td>@('arithmetic/top-with-meta')</td></tr>
 <tr><td>@('arithmetic-5')</td><td>@('arithmetic-5/top')</td></tr>
 <tr><td>@('arithmetic-5-nonlinear-weak')</td><td>@('arithmetic-5/top') with weak
      nonlinear hint settings</td></tr>
 <tr><td>@('arithmetic-5-nonlinear')</td><td>@('arithmetic-5/top') with stronger
      nonlinear hint settings</td></tr>
 </table>

 Note that it can be reasonable to only include this book locally, since these
 forms can often only occur in lemmas local to the book performing the
 including.")

; It might be nice to create an xdoc topic for each of the following
; primitives, but then we'd need two "arithmetic" topics.  It doesn't seem
; worth it.

(defmacro arithmetic ()
  `(include-book "arithmetic/top-with-meta" :dir :system))

(defmacro arithmetic-5 ()
  `(include-book "arithmetic-5/top" :dir :system))

(defmacro arithmetic-5-nonlinear-weak ()
  '(progn
     (include-book "arithmetic-5/top" :dir :system)
     (set-default-hints '((ACL2::nonlinearp-default-hint
                           ACL2::stable-under-simplificationp ACL2::hist
                           ACL2::pspv)))))

(defmacro arithmetic-5-nonlinear ()
  '(progn
     (include-book "arithmetic-5/top" :dir :system)
     (set-default-hints '((ACL2::nonlinearp-default-hint++
                           ACL2::id ACL2::stable-under-simplificationp ACL2::hist nil)))))
