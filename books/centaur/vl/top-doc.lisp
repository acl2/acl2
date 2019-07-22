; Copyright (C) 2018 Centaur Technology
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
; Original author (this file): Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "xdoc/archive-matching-topics" :dir :system)

(local (include-book "kit/top"))
(local (include-book "lint/lvaluecheck"))
(local (include-book "transforms/eliminitial"))
(local (include-book "transforms/problem-mods"))
(local (include-book "doc"))
(local (include-book "mlib/remove-bad")) ;; hack -- only included by sv/vl/top

(xdoc::archive-matching-topics
 (or (str::strprefixp "[books]/centaur/vl/" (cdr (assoc :from x)))
     ;; hack -- this book isn't included in sv, probably should be moved to vl/lint dir
     (equal (cdr (assoc :from x)) "[books]/centaur/sv/vl/use-set.lisp")
     (equal (cdr (assoc :from x)) "[defxdoc-raw]"))) ;; for topics defined using defxdoc-raw
