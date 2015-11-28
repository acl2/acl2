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

; defxdoc-raw.lisp
;
; This book requires a TTAG.  You should typically not need to include it
; directly unless you want to document some raw-lisp code with xdoc.

(in-package "XDOC")
(include-book "base")
(include-book "tools/include-raw" :dir :system)
; (depends-on "defxdoc-raw-impl.lsp")
(set-state-ok t)

(defttag :xdoc)

(defun all-xdoc-topics (state)
  (declare (xargs :stobjs state :verify-guards t))
  (prog2$
   (er hard? 'all-xdoc-topics "all-xdoc-topics not yet defined.")
   (read-acl2-oracle state)))

(acl2::include-raw "defxdoc-raw-impl.lsp")
