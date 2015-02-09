; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")

; This is an empty book which is included in cert.acl2 in order to consolidate
; all of our portcullis commands into a single, usually-redundant include-book
; command.  This simply improves the efficiency of our build process.

(include-book "tools/safe-case" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "tools/rulesets" :dir :system)

(defmacro VL2014::case (&rest args)
  `(ACL2::safe-case . ,args))

(defmacro VL2014::concatenate (&rest args)
  `(STR::fast-concatenate . ,args))

(defmacro VL2014::enable (&rest args)
  `(ACL2::enable* . ,args))

(defmacro VL2014::disable (&rest args)
  `(ACL2::disable* . ,args))

(defmacro VL2014::e/d (&rest args)
  `(ACL2::e/d* . ,args))

