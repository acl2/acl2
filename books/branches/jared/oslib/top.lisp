; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
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

(in-package "OSLIB")

(include-book "argv")
(include-book "catpath")
(include-book "date")
(include-book "getpid")
(include-book "lisptype")
(include-book "ls")
(include-book "mkdir")
(include-book "file-types")
(include-book "tempfile")
(include-book "rmtree")

(defxdoc oslib
  :parents (acl2::interfacing-tools)
  :short "Operating System Utilities Library"

  :long "<p>This is a collection of ACL2 functions that allow you to do various
basic operating-system related tasks, e.g., you can get the current PID or user
name, file listings, etc.</p>

<p>Almost everything here necessarily requires a trust tag, because it is
implemented in raw Lisp.  We believe we have connected this functionality to
ACL2 in a sound way, using @(see read-acl2-oracle).</p>

<p>The library is far from complete since we tend to extend it only as the need
arises.  Most functions are not implemented on all Lisp and operating system
combinations, and will simply fail on unsupported Lisps.</p>


<h3>Loading the library</h3>

<p>You can load the full library with:</p>

@({
 (include-book \"oslib/top\" :dir :system)
})

<p>But it is often better, in this case, to just pick and choose the specific
books you want to load.</p>")




