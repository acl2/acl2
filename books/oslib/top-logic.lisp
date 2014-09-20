; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
(include-book "argv-logic")
(include-book "copy-logic")
(include-book "date-logic")
(include-book "dirname-logic")
(include-book "file-types-logic")
(include-book "getpid-logic")
(include-book "lisptype-logic")
(include-book "ls-logic")
(include-book "mkdir-logic")
(include-book "rmtree-logic")

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

<p>Please regard oslib as somewhat experimental.  In the near future we may try
to standardize the interfaces of oslib functions to make them more
predictable.</p>


<h3>Loading the library</h3>

<p>You can load the full library with:</p>

@({
   (include-book \"oslib/top\" :dir :system)
})

<p>But you can alternately just pick out the specific books that you want to
load.  The library has been arranged so that you can load only the logical
definitions without loading their associated raw Lisp code.  For instance:</p>

@({
    (include-book \"oslib/argv\" :dir :system)
      ;; -- requires a ttag, loads (argv) and its raw Lisp code

    (include-book \"oslib/argv-logic\" :dir :system)
      ;; -- gets the logical definition of (argv)
      ;; -- no ttag, but of course the resulting (argv) won't work yet
})

<p>Some users may find this to be useful, e.g., you can avoid trust tags in the
vast majority of your books, and only include the actual oslib raw Lisp code
when you're ready to run your ACL2 programs.</p>

<p>This paradigm is followed throughout the library.  For instance, you can load
all oslib functions (without trust tags) using:</p>

@({
    (include-book \"oslib/top-logic\" :dir :system)
})

<p>But the resulting definitions won't work until you include the regular
@('top') book.</p>")
