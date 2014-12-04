; Centaur Miscellaneous Books
; Copyright (C) 2014 Centaur Technology
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
(include-book "tools/include-raw" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "std/util/define" :dir :system)

(define spacewalk ()
  :parents (debugging)
  :short "A tool that analyzes the memory usage in your ACL2 session. (CCL
Only)"

  :long "<p>This is a debugging aide that collects and prints some space usage
information to the console.  Usage is simply:</p>

@({
    (include-book \"centaur/misc/spacewalk\" :dir :system)
    :spacewalk
})

<p>You should almost certainly <b>not</b> include the spacewalk book in
ordinary ACL2 books, since it will not help you prove anything.  You could
include it in your @(see acl2-customization) file or similar.  We may
eventually try to integrate it into the @(see Sidekick).</p>

<p>Logically @('(spacewalk)') just returns @('nil').  Under the hood, we call
on various low-level CCL functions to analyze memory usage of various ACL2 data
structures.</p>"

  #+Clozure
  (raise "Under the hood definition not yet installed?")
  #-Clozure
  (cw "Spacewalk is not implemented on this lisp.~%"))

(defttag :spacewalk)

; (depends-on "spacewalk-raw.lsp")
#+Clozure
(include-raw "spacewalk-raw.lsp" :host-readtable t)
