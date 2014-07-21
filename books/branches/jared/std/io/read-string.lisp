; Standard IO Library
; read-string.lisp
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

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "tools/include-raw" :dir :system)
(local (include-book "oslib/read-acl2-oracle" :dir :system))

(define read-string
  :parents (std/io)
  :short "Parse a string into s-expressions, by using Common Lisp's @('read')
under the hood. (requires a ttag)"
  ((str stringp "The string to parse.")
   &key
   (state 'state))
  :returns (mv (errmsg  "An error @(see msg) on failure, e.g., parse errors;
                         or @('nil') on success.")
               (objects "The list of objects parsed from @('str').")
               (state   state-p1 :hyp (state-p1 state)))

  :long "<p>In the logic we just read the oracle to decide if parsing will
succeed or fail.  So you can never prove any relationship between the input
@('str') and the resulting s-expressions that you get out.</p>

<p>In the execution, we turn the string into a Common Lisp input stream and try
to parse it using @('read'), so that full Common Lisp syntax is permitted.  If
we are able to successfully parse objects until EOF is reached, we return
success and the list of objects we read.</p>

<p>Jared thinks this may be sound.  See read-string-tests.lisp for some obvious
attempts to cause unsoundness.</p>"

  (declare (ignorable str))
  (b* ((- (raise "Raw lisp definition not installed?"))
       ((mv err1 errmsg? state) (read-acl2-oracle state))
       ((mv err2 objects state) (read-acl2-oracle state))
       ((when (or err1 err2))
        (mv (msg "Reading oracle failed.") nil state))
       ((when errmsg?)
        (mv errmsg? nil state)))
    (mv nil objects state)))

(defttag :read-string)

; (depends-on "read-string-raw.lsp")
(include-raw "read-string-raw.lsp")
