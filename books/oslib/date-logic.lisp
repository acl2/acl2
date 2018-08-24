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
(include-book "read-acl2-oracle")
(include-book "std/util/define" :dir :system)
(local (xdoc::set-default-parents oslib))

(define date (&optional (state 'state))
  :returns (mv (datestamp stringp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current datestamp, like \"November 17, 2010 10:25:33\"."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution we use Common Lisp's @('get-decoded-time') function to figure out
what the current date and time is.  We think this <i>should</i> work on any
Common Lisp system.</p>

<p>See also @(see universal-time), which returns an integer representation of
the current time.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (stringp val))
        (mv val state)
      (mv "Error reading date." state))))

(define universal-time (&optional (state 'state))
  :returns (mv (seconds natp :rule-classes :type-prescription)
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get the current timestamp as a natural number, specifically the
number of seconds since 00:00 January 1, 1900 GMT.  Note well that this is
<b>not</b> the Unix epoch."

  :long "<p>In the logic this function reads from the ACL2 oracle, so there is
no logical guarantee that it will return successive times.  (Indeed, the user
could likely change their computer's clock so that it would report earlier
times.)</p>

<p>In the execution, we use Common Lisp's @('get-universal-time') function to
figure out the current time in seconds since the start of 1900.</p>

<p>This is, for whatever reason, a different starting date than the Unix
epoch (which records time since the start of 1970).  You should therefore be
careful if you need to compare this timestamp against those produced by
external tools.</p>"

  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state)))
    (if (and (not err)
             (natp val))
        (mv val state)
      (mv 0 state))))
