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

(define rmtree
  :short "Recursively delete files, like the shell command @('rm -rf'), and
return a success indicator so you can recover from errors."
 ((dir "The path that you want to remove, e.g., @('./foo/bar')" stringp)
  &optional (state 'state))
 :returns (mv (successp booleanp
                        :rule-classes :type-prescription
                        "Success indicator.  We might fail due to file system
                          permissions, illegal file names, etc.")
              (state state-p1
                     :hyp (force (state-p1 state))))
  :long "<p>In the logic this function reads from the ACL2 oracle to determine
if it succeeds.  In the execution, we attempt to delete the requested path, and
detect errors.</p>"
  :ignore-ok t
  (b* ((- (raise "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       (okp (and (not err)
                 (booleanp val)
                 val)))
    (mv okp state)))

(define rmtree! ((path stringp) &key (state 'state))
  :short "Recursively delete files, like the shell command @('rm -rf'), causing
a hard error on any failure."
  (b* (((mv successp state) (rmtree path))
       ((unless successp)
        (raise "Error removing ~s0." path)
        state))
    state))