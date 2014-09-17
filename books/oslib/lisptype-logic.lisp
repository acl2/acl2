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

(define lisp-type (&optional (state 'state))
  :returns (mv (description stringp :rule-classes :type-prescription
                            "E.g., @('\"Clozure Common Lisp\"').")
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get a host-Lisp specific string describing what kind of Common Lisp
implementation this is."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution, we call the Common Lisp function @('lisp-implementation-type'), and
return whatever string it produces.</p>

<p>Note that the Common Lisp @('lisp-implementation-type') function is
technically allowed to return @('nil'); in this case we return the empty
string.</p>"

  (b* (((mv err val state) (read-acl2-oracle state))
       (description (if (and (not err)
                             (stringp val))
                        val
                      "")))
    (mv description state)))

(define lisp-version (&optional (state 'state))
  :returns (mv (description stringp :rule-classes :type-prescription
                            "E.g., @('\"Version 1.9-r15996  (LinuxX8664)\"').")
               (state state-p1 :hyp (force (state-p1 state))))
  :short "Get a host-Lisp specific string describing the version number for
this Common Lisp implementation."

  :long "<p>In the logic this function reads from the ACL2 oracle.  In the
execution, we call the Common Lisp function @('lisp-implementation-version'),
and return the string it produces.</p>

<p>Note that the Common Lisp @('lisp-implementation-type') function is
technically allowed to return @('nil'); in this case we return the empty
string.</p>"

  (b* (((mv err val state) (read-acl2-oracle state))
       (description (if (and (not err)
                             (stringp val))
                        val
                      "")))
    (mv description state)))


