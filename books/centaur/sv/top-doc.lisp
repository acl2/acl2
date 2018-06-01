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

(in-package "SV")

(include-book "xdoc/archive-matching-topics" :dir :system)
(local (include-book "build/ifdef" :dir :system))
(local (include-book "top"))

(local (acl2::ifdef "OS_HAS_GLUCOSE"
                    (include-book "centaur/sv/tutorial/alu" :dir :system)
                    (include-book "centaur/sv/tutorial/boothpipe" :dir :system)

                    (acl2::ifdef "OS_HAS_IPASIR"
                                 (include-book "centaur/sv/tutorial/sums" :dir :system)
                                 :endif)
                    :endif))
(local (acl2::ifndef "OS_HAS_GLUCOSE"
                     ;; This is needed to avoid broken topic link errors
                     (defxdoc sv::sv-tutorial
                       :parents (sv::sv)
                       :short "Stub for missing topic"
                       :long "<p>This topic was omitted from the manual because it is in a
book that depends on Glucose being installed.</p>")
                     (defxdoc sv::stvs-and-testing
                       :parents (sv::sv-tutorial)
                       :short "Stub for missing topic"
                       :long "<p>This topic was omitted from the manual because it is in a
book that depends on Glucose being installed.</p>")
                     :endif))


(xdoc::archive-matching-topics
 (str::strprefixp "[books]/centaur/sv/" (cdr (assoc :from x))))
