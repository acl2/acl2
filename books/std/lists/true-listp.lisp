; True-Listp Lemmas
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "xdoc/top" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(in-theory (disable true-listp))

(defsection std/lists/true-listp
  :parents (std/lists true-listp)
  :short "Lemmas about @(see true-listp) available in the @(see std/lists)
library."

  :long "<p>Note: the list of lemmas below is quite incomplete.  For instance,
the @(see true-listp) rule about @(see append) will be found in the
documentation for @(see std/lists/append), instead of here.</p>"

  (local (in-theory (enable true-listp)))

  (defthm true-listp-when-atom
    (implies (atom x)
             (equal (true-listp x)
                    (not x))))

  (defthm true-listp-of-cons
    (equal (true-listp (cons a x))
           (true-listp x)))

  (defthm consp-under-iff-when-true-listp
    ;; BOZO even with the backchain limit, this rule can get too expensive.
    (implies (true-listp x)
             (iff (consp x)
                  x))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


