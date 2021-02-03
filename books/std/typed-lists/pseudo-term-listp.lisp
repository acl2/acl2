; Standard Typed Lists Library
; Copyright (C) 2008-2014 Centaur Technology
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
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "ACL2")
(include-book "std/util/deflist" :dir :system)

(in-theory (disable pseudo-term-listp))

(defsection std/typed-lists/pseudo-term-listp
  :parents (pseudo-termp)
  :short "Lemmas about lists of @(see pseudo-termp)s, available in the @(see
std/typed-lists) library."

  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist pseudo-term-listp (x)
                (pseudo-termp x)
                :true-listp t
                :elementp-of-nil t
                :already-definedp t
                ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
                :parents nil)

  (defthm pseudo-term-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (remove-equal a x))))

  (defthm pseudo-term-listp-of-remove1-equal
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (remove1-equal a x))))

  (defthm pseudo-term-listp-of-make-list-ac
    ;; BOZO probably silly given REPEAT as the normal form...
    (equal (pseudo-term-listp (make-list-ac n x ac))
           (and (pseudo-term-listp ac)
                (or (pseudo-termp x)
                    (zp n)))))

  (defthm pseudo-term-listp-when-symbol-listp
    (implies (symbol-listp syms)
             (pseudo-term-listp syms))))
