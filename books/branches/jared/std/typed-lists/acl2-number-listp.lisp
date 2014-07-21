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

(in-package "ACL2")
(include-book "std/util/deflist" :dir :system)

(in-theory (disable acl2-number-listp))

(defsection std/typed-lists/acl2-number-listp
  :parents (acl2-number-listp)
  :short "Lemmas about @(see acl2-number-listp) available in the @(see
std/typed-lists) library."

  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist acl2-number-listp (x)
                (acl2-numberp x)
                :true-listp t
                :elementp-of-nil nil
                :already-definedp t
                ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
                :parents nil)

  (defthm acl2-number-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (acl2-number-listp x)
             (acl2-number-listp (remove-equal a x))))

  (defthm acl2-number-listp-of-make-list-ac
    ;; BOZO probably silly given REPEAT as the normal form...
    (equal (acl2-number-listp (make-list-ac n x ac))
           (and (acl2-number-listp ac)
                (or (acl2-numberp x)
                    (zp n)))))

  (defthm eqlable-listp-when-acl2-number-listp
    ;; Useful for the guards of MEMBER on acl2-number-listp's.
    ;; BOZO should this just be a TAU rule?
    (implies (acl2-number-listp x)
             (eqlable-listp x))))
