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
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "std/util/deflist" :dir :system)

(in-theory (disable nat-listp
                    nat-listp-of-append-weak))

(defsection std/typed-lists/nat-listp
  :parents (nat-listp)
  :short "Lemmas about @(see nat-listp) available in the @(see std/typed-lists)
library."

  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>

<p>BOZO some additional lemmas are found in @('arithmetic/nat-listp').</p>"

  (std::deflist nat-listp (x)
    (natp x)
    :true-listp t
    :elementp-of-nil nil
    :already-definedp t
    ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
    :parents nil)

  (defthm integerp-of-car-when-nat-listp
    ;; Gross, but maybe useful when natp is enabled?
    (implies (nat-listp x)
             (equal (integerp (car x))
                    (consp x))))

  (defthm lower-bound-of-car-when-nat-listp
    (implies (nat-listp x)
             (<= 0 (car x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :induct (len x))))

  ;; This rewrite is fine, but the arithmetic/nat-listp book now has both
  ;; a rewrite and a compound recognizer, so there's no reason to include this.
  ;; (defthm true-listp-when-nat-listp-rewrite
  ;;   ;; The deflist gives us a compound-recognizer, but in this case having a
  ;;   ;; rewrite rule seems worth it.
  ;;   (implies (nat-listp x)
  ;;            (true-listp x))
  ;;   :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm nat-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (nat-listp x)
             (nat-listp (remove-equal a x))))

  (defthm nat-listp-of-make-list-ac
    ;; BOZO probably silly given REPEAT as the normal form...
    (equal (nat-listp (make-list-ac n x ac))
           (and (nat-listp ac)
                (or (natp x)
                    (zp n)))))

  (defthm eqlable-listp-when-nat-listp
    ;; Useful for the guards of MEMBER on nat-listp's.
    ;; BOZO should this just be a TAU rule?
    (implies (nat-listp x)
             (eqlable-listp x))))
