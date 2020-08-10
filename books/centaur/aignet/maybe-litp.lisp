; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "centaur/satlink/litp" :dir :system)

(defsection maybe-litp
  :parents (litp)
  :short "Recognizer for lits and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-litp'), then either it is a @(see litp) or nothing.</p>"

  (defund-inline maybe-litp (x)
    (declare (xargs :guard t))
    (or (not x)
        (litp x)))

  (local (in-theory (enable maybe-litp)))

  (defthm maybe-litp-compound-recognizer
    (equal (maybe-litp x)
           (or (not x)
               (litp x)))
    :rule-classes :compound-recognizer))

(defsection maybe-lit-fix
  :parents (fty::basetypes maybe-litp)
  :short "@(call maybe-lit-fix) is the identity for @(see maybe-litp)s, or
  coerces any non-@(see litp) to @('nil')."
  :long "<p>Performance note.  In the execution this is just an inlined
  identity function, i.e., it should have zero runtime cost.</p>"

  (defund-inline maybe-lit-fix (x)
    (declare (xargs :guard (maybe-litp x)
                    :guard-hints (("Goal" :in-theory (e/d (maybe-litp)
                                                          ())))))
    (mbe :logic (if x (lit-fix x) nil)
         :exec x))

  (local (in-theory (enable maybe-litp maybe-lit-fix)))

  (defthm maybe-litp-of-maybe-lit-fix
    (maybe-litp (maybe-lit-fix x))
    :rule-classes (:rewrite :type-prescription))

  (defthm maybe-lit-fix-when-maybe-litp
    (implies (maybe-litp x)
             (equal (maybe-lit-fix x) x)))

  (defthm maybe-lit-fix-under-iff
    (iff (maybe-lit-fix x) x))

  (defthm maybe-lit-fix-under-lit-equiv
    (lit-equiv (maybe-lit-fix x) x)
    :hints(("Goal" :in-theory (enable maybe-lit-fix)))))
