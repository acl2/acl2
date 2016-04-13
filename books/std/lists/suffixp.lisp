; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defsection suffixp
  :parents (std/lists)
  :short "@(call suffixp) determines if the list @('x') occurs at the end of
the list @('y')."
  :long "<p>For example:</p>

  @({
      (suffixp '(3 4 5) '(1 2 3 4 5)) == t
      (suffixp '(a b c) '(1 2 3 4 5)) == nil
  })

  <p>Note that the check is carried out using @('equal'), so the final cdr
  of the list is considered relevant.  That is,</p>

  @({
      (suffixp '(3 4 5 . 6) '(1 2 3 4 5 . 6)) = t
      (suffixp '(3 4 5)     '(1 2 3 4 5 . 6)) = nil
  })"

  (defund suffixp (x y)
    (declare (xargs :guard t))
    (or (equal x y)
        (and (consp y)
             (suffixp x (cdr y)))))

  (local (in-theory (enable suffixp)))

  (defthm suffixp-of-cons-right
    (equal (suffixp a (cons c b))
           (or (equal a (cons c b))
               (suffixp a b))))

  (defthm not-suffixp-of-cons-left
    (implies (not (suffixp a b))
             (not (suffixp (cons c a) b))))

  (defthm suffixp-of-self
    (suffixp x x))

  (defthm suffixp-transitive
    (implies (and (suffixp b c)
                  (suffixp a b))
             (suffixp a c)))

  "<p>Note that the following is disabled by default:</p>"

  (defthmd suffixp-equals-nthcdr
    (equal (suffixp x y)
           (equal x (nthcdr (- (len y) (len x)) y)))))

