; Intersectp Lemmas
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
(include-book "list-defuns")
(include-book "xdoc/top" :dir :system)
(local (include-book "sets"))

(local (in-theory (enable intersection$ intersectp)))

(defsection std/lists/intersectp
  :parents (std/lists intersectp)
  :short "Lemmas about @(see intersectp) available in the @(see std/lists)
library."

  (defthm intersectp-equal-of-atom-left
    (implies (atom x)
             (equal (intersectp-equal x y)
                    nil)))

  (defthm intersectp-equal-of-atom-right
    (implies (atom y)
             (equal (intersectp-equal x y)
                    nil)))

  (defthm intersect-equal-of-cons-left
    (equal (intersectp-equal (cons a x) y)
           (if (member-equal a y)
               t
             (intersectp-equal x y))))

  (defthm intersectp-equal-of-cons-right
    (equal (intersectp-equal x (cons a y))
           (if (member-equal a x)
               t
             (intersectp-equal x y))))

  "<h5>Basic set reasoning</h5>"

  (defcong set-equiv equal (intersectp x y) 1)
  (defcong set-equiv equal (intersectp x y) 2)

  (defthm intersectp-of-self
    (equal (intersectp x x)
           (consp x))))
