; Set Difference Lemmas
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
(include-book "xdoc/top" :dir :system)
(local (include-book "sets"))
(local (include-book "intersectp"))

(local (in-theory (enable set-difference-equal)))

(defsection std/lists/set-difference
  :parents (std/lists set-difference$)
  :short "Lemmas about @(see set-difference$) available in the @(see std/lists)
library."

  (defthm set-difference-equal-when-atom
    (implies (atom x)
             (equal (set-difference-equal x y)
                    nil)))

  (defthm set-difference-equal-of-cons
    (equal (set-difference-equal (cons a x) y)
           (if (member-equal a y)
               (set-difference-equal x y)
             (cons a (set-difference-equal x y)))))

  (defthm set-difference-equal-when-subsetp-equal
    (implies (subsetp-equal x y)
             (equal (set-difference-equal x y)
                    nil)))

  (defthm set-difference-equal-of-self
    (equal (set-difference-equal x x)
           nil))

  (defthm empty-intersect-with-difference-of-self
    (not (intersectp-equal a (set-difference-equal b a))))

  (defthm no-duplicatesp-of-set-difference-equal
    (implies
     (no-duplicatesp-equal l1)
     (no-duplicatesp-equal (set-difference-equal l1 l2)))))
