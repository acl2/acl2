; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

(in-package "XDOC")
(include-book "../top")

(defxdoc test :short "Test of defsection")

(defsection foo1
  :parents (test)
  :autodoc nil
  (defun foo1 (x) x))

(defsection foo2
  :parents (test)
  (defun foo2 (x) x))

(defsection foo3
  :parents (test)
  :short "Section for foo3"
  :long "<p>Foo3 is wonderful.</p>"

  (defund foo3 (x) (+ 1 x))

  (local (in-theory (enable foo3)))

  (defthm natp-of-foo3
    (implies (natp x)
             (natp (foo3 x))))

  (local (defthm foo3-lemma
           (implies (equal x 3)
                    (equal (foo3 x) 4))))

  (defmacro foo3-alias (x)
    `(foo3 ,x))

  (defsection bar
    :parents (test)
    :short "Section for bar"
    :long "<p>Bar is wonderful.</p>"
    (defund bar (x) (+ 2 x))))

;; BOZO the theorems in the nested section are leaking out into the superior
;; section... ugh.


(defsection foo3-advanced
  :extension foo3

  (local (in-theory (enable foo3)))

  (defthm posp-of-foo3
    (implies (natp x)
             (posp (foo3 x))))

  (defthm oddp-of-foo3
    (implies (evenp x)
             (oddp (foo3 x)))))


(defsection foo3-advanced-more
  :extension foo3
  :long "<h3>Even more theorems!</h3>"

  (local (in-theory (enable foo3)))

  (defthm integerp-of-foo3
    (implies (integerp x)
             (integerp (foo3 x)))))


