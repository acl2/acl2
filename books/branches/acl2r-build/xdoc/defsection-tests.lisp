; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "top")

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


