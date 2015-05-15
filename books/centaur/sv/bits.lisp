; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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

(in-package "SV")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)

(defthm b-and-equal-1-in-hyp
  (implies (syntaxp (or (acl2::rewriting-negative-literal-fn `(equal (acl2::b-and$inline ,x ,y) '1) mfc state)
                        (acl2::rewriting-negative-literal-fn `(equal '1 (acl2::b-and$inline ,x ,y)) mfc state)))
           (equal (equal (acl2::b-and x y) 1)
                  (and (equal x 1) (equal y 1))))
  :hints(("Goal" :in-theory (enable acl2::b-and))))

(defthm b-and-equal-0-in-concl
  (implies (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (acl2::b-and$inline ,x ,y) '0) mfc state)
                        (acl2::rewriting-positive-literal-fn `(equal '0 (acl2::b-and$inline ,x ,y)) mfc state)))
           (equal (equal (acl2::b-and x y) 0)
                  (or (not (equal x 1)) (not (equal y 1)))))
  :hints(("Goal" :in-theory (enable acl2::b-and))))

(defthm b-ior-equal-1-in-concl
  (implies (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (acl2::b-ior$inline ,x ,y) '1) mfc state)
                        (acl2::rewriting-positive-literal-fn `(equal '1 (acl2::b-ior$inline ,x ,y)) mfc state)))
           (equal (equal (acl2::b-ior x y) 1)
                  (or (equal x 1) (equal y 1))))
  :hints(("Goal" :in-theory (enable acl2::b-ior))))

(defthm b-ior-equal-0-in-concl
  (implies (syntaxp (or (acl2::rewriting-negative-literal-fn `(equal (acl2::b-ior$inline ,x ,y) '0) mfc state)
                        (acl2::rewriting-negative-literal-fn `(equal '0 (acl2::b-ior$inline ,x ,y)) mfc state)))
           (equal (equal (acl2::b-ior x y) 0)
                  (and (not (equal x 1)) (not (equal y 1)))))
  :hints(("Goal" :in-theory (enable acl2::b-ior))))

(defthm b-not-equal-0
  (equal (equal (acl2::b-not x) 0)
         (equal x 1))
  :hints(("Goal" :in-theory (enable acl2::b-not))))

(defthm b-not-equal-1
  (equal (equal (acl2::b-not x) 1)
         (not (equal x 1)))
  :hints(("Goal" :in-theory (enable acl2::b-not))))

(defthm bool->bit-equal-1
  (iff (equal (bool->bit x) 1)
       x)
  :hints(("Goal" :in-theory (enable bool->bit))))

(defthm bool->bit-equal-0
  (equal (equal (bool->bit x) 0)
         (not x))
  :hints(("Goal" :in-theory (enable bool->bit))))
