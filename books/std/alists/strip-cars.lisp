; Standard Association Lists Library
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "../lists/list-defuns")
(local (include-book "../lists/take"))

(local (in-theory (enable strip-cars)))

(local (defthm take-of-nil
         (equal (take n nil)
                (replicate n nil))
         :hints(("Goal" :in-theory (enable replicate)))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil)
                nil)))

(defsection std/alists/strip-cars
  :parents (std/alists strip-cars)
  :short "Lemmas about @(see strip-cars) available in the @(see std/alists)
library."

  :long "<p>Note that @('strip-cars') is a \"traditional\" alist function: it
has an @(see alistp) guard and fails to respect the non-alist convention.  We
generally prefer to work with @(see alist-keys) instead.</p>

<p>Even so, we provide many lemmas for working with @('strip-cars'), in case
for some reason that's what you want to do.</p>"

  (defthm strip-cars-when-atom
    (implies (atom x)
             (equal (strip-cars x)
                    nil)))

  (defthm strip-cars-of-cons
    (equal (strip-cars (cons a x))
           (cons (car a)
                 (strip-cars x))))

  (defthm len-of-strip-cars
    (equal (len (strip-cars x))
           (len x)))

  (defthm consp-of-strip-cars
    (equal (consp (strip-cars x))
           (consp x)))

  (defthm car-of-strip-cars
    (equal (car (strip-cars x))
           (car (car x))))

  (defthm cdr-of-strip-cars
    (equal (cdr (strip-cars x))
           (strip-cars (cdr x))))

  (defthm strip-cars-under-iff
    (iff (strip-cars x)
         (consp x)))

  (defthm strip-cars-of-list-fix
    (equal (strip-cars (list-fix x))
           (strip-cars x))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defcong list-equiv equal (strip-cars x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (strip-cars-of-list-fix))
            :use ((:instance strip-cars-of-list-fix (x x))
                  (:instance strip-cars-of-list-fix (x x-equiv))))))

  (encapsulate
    ()
    (local (defthm l1
             (implies (and (member-equal a x)
                           (not (consp a)))
                      (member-equal nil (strip-cars x)))))

    (local (defthm l2
             (implies (member-equal (cons a b) x)
                      (member-equal a (strip-cars x)))))

    (local (defthm l3
             (implies (and (subsetp x y)
                           (member a x))
                      (member (car a) (strip-cars y)))
             :hints(("Goal" :induct (len x)))))

    (local (defthm l4
             (implies (subsetp x y)
                      (subsetp (strip-cars x) (strip-cars y)))
             :hints(("Goal" :induct (len x)))))

    (defcong set-equiv set-equiv (strip-cars x) 1
      :hints(("Goal" :in-theory (enable set-equiv)))))

  (defthm strip-cars-of-append
    (equal (strip-cars (append x y))
           (append (strip-cars x)
                   (strip-cars y))))

  (defthm strip-cars-of-rev
    (equal (strip-cars (rev x))
           (rev (strip-cars x)))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm strip-cars-of-revappend
    (equal (strip-cars (revappend x y))
           (revappend (strip-cars x)
                      (strip-cars y))))

  (defthm strip-cars-of-replicate
    (equal (strip-cars (replicate n x))
           (replicate n (car x)))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm strip-cars-of-take
    (equal (strip-cars (take n x))
           (take n (strip-cars x)))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm strip-cars-of-nthcdr
    (equal (strip-cars (nthcdr n x))
           (nthcdr n (strip-cars x))))

  (defthm strip-cars-of-last
    (equal (strip-cars (last x))
           (last (strip-cars x))))

  (defthm strip-cars-of-butlast
    (equal (strip-cars (butlast x n))
           (butlast (strip-cars x) n)))

  (defthm strip-cars-of-pairlis$
    (equal (strip-cars (pairlis$ x y))
           (list-fix x))))

