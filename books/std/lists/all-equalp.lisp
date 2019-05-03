; Standard Lists Library
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
(include-book "std/util/define" :dir :system)
(local (include-book "sets"))
(local (include-book "take"))
(local (include-book "repeat"))

(local (in-theory (enable list-fix repeat)))

(define all-equalp (a x)
  :parents (std/lists)
  :short "@(call all-equalp) determines if every member of @('x') is equal to
@('a')."

  :long "<p>In the logic, we define @('all-equalp') in terms of @(see
repeat).</p>

<p>We usually leave this enabled and prefer to reason about @('repeat')
instead.  On the other hand, we also sometimes disable it and reason about it
recursively, so we do prove a few theorems about it.</p>

<p>For better execution speed, we use a recursive definition that does no
consing.</p>

@(def all-equalp)"

  :enabled t

  (mbe :logic
       (equal (list-fix x) (repeat (len x) a))
       :exec
       (if (consp x)
           (and (equal a (car x))
                (all-equalp a (cdr x)))
         t))
  ///
  (defthm all-equalp-when-atom
    (implies (atom x)
             (all-equalp a x)))

  (defthm all-equalp-of-cons
    (equal (all-equalp a (cons b x))
           (and (equal a b)
                (all-equalp a x))))

  (local (in-theory (disable all-equalp)))

  (defthm car-when-all-equalp
    (implies (all-equalp a x)
             (equal (car x)
                    (if (consp x) a nil)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm all-equalp-of-cdr-when-all-equalp
    (implies (all-equalp a x)
             (all-equalp a (cdr x))))

  (defthm member-equal-when-all-equalp
    (implies (all-equalp a x)
             (iff (member-equal b x)
                  (and (consp x)
                       (equal a b))))
    :hints(("Goal" :induct (len x))))

  (defthm all-equalp-by-superset
    (implies (and (all-equalp a y)
                  (subsetp-equal x y))
             (all-equalp a x))
    :hints(("Goal" :induct (len x))))

  (defcong set-equiv equal (all-equalp a x) 2
    :hints(("Goal"
            :in-theory (enable set-equiv)
            :cases ((all-equalp a x)))))

  (defthm all-equalp-of-append
    (equal (all-equalp a (append x y))
           (and (all-equalp a x)
                (all-equalp a y)))
    :hints(("Goal" :induct (len x))))

  (defthm all-equalp-of-list-fix
    ;; BOZO silly to prove this?  Consequence of set-equiv.
    (equal (all-equalp a (list-fix x))
           (all-equalp a x)))

  (defthm all-equalp-of-rev
    ;; BOZO silly to prove this?  Consequence of set-equiv.
    (equal (all-equalp a (rev x))
           (all-equalp a x)))

  (defthm all-equalp-of-repeat
    (equal (all-equalp a (repeat n b))
           (or (equal a b)
               (zp n))))

  (defthm all-equalp-of-take
    (implies (all-equalp a x)
             (equal (all-equalp a (take n x))
                    (or (not a)
                        (<= (nfix n) (len x)))))
    :hints(("Goal" :in-theory (enable take))))

  (defthm all-equalp-of-nthcdr
    (implies (all-equalp a x)
             (all-equalp a (nthcdr n x)))
    :hints(("Goal" :in-theory (enable nthcdr)))))
