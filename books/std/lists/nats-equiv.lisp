; Standard Typed Lists Library
; Copyright (C) 2008-2016 Centaur Technology
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
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "std/lists/take" :dir :system))

(defsection nats-equiv
  :parents (std/lists nat-equiv)
  :short "Recognizer for lists that are the same length and that are pairwise
  equivalent up to @(see nfix)."

  (defund nats-equiv (x y)
    (declare (xargs :measure (+ (len x) (len y))))
    (if (and (atom x)
             (atom y))
        t
      (and (nat-equiv (car x) (car y))
           (nats-equiv (cdr x) (cdr y)))))

  (local (in-theory (enable nats-equiv)))

  "<p>This is an @(see equivalence) relation:</p>"

  (encapsulate
    ()
    (local (defthm nats-equiv-reflexive
             (nats-equiv x x)
             :hints(("Goal" :induct (len x)))))

    (local (defthm nats-equiv-symmetric
             (implies (nats-equiv x y)
                      (nats-equiv y x))))

    (local (defthm nats-equiv-transitive
             (implies (and (nats-equiv x y)
                           (nats-equiv y z))
                      (nats-equiv x x))))

    (defequiv nats-equiv))

  "<p>It is also a @(see refinement) of @(see list-equiv):</p>"

  (defrefinement list-equiv nats-equiv)


  "<p>It also enjoys several basic congruences:</p>"

  (defcong nats-equiv nat-equiv (car x) 1)
  (defcong nats-equiv nats-equiv (cdr x) 1)
  (defcong nats-equiv nats-equiv (cons a x) 2)

  (defthm nats-equiv-of-cons
    (equal (nats-equiv (cons a x) z)
           (and (nat-equiv a (car z))
                (nats-equiv x (cdr z)))))

  (local (defun my-ind (n x y)
           (if (zp n)
               (list n x y)
             (my-ind (- n 1) (cdr x) (cdr y)))))

  (defcong nats-equiv nat-equiv (nth n x) 2
    :hints(("Goal"
            :in-theory (enable nth)
            :induct (my-ind n x x-equiv))))

  (defcong nats-equiv nats-equiv (update-nth n v x) 3
    :hints(("Goal"
            :in-theory (enable update-nth)
            :induct (my-ind n x x-equiv))))

  (defcong nat-equiv nats-equiv (update-nth n v x) 2
    :hints(("Goal"
            :in-theory (enable update-nth)
            :induct (my-ind n x x-equiv))))

  (defcong nats-equiv nats-equiv (append x y) 2)
  (defcong nats-equiv nats-equiv (revappend x y) 2)

  (defcong nats-equiv nats-equiv (take n x) 2
    :hints(("Goal" :in-theory (enable take))))

  (defcong nats-equiv nats-equiv (nthcdr n x) 2)

  (defcong nats-equiv nats-equiv (make-list-ac n val ac) 3)

  (defcong nat-equiv nats-equiv (replicate n x) 2
    :hints(("Goal" :in-theory (enable replicate)))))
