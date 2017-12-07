; Random$ function
; Copyright (C) 2012 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)
(local (include-book "tools/mv-nth" :dir :system))
(set-state-ok t)

(defsection random$-lemmas
  :parents (random$)
  :short "Lemmas about random$ available in the system/random book."

  (local (in-theory (enable random$)))

  (defthm natp-random$-better
    (natp (mv-nth 0 (random$ limit state)))
    :rule-classes :type-prescription)

  (defthm random$-linear-better
    (and (<= 0 (mv-nth 0 (random$ n state)))
         (implies (posp n)
                  (< (mv-nth 0 (random$ n state)) n)))
    :hints(("Goal"
            :in-theory (enable mv-nth)
            :use ((:instance acl2::random$-linear (acl2::n n))))))

  (defthm state-p1-of-random
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (random$ limit state))))
    :hints(("Goal" :in-theory (enable random$ read-acl2-oracle)))))


(defsection random-list-aux
  :parents (random$)
  :short "Add random numbers onto an accumulator."

  (defund random-list-aux (n limit acc state)

; Matt K. mod: Reverse acc before the return.  This is probably not important;
; I've done it for backward compatibility in centaur/misc/seed-random.lisp when
; replacing the definition of random-list there, which was not tail-recursive,
; with the one here.

    (declare (xargs :guard (and (natp n)
                                (posp limit)
                                (true-listp acc))))
    (if (zp n)
        (mv (reverse acc) state)
      (b* (((mv x1 state) (random$ limit state)))
        (random-list-aux (- n 1) limit (cons x1 acc) state))))

  (local (in-theory (enable random-list-aux)))

  (local (defthm nat-listp-revappend
           (implies (nat-listp x)
                    (equal (nat-listp (revappend x y))
                           (nat-listp y)))))

  (defthm nat-listp-of-random-list-aux
    (implies (nat-listp acc)
             (equal (nat-listp (mv-nth 0 (random-list-aux n limit acc state)))
                    (nat-listp acc))))

  (defthm state-p1-of-random-list-aux
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (random-list-aux n limit acc state))))))


(defsection random-list
  :parents (random$)
  :short "Generate a list of random numbers in [0, limit)."

  (defund random-list (n limit state)
    (declare (xargs :guard (and (natp n)
                                (posp limit))))
    (random-list-aux n limit nil state))

  (local (in-theory (enable random-list)))

  (defthm nat-listp-of-random-list
    (nat-listp (mv-nth 0 (random-list n limit state))))

  (defthm state-p1-of-random-list
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (random-list n limit state))))))



