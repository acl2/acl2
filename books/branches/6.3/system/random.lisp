; Random$ function
; Copyright (C) 2012 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "tools/bstar" :dir :system)
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
    (declare (xargs :guard (and (natp n)
                                (posp limit))))
    (if (zp n)
        (mv acc state)
      (b* (((mv x1 state) (random$ limit state)))
        (random-list-aux (- n 1) limit (cons x1 acc) state))))

  (local (in-theory (enable random-list-aux)))

  (defthm nat-listp-of-random-list-aux
    (equal (nat-listp (mv-nth 0 (random-list-aux n limit acc state)))
           (nat-listp acc)))

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



