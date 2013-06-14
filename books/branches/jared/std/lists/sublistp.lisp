; Sublistp and Listpos functions
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")
(include-book "prefixp")
(include-book "equiv")
(local (include-book "take"))
(local (include-book "nthcdr"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection sublistp
  :parents (std/lists search)
  :short "@(call sublistp) checks whether the list @('x') ever occurs within
the list @('y')."

  :long "<p>ACL2 has a built-in @(see search) function, but it's very
complicated; it can operate on either lists or strings, using either equality
or case-insensitive character comparison, and can stop early, and can search
from the front or end, and so on.</p>

<p>In comparison, @('sublistp') is much simpler.  It only operates on lists,
always considers only equality, and always searches the whole list from the
front.  This makes it generally much more pleasant to reason about.</p>"

  (defund sublistp (x y)
    (declare (xargs :guard t))
    (cond ((prefixp x y) t)
          ((atom y)      nil)
          (t             (sublistp x (cdr y)))))

  (local (in-theory (enable sublistp)))

  (defthm sublistp-when-atom-left
    (implies (atom x)
             (equal (sublistp x y)
                    t)))

  (defthm sublistp-when-atom-right
    (implies (atom y)
             (equal (sublistp x y)
                    (atom x))))

  (defthm sublistp-of-cons-right
    (equal (sublistp x (cons a y))
           (or (prefixp x (cons a y))
               (sublistp x y))))

  (defthm sublistp-when-prefixp
    (implies (prefixp x y)
             (sublistp x y)))

  (defthm sublistp-of-list-fix-left
    (equal (sublistp (list-fix x) y)
           (sublistp x y)))

  (defthm sublistp-of-list-fix-right
    (equal (sublistp x (list-fix y))
           (sublistp x y)))

  (defcong list-equiv equal (sublistp x y) 1
    :hints(("Goal" :in-theory (disable sublistp
                                       sublistp-of-list-fix-left)
            :use ((:instance sublistp-of-list-fix-left (x x))
                  (:instance sublistp-of-list-fix-left (x x-equiv))))))

  (defcong list-equiv equal (sublistp x y) 2
    :hints(("Goal" :in-theory (disable sublistp
                                       sublistp-of-list-fix-right)
            :use ((:instance sublistp-of-list-fix-right (y y))
                  (:instance sublistp-of-list-fix-right (y y-equiv))))))

  (defthm lower-bound-of-len-when-sublistp
    (implies (sublistp x y)
             (<= (len x) (len y)))
    :rule-classes ((:rewrite) (:linear))))



(defsection listpos
  :parents (std/lists)
  :short "@(call listpos) returns the starting position of the first occurrence
of the sublist @('x') within the list @('y'), or @('NIL') if there is no such
occurrence."

  :long "<p>This is strongly related to @(see sublistp).</p>"

  (defund listpos (x y)
    (declare (xargs :guard t))
    (cond ((prefixp x y)
           0)
          ((atom y)
           nil)
          (t
           (let ((pos-in-cdr (listpos x (cdr y))))
             (and pos-in-cdr
                  (+ 1 pos-in-cdr))))))

  (local (in-theory (enable listpos)))

  (defthm listpos-when-atom-left
    (implies (atom x)
             (equal (listpos x y)
                    0)))

  (defthm listpos-when-atom-right
    (implies (atom y)
             (equal (listpos x y)
                    (if (atom x)
                        0
                      nil))))

  (defthm listpos-of-list-fix-left
    (equal (listpos (list-fix x) y)
           (listpos x y)))

  (defthm listpos-of-list-fix-right
    (equal (listpos x (list-fix y))
           (listpos x y)))

  (defcong list-equiv equal (listpos x y) 1)
  (defcong list-equiv equal (listpos x y) 2
    :hints(("Goal"
            :in-theory (disable listpos-of-list-fix-right)
            :use ((:instance listpos-of-list-fix-right)
                  (:instance listpos-of-list-fix-right
                             (y y-equiv))))))

  (defthm listpos-under-iff
    (iff (listpos x y)
         (sublistp x y))
    :hints(("Goal" :in-theory (enable sublistp))))

  (encapsulate
    ()

    ;; BLAH, yuck, stupid rules.  To see why they're necessary, try to prove
    ;; them after (in-theory (disable listpos sublistp)).  You'd think the
    ;; type-prescription of listpos would be enough to not need any of this.

    (defthm natp-of-listpos
      (equal (natp (listpos x y))
             (sublistp x y)))

    (defthm integerp-of-listpos
      (equal (integerp (listpos x y))
             (sublistp x y)))

    (defthm rationalp-of-listpos
      (equal (rationalp (listpos x y))
             (sublistp x y)))

    (defthm acl2-numberp-of-listpos
      (equal (acl2-numberp (listpos x y))
             (sublistp x y))))

  (defthm listpos-lower-bound-weak
    ;; You'd think that type reasoning would save us from dealing with this kind
    ;; of shit, but you'd be wrong.
    (<= 0 (listpos x y))
    :rule-classes (:linear))

  (defthm listpos-upper-bound-weak
    (<= (listpos x y) (len y))
    :rule-classes ((:rewrite) (:linear)))

  (defthm listpos-upper-bound-strong-1
    (equal (< (listpos x y) (len y))
           (consp y))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (consp y)
                                     (< (listpos x y) (len y))))))

  (defthm listpos-upper-bound-strong-2
    (implies (sublistp x y)
             (<= (listpos x y) (- (len y) (len x))))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm l0
           (implies (and (prefixp x (nthcdr n y))
                         (natp n))
                    (<= (listpos x y) n))))

  (defthm listpos-complete
    ;; Suppose there exists some N such that X is a prefix of Y[M:...].  Then the
    ;; index returned by (listpos X Y) is at most N.  In other words, it really
    ;; does find the first occurrence of X in Y.
    (implies (prefixp x (nthcdr n y))
             (and (listpos x y)
                  (<= (listpos x y) (nfix n))))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (prefixp x (nthcdr n y))
                                     (<= (listpos x y) (nfix n)))))))


(defsection sublistp-correctness
  :extension sublistp

  (local (in-theory (enable sublistp listpos)))

  (defthm sublistp-sound
    ;; Suppose we say X is a sublist of Y.  Then there truly does exists some
    ;; offset, N, such that X is a prefix of Y[N:...].
    (implies (sublistp x y)
             (let ((n (listpos x y)))
               (prefixp x (nthcdr n y))))
    :hints(("Goal" :induct (sublistp x y))))

  (defthm sublistp-complete
    ;; Suppose there exists some N such that X is a prefix of Y[N:...].  Then we
    ;; properly say X is a sublist of Y.
    (implies (prefixp x (nthcdr n y))
             (sublistp x y))))



