; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "xdoc/top" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "integer-length"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection logbitp-mismatch
  :parents (bitops logbitp)
  :short "@(call logbitp-mismatch) finds the minimal bit-position for which
@('a') and @('b') differ, or returns @('NIL') if no such bit exists."

  :long "<p>This is mainly useful for proving @(see equal-by-logbitp), but it's
also occasionally useful as a witness in other theorems.</p>"

  (defund logbitp-mismatch (a b)
    (declare (xargs :measure (+ (integer-length a)
                                (integer-length b))
                    :guard (and (integerp a)
                                (integerp b))))
    (cond ((not (equal (logcar a) (logcar b)))
           0)
          ((and (zp (integer-length a))
                (zp (integer-length b)))
           nil)
          (t
           (let ((tail (logbitp-mismatch (logcdr a) (logcdr b))))
             (and tail (+ 1 tail))))))

  (local (in-theory (enable logbitp-mismatch integer-length**)))
  (local (in-theory (enable* arith-equiv-forwarding)))

  (defthm logbitp-mismatch-under-iff
    (iff (logbitp-mismatch a b)
         (not (equal (ifix a) (ifix b)))))

  (local (in-theory (disable logbitp-mismatch-under-iff)))

  (defthm logbitp-mismatch-correct
    (implies (logbitp-mismatch a b)
             (not (equal (logbitp (logbitp-mismatch a b) a)
                         (logbitp (logbitp-mismatch a b) b))))
    :hints(("Goal"
            :in-theory (enable logbitp-mismatch logbitp**)
            :induct (logbitp-mismatch a b))))

  (defthm logbitp-mismatch-upper-bound
    (implies (logbitp-mismatch a b)
             (<= (logbitp-mismatch a b)
                 (max (integer-length a)
                      (integer-length b))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm logbitp-mismatch-upper-bound-for-nonnegatives
    (implies (and (not (and (integerp a) (< a 0)))
                  (not (and (integerp b) (< b 0)))
                  (logbitp-mismatch a b))
             (< (logbitp-mismatch a b)
                (max (integer-length a)
                     (integer-length b))))
    :rule-classes ((:rewrite) (:linear :trigger-terms ((logbitp-mismatch a b)))))

  (defthm integerp-of-logbitp-mismatch
    ;; BOZO why do I have to have this stupid rule when the type prescription
    ;; for logbitp-mismatch says it's either a nonnegative integer or nil?
    (iff (integerp (logbitp-mismatch a b))
         (logbitp-mismatch a b))
    :hints(("Goal" :in-theory (enable logbitp-mismatch)))))

