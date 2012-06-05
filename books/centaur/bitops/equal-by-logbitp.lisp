; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

; equal-by-logbitp
;
; We prove equal-by-logbitp, a way to prove integers are equal by showing they
; agree on every bit.

(in-package "ACL2")
(include-book "cutil/defsection" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "integer-length"))
(local (in-theory (disable floor mod logbitp evenp oddp)))
(local (in-theory (disable logcons logcar logcdr integer-length)))
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm equal-of-logcdrs-when-equal-of-logcars
         (implies (and (integerp i)
                       (integerp j)
                       (equal (logcar i) (logcar j)))
                  (equal (equal (logcdr i) (logcdr j))
                         (equal i j)))))

(local
 (defthm logbitp-of-increment
   (implies (and (natp i)
                 (integerp j))
            (equal (logbitp (+ 1 i) j)
                   (logbitp i (logcdr j))))))

(local
 (defthm logcar-possibilities
   (or (equal (logcar a) 0)
       (equal (logcar a) 1))
   :rule-classes ((:forward-chaining :trigger-terms ((logcar a))))))

(local (defthm lemma1
         (implies (integerp a)
                  (equal (mod a 2) (logcar a)))
         :hints(("Goal" :in-theory (enable  logcar)))))

(local (defthm lemma2
         (implies (integerp a)
                  (equal (floor a 2) (logcdr a)))
         :hints(("Goal" :in-theory (enable  logcdr)))))


(defsection logbitp-mismatch
  :parents (bitops)
  :short "@(call logbitp-mismatch) finds the minimal bit-position for which
<tt>a</tt> and <tt>b</tt> differ, or returns <tt>NIL</tt> if no such bit
exists."
  :long "<p>This is mainly useful for proving @(see equal-by-logbitp), but
it's also occasionally useful as a witness in other theorems.</p>"

  (defund logbitp-mismatch (a b)
    (declare (xargs :measure (+ (integer-length a)
                                (integer-length b))
                    :guard t))
    (let ((a (ifix a))
          (b (ifix b)))
      (cond ((not (equal (mod a 2) (mod b 2)))
             0)
            ((and (zp (integer-length a))
                  (zp (integer-length b)))
             nil)
            (t
             (let ((tail (logbitp-mismatch (floor a 2) (floor b 2))))
               (and tail (+ 1 tail)))))))

  (local (defun logbitp-mismatch* (a b)
           (declare (xargs :measure (+ (integer-length a)
                                       (integer-length b))))
           (cond ((not (equal (logcar a) (logcar b)))
                  0)
                 ((and (zp (integer-length a))
                       (zp (integer-length b)))
                  nil)
                 (t
                  (let ((tail (logbitp-mismatch* (logcdr a) (logcdr b))))
                    (and tail (+ 1 tail)))))))

  (local (defthm logbitp-mismatch-redefinition
           (implies (and (integerp a)
                         (integerp b))
                    (equal (logbitp-mismatch a b)
                           (logbitp-mismatch* a b)))
           :hints(("Goal"
                   :induct (logbitp-mismatch* a b)
                   :in-theory (enable logbitp-mismatch
                                      logbitp-mismatch*)))))

  (defthm logbitp-mismatch-under-iff
    (implies (and (integerp a)
                  (integerp b))
             (iff (logbitp-mismatch a b)
                  (not (equal a b))))
    :hints(("Goal"
            :in-theory (enable logbitp-mismatch*)
            :induct (logbitp-mismatch* a b))))

  (local (in-theory (disable logbitp-mismatch-under-iff)))

  (encapsulate
    ()

    (local (defthm lemma
             (implies (and (integerp a)
                           (integerp b)
                           (logbitp-mismatch* a b))
                      (not (equal (logbitp (logbitp-mismatch* a b) a)
                                  (logbitp (logbitp-mismatch* a b) b))))
             :hints(("Goal"
                     :in-theory (enable logbitp-mismatch* logbitp**)
                     :induct (logbitp-mismatch* a b)))))

    (defthm logbitp-mismatch-correct
      (implies (and (integerp a)
                    (integerp b)
                    (logbitp-mismatch a b))
               (not (equal (logbitp (logbitp-mismatch a b) a)
                           (logbitp (logbitp-mismatch a b) b))))))


  (encapsulate
    ()
    (local (defthmd lemma
             (implies (and (integerp a)
                           (integerp b)
                           (logbitp-mismatch* a b))
                      (<= (logbitp-mismatch* a b)
                          (max (integer-length a)
                               (integer-length b))))
             :hints(("Goal" :in-theory (enable logbitp-mismatch* integer-length)))))

    (defthm logbitp-mismatch-upper-bound-for-integers
      (implies (and (integerp a)
                    (integerp b)
                    (logbitp-mismatch a b))
               (<= (logbitp-mismatch a b)
                   (max (integer-length a)
                        (integer-length b))))
      :rule-classes ((:rewrite) (:linear))
      :hints(("Goal" :use ((:instance lemma))))))


  (encapsulate
    ()
    (local (defthmd lemma
             (implies (and (natp a)
                           (natp b)
                           (logbitp-mismatch* a b))
                      (< (logbitp-mismatch* a b)
                         (max (integer-length a)
                              (integer-length b))))
             :hints(("Goal" :in-theory (enable logbitp-mismatch* integer-length)))))

    (defthm logbitp-mismatch-upper-bound-for-naturals
      (implies (and (natp a)
                    (natp b)
                    (logbitp-mismatch a b))
               (< (logbitp-mismatch a b)
                  (max (integer-length a)
                       (integer-length b))))
      :rule-classes ((:rewrite) (:linear))
      :hints(("Goal" :use ((:instance lemma))))))


  (defthm integerp-of-logbitp-mismatch
    ;; BOZO why do I have to have this stupid rule when the type prescription
    ;; for logbitp-mismatch says it's either a nonnegative integer or nil?
    (equal (integerp (logbitp-mismatch a b))
           (if (logbitp-mismatch a b)
               t
             nil))
    :hints(("Goal" :in-theory (enable logbitp-mismatch)))))




(defsection equal-by-logbitp
  :parents (bitops)
  :short "Show <tt>a = b</tt> by showing their bits are equal."

  :long "<p><tt>Equal-by-logbitp</tt> may be functionally instantiated to prove
<tt>(equal a b)</tt> by showing that:</p>

<code>
 (equal (logbitp bit a) (logbitp bit b))
</code>

<p>for any arbitrary <tt>bit</tt> less than the maximum @(see integer-length)
of <tt>a</tt> or <tt>b</tt>, where <tt>a</tt> and <tt>b</tt> are known to be
integers.</p>

<p>This unusual (but occasionally useful) proof strategy is similar to the
<i>pick-a-point</i> proofs found in the ordered sets or <see topic=\"@(url
ubdds)\">ubdd</see> libraries, except we do not try to automate its
application.  Instead, to use it, you must give a hint such as:</p>

<code>
 :use ((:functional-instance equal-by-logbitp
         (logbitp-lhs (lambda () a))
         (logbitp-rhs (lambda () b))))
</code>"

  (encapsulate
    (((logbitp-hyp) => *)
     ((logbitp-lhs) => *)
     ((logbitp-rhs) => *))

    (local (defun logbitp-hyp () t))
    (local (defun logbitp-lhs () 0))
    (local (defun logbitp-rhs () 0))

    (defthm logbitp-constraint
      (implies (and (logbitp-hyp)
                    (integerp (logbitp-lhs))
                    (integerp (logbitp-rhs))
                    (natp bit)
                    (<= bit (max (integer-length (logbitp-lhs))
                                 (integer-length (logbitp-rhs)))))
               (equal (logbitp bit (logbitp-lhs))
                      (logbitp bit (logbitp-rhs))))))

  (defthmd equal-by-logbitp
    (implies (and (logbitp-hyp)
                  (integerp (logbitp-lhs))
                  (integerp (logbitp-rhs)))
             (equal (logbitp-lhs) (logbitp-rhs)))
    :hints(("Goal"
            :in-theory (e/d (logbitp-mismatch-under-iff)
                            (logbitp-mismatch-upper-bound-for-integers
                             logbitp-constraint))
            :use ((:instance logbitp-constraint
                             (bit (logbitp-mismatch (logbitp-lhs) (logbitp-rhs))))
                  (:instance logbitp-mismatch-upper-bound-for-integers
                             (a (logbitp-lhs))
                             (b (logbitp-rhs))))))))

