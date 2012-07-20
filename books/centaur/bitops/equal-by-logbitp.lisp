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
(include-book "cutil/wizard" :dir :system)
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
      :rule-classes ((:rewrite) (:linear :trigger-terms ((logbitp-mismatch a b))))
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
ubdds)\">ubdd</see> libraries.</p>

<p>There are a couple of ways to invoke the hint.  First, you might manually
appeal to the theorem using a hint such as:</p>

<code>
 :use ((:functional-instance equal-by-logbitp
         (logbitp-hyp (lambda () my-hyps))
         (logbitp-lhs (lambda () my-lhs))
         (logbitp-rhs (lambda () my-rhs))))
</code>

<p>But this can be irritating if your particular hyps, lhs, and rhs are large
or complex terms.  See the @(see equal-by-logbitp-hint) computed hint, which
can generate the appropriate <tt>:functional-instance</tt> automatically.</p>"

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


(defsection equal-by-logbitp-hint
  :parents (bitops)
  :short "Basic automation for @(see equal-by-logbitp)."
  :long "<p>The <tt>equal-by-logbitp-hint</tt> computed hint looks for goals of
the form:</p>

<code>
 (implies (and hyp1 hyp2 ...)
          (equal lhs rhs))
</code>

<p>And automatically generates an appropriate <tt>:functional-instance</tt> of
the @(see equal-by-logbitp) theorem.  A typical use of this hint might be:</p>

<code>
 :hints((\"Goal\"
         :in-theory (enable foo bar))
        (and stable-under-simplificationp
             (equal-by-logbitp-hint)))
</code>

<p>Note that this hint is very aggressive.  For instance, it doesn't try to
determine whether <tt>lhs</tt> and <tt>rhs</tt> are numbers, it'll will try to
use @(see equal-by-logbitp) anyway.  Because of this, you would never want to
add this to the @(see default-hints).</p>"

  (defun equal-by-logbitp-hint-fn (clause)
    (declare (xargs :mode :program))
    (b* ((concl (car (last clause)))
         ((unless (and (consp concl)
                       (eq (car concl) 'equal)))
          nil)
         (lhs (cadr concl))
         (rhs (caddr concl))
         (hyp (cons 'and (acl2::dumb-negate-lit-lst (butlast clause 1)))))
      `(:use ((:functional-instance
               acl2::equal-by-logbitp
               (acl2::logbitp-hyp (lambda () ,hyp))
               (acl2::logbitp-lhs (lambda () ,lhs))
               (acl2::logbitp-rhs (lambda () ,rhs)))))))

  (defmacro equal-by-logbitp-hint ()
    `(equal-by-logbitp-hint-fn clause)))




(defsection open-logbitp-of-const-meta
  :parents (logbitp)
  :short "Rewrite terms like <tt>(logbitp foo 7)</tt> to <tt>(or (not (natp
foo)) (member-equal foo '(0 1 2)))</tt>."

  :long "<p>This meta rule targets terms of the form</p>

<code>
 (logbitp term const)
</code>

<p>where <tt>const</tt> is a quoted constant, typically a number.  We know that
such a term can only be true when <tt>term</tt> happens to be one of the bit
positions that has a <tt>1</tt> bit set in <tt>const</tt>, so we can split into
cases based on which bits of <tt>const</tt> are set.</p>

<p>Note that this rule basically is going to split into <tt>n</tt> cases, where
<tt>n</tt> is the number of <tt>1</tt> bits in <tt>const</tt>!  Because of this
we keep it disabled.  But if you see a <tt>logbitp</tt> term applied to a
constant, you might want to consider enabling this rule.</p>"

  (defevaluator lbpc-ev lbpc-ev-lst
    ((logbitp a b)
     (not a)
     (if a b c)
     (equal a b)
     (natp a)
     (zp a)
     (member-equal a x)))

  (defund bits-between (n m x)
    ;; bozo redundant with bits-between.lisp
    (declare (xargs :guard (and (natp n)
                                (natp m)
                                (<= n m)
                                (integerp x))
                    :hints(("Goal" :in-theory (enable nfix)))
                    :measure (nfix (- (nfix m) (nfix n)))))
    (let* ((n (mbe :logic (nfix n) :exec n))
           (m (mbe :logic (nfix m) :exec m)))
      (cond ((mbe :logic (zp (- m n))
                  :exec (= m n))
             nil)
            ((logbitp n x)
             (cons n (bits-between (+ n 1) m x)))
            (t
             (bits-between (+ n 1) m x)))))

  (local (defthm member-equal-of-bits-between
           (iff (member-equal a (bits-between n m x))
                (and (natp a)
                     (<= (nfix n) a)
                     (< a (nfix m))
                     (logbitp a x)))
           :hints(("Goal"
                   :in-theory (enable bits-between)
                   :induct (bits-between n m x)))))

  (defund enumerate-logbitps (x)
    (declare (xargs :guard (integerp x)))
    (bits-between 0 (integer-length x) x))

  (local (defun ind (n x)
           (if (zp n)
               (list n x)
             (ind (- n 1)
                  (logcdr x)))))

  (local (defthm crock
           (implies (and (natp x)
                         (<= (integer-length x) (nfix n)))
                    (not (logbitp n x)))
           :hints(("Goal"
                   :induct (ind n x)
                   :in-theory (enable* logbitp** integer-length**)))))

  (local (defthm member-equal-of-enumerate-logbitps-for-naturals
           (implies (and (natp x)
                         (natp a))
                    (iff (member-equal a (enumerate-logbitps x))
                         (logbitp a x)))
           :hints(("Goal" :in-theory (enable enumerate-logbitps)))))

  (defund open-logbitp-of-const (term)
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('logbitp x ('quote const . &) . &)
       (cond ((or (not (integerp const))
                  (= const 0))
              ''nil)
             ((= const -1) ''t)
             ((natp const)
              `(if (natp ,x)
                   (if (member-equal ,x ',(enumerate-logbitps const))
                       't
                     'nil)
                 ',(logbitp 0 const)))
             (t
              `(if (natp ,x)
                   (not (member-equal ,x ',(enumerate-logbitps (lognot const))))
                 ',(logbitp 0 const)))))
      (&
       term)))

  (defthmd open-logbitp-of-const-meta
    (equal (lbpc-ev x a)
           (lbpc-ev (open-logbitp-of-const x) a))
    :rule-classes ((:meta :trigger-fns (logbitp)))
    :hints(("Goal" :in-theory (enable* open-logbitp-of-const
                                       arith-equiv-forwarding))))

  (add-wizard-advice :pattern (logbitp x const)
                     :restrict (and (quotep const)
                                    (< 1 (logcount (unquote const))))
                     :msg "Possibly enable OPEN-LOGBITP-OF-CONST-META to ~
                           match ~x0; this may cause a ~x1-way case split."
                     :args (list `(logbitp ,x ,const)
                                 (logcount (unquote const))))


  (local (defthm logbitp-of-ash-free-lemma
           (implies (equal x (ash 1 y))
                    (equal (logbitp n x)
                           (equal (nfix n) (ifix y))))
           :hints(("Goal" :in-theory (enable logbitp-of-ash-split)))))

  (local (in-theory (enable* arith-equiv-forwarding)))

  (local (defthm logbitp-of-ash-free-lemma2
           (implies (and (equal (lognot x) (ash 1 y))
                         (natp y))
                    (equal (logbitp n x)
                           (not (equal (nfix n) (ifix y)))))
           :hints(("Goal" :in-theory (e/d ()
                                          (logbitp-of-ash-free-lemma))
                   :use ((:instance logbitp-of-ash-free-lemma
                                    (x (lognot x))))))))

  (local (defthm logbitp-of-ash-free-lemma3
           (equal (logbitp n -2)
                  (not (zp n)))
           :hints(("Goal" :in-theory (e/d* (logbitp**))))))

  (defund open-logbitp-of-const-lite (term)
    ;; Lighter weight version whose meta rule we'll leave enabled by default --
    ;; only applies when we can simplify (logbitp term const) without
    ;; introducing case splits.
    (declare (xargs :guard (pseudo-termp term)))
    (case-match term
      (('logbitp x ('quote const . &) . &)
       (cond ((or (not (integerp const))
                  (= const 0))
              ''nil)
             ((= const -1) ''t)
             ((natp const)
              ;; These cases are pretty convoluted, but the benefit of the
              ;; weird IFs here is that the new term we generate has no case
              ;; splits
              (let ((len (1- (integer-length const))))
                (if (equal const (ash 1 len))
                    (if (= len 0)
                        `(zp ,x)
                      `(equal ,x ',len))
                  term)))
             (t
              (let* ((const (lognot const))
                     (len (1- (integer-length const))))
                (if (equal const (ash 1 len))
                    (if (= len 0)
                        `(not (zp ,x))
                      `(not (equal ,x ',len)))
                  term)))))
      (&
       term)))

  (defthm open-logbitp-of-const-lite-meta
    (equal (lbpc-ev x a)
           (lbpc-ev (open-logbitp-of-const-lite x) a))
    :rule-classes ((:meta :trigger-fns (logbitp)))
    :hints(("Goal"
            :in-theory (e/d* (open-logbitp-of-const-lite
                              arith-equiv-forwarding
                              nfix ifix))))))

