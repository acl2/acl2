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
(include-book "std/util/wizard" :dir :system)
(local (include-book "integer-length"))
(local (in-theory (disable floor mod logbitp evenp oddp)))
(local (in-theory (disable logcons logcar logcdr integer-length)))
(include-book "ihsext-basics")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(include-book "clause-processors/witness-cp" :dir :system)

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
                   (logbitp i (logcdr j))))
   :hints(("Goal" :in-theory (enable logbitp**)))))

(local
 (defthm logcar-possibilities
   (or (equal (logcar a) 0)
       (equal (logcar a) 1))
   :rule-classes ((:forward-chaining :trigger-terms ((logcar a))))))

;; (local (defthm lemma1
;;          (implies (integerp a)
;;                   (equal (mod a 2) (logcar a)))
;;          :hints(("Goal" :in-theory (enable  logcar)))))

;; (local (defthm lemma2
;;          (implies (integerp a)
;;                   (equal (floor a 2) (logcdr a)))
;;          :hints(("Goal" :in-theory (enable  logcdr)))))


(defsection logbitp-mismatch
  :parents (bitops)
  :short "@(call logbitp-mismatch) finds the minimal bit-position for which
@('a') and @('b') differ, or returns @('NIL') if no such bit exists."

  :long "<p>This is mainly useful for proving @(see equal-by-logbitp), but
it's also occasionally useful as a witness in other theorems.</p>"

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

  (local (in-theory (enable logbitp-mismatch
                            integer-length**)))
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
    (equal (integerp (logbitp-mismatch a b))
           (if (logbitp-mismatch a b)
               t
             nil))
    :hints(("Goal" :in-theory (enable logbitp-mismatch)))))




(defsection equal-by-logbitp
  :parents (bitops)
  :short "Show @('a = b') by showing their bits are equal."

  :long "<p>@('Equal-by-logbitp') may be functionally instantiated to prove
@('(equal a b)') by showing that:</p>

@({
 (equal (logbitp bit a) (logbitp bit b))
})

<p>for any arbitrary @('bit') less than the maximum @(see integer-length) of
@('a') or @('b'), where @('a') and @('b') are known to be integers.</p>

<p>This unusual (but occasionally useful) proof strategy is similar to the
<i>pick-a-point</i> proofs found in the ordered sets or <see topic=\"@(url
ubdds)\">ubdd</see> libraries.</p>

<p>There are a couple of ways to invoke the hint.  First, you might manually
appeal to the theorem using a hint such as:</p>

@({
 :use ((:functional-instance equal-by-logbitp
         (logbitp-hyp (lambda () my-hyps))
         (logbitp-lhs (lambda () my-lhs))
         (logbitp-rhs (lambda () my-rhs))))
})

<p>But this can be irritating if your particular hyps, lhs, and rhs are large
or complex terms.  See the @(see equal-by-logbitp-hint) computed hint, which
can generate the appropriate @(':functional-instance') automatically.</p>"

  (encapsulate
    (((logbitp-hyp) => *)
     ((logbitp-lhs) => *)
     ((logbitp-rhs) => *))

    (local (defun logbitp-hyp () t))
    (local (defun logbitp-lhs () 0))
    (local (defun logbitp-rhs () 0))

    (defthm logbitp-constraint
      (implies (and (logbitp-hyp)
                    (natp bit)
                    (<= bit (max (integer-length (logbitp-lhs))
                                 (integer-length (logbitp-rhs)))))
               (equal (logbitp bit (logbitp-lhs))
                      (logbitp bit (logbitp-rhs))))))

  (defthmd equal-by-logbitp
    (implies (logbitp-hyp)
             (equal (ifix (logbitp-lhs)) (ifix (logbitp-rhs))))
    :hints(("Goal"
            :in-theory (e/d (logbitp-mismatch-under-iff)
                            (logbitp-mismatch-upper-bound
                             logbitp-constraint))
            :use ((:instance logbitp-constraint
                             (bit (logbitp-mismatch (logbitp-lhs) (logbitp-rhs))))
                  (:instance logbitp-mismatch-upper-bound
                             (a (logbitp-lhs))
                             (b (logbitp-rhs))))))))


(defthmd logbitp-when-bit
  ;; Disabled because the case split could be expensive
  (implies (bitp b)
           (equal (logbitp i b)
                  (and (= (nfix i) 0)
                       (equal b 1)))))

(defthm logbitp-of-negative-const
  (implies (and (syntaxp (quotep x))
                (< x 0))
           (equal (logbitp bit x)
                  (not (logbitp bit (lognot x))))))



(defsection logbitp-of-const

  (local (in-theory (enable* arith-equiv-forwarding)))

  (local (defthm logbitp-of-lognot-free
           (implies (equal n (lognot m))
                    (equal (logbitp x n)
                           (not (logbitp x m))))))

  (local (defthm logbitp-of-1
           (equal (logbitp x 1)
                  (zp x))
           :hints(("Goal" :in-theory (enable logbitp** zp nfix)))))

  (local (defthm logbitp-of-minus-2
           (equal (logbitp x -2)
                  (not (zp x)))
           :hints(("Goal" :in-theory (enable logbitp**)))))

  ;; This shouldn't case split because of the (quotep n) requirement.
  (defthm logbitp-of-const
    (implies (and (syntaxp (quotep n))
                  (let ((n (ifix n)))
                    (or (= n 0)
                        (= n -1)
                        (if (< n 0)
                            (= n (lognot (ash 1 (1- (integer-length n)))))
                          (= n (ash 1 (1- (integer-length n))))))))
             (equal (logbitp x n)
                    (let ((n (ifix n)))
                      (cond ((= n 0) nil)
                            ((= n -1) t)
                            ((< n 0)
                             (not (equal (nfix x)
                                         (1- (integer-length n)))))
                            (t
                             (equal (nfix x)
                                    (1- (integer-length n))))))))
    :hints(("Goal" :in-theory (enable logbitp-of-ash-split nfix ifix)
            :cases ((> (integer-length n) 0)))))

  (defthmd logbitp-of-bitmask
    (implies (bitmaskp n)
             (equal (logbitp x n)
                    (< (nfix x) (integer-length n))))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions)
            :induct t)
           '(:cases ((logbitp x n)))))

  (local (in-theory (enable logbitp-of-bitmask)))

  (defthm integer-length-of-lognot
    (equal (integer-length (lognot x))
           (integer-length x))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions))))

  (defthm logbitp-of-mask
    (implies (and (syntaxp (quotep n))
                  (let* ((n (ifix n))
                         (len (integer-length n)))
                    (and (< 0 len)
                         (if (< n 0)
                             (equal n (lognot (1- (ash 1 (1- (integer-length n))))))
                           (equal n (1- (ash 1 (1- (integer-length n)))))))))
             (equal (logbitp x n)
                    (let ((n (ifix n)))
                      (if (< n 0)
                          (<= (integer-length n) (nfix x))
                        (< (nfix x) (integer-length n))))))
    :hints (("goal" :cases ((logbitp x n))
             :in-theory (enable ifix nfix)))))


(defsection logbitp-of-const-split

  (local (in-theory (enable* arith-equiv-forwarding)))

  (defund scan-for-bit (start val n)
    (declare (xargs :guard (and (natp start)
                                (booleanp val)
                                (integerp n))))
    (if (zp start)
        nil
      (let ((start (1- start)))
        (if (eq (logbitp start n)
                (mbe :logic (and val t) :exec val))
            start
          (scan-for-bit start val n)))))

  (local
   (progn
     (in-theory (enable scan-for-bit))

     (defcong nat-equiv equal (scan-for-bit start val n) 1)
     (defcong iff       equal (scan-for-bit start val n) 2)
     (defcong int-equiv equal (scan-for-bit start val n) 3)

     (defthm logbitp-of-scan-for-bit
       (implies (scan-for-bit start val n)
                (equal (logbitp (scan-for-bit start val n) n)
                       (and val t))))

     (defthm logbitp-of-scan-for-bit-free
       (implies (and (equal x (scan-for-bit start val n))
                     (scan-for-bit start val n))
                (equal (logbitp x n)
                       (and val t))))

     (defthm scan-for-bit-bound
       (implies (scan-for-bit start val n)
                (< (scan-for-bit start val n) (nfix start)))
       :rule-classes :linear)

     (defthm scan-for-bit-between
       (implies (and (< (scan-for-bit start val n) bit)
                     (natp bit)
                     (equal val (not (logbitp start n)))
                     (<= bit (nfix start)))
                (equal (logbitp bit n) (not val)))
       :hints(("Goal" :in-theory (enable nfix)
               :induct (scan-for-bit start val n))
              '(:cases ((= bit (nfix start))))))

     ;; (defthm scan-for-bit-single-bit
     ;;   (implies (and (equal (scan-for-bit start val n)
     ;;                        (+ -1 start))
     ;;                 (natp bit)
     ;;                 (natp start)
     ;;                 (equal val (not (logbitp start n)))
     ;;                 (<= bit (nfix start)))
     ;;            (equal (logbitp bit n) (not val)))
     ;;   :hints(("Goal" :in-theory (enable nfix)
     ;;           :induct (scan-for-bit start val n))
     ;;          '(:cases ((= bit (nfix start))))))

     (defthm logbitp-when-not-scan-for-bit
       (implies (and (not (scan-for-bit start val n))
                     (syntaxp (not (equal start b)))
                     (equal val (not (logbitp start n)))
                     (<= (nfix b) (nfix start)))
                (equal (logbitp b n) (not val))))

     (in-theory (disable scan-for-bit))))



  (defun bit-scan-rec (bit start curr-val n)
    (declare (xargs :guard (and (natp bit)
                                (natp start)
                                (booleanp curr-val)
                                (integerp n))
                    :measure (nfix start)))
    (let* ((nbit (mbe :logic (nfix bit) :exec bit))
           (start (mbe :logic (nfix start) :exec start))
           (curr-val (mbe :logic (and curr-val t) :exec curr-val))
           (n (mbe :logic (ifix n) :exec n))
           (next (scan-for-bit start (not curr-val) n)))
      (cond ((not next)
             (and curr-val
                  (if (= start 0)
                      (zp bit)
                    (or (not (natp bit))
                        (<= bit start)))))
            ((not curr-val)
             (bit-scan-rec nbit next t n))
            ((= next (1- (nfix start)))
             (or (= bit start)
                 (bit-scan-rec nbit next nil n)))
            (t (or (and (<= nbit start)
                        (> nbit next))
                   (bit-scan-rec nbit next nil n))))))

  (local
   (progn
     (defcong nat-equiv equal (bit-scan-rec bit start curr-val n) 1
       :hints (("goal" :expand ((:free (bit) (bit-scan-rec bit start curr-val n)))
                :in-theory (enable nfix))))
     (defcong nat-equiv equal (bit-scan-rec bit start curr-val n) 2
       :hints (("goal" :expand ((:free (start) (bit-scan-rec bit start curr-val n))))))
     (defcong iff       equal (bit-scan-rec bit start curr-val n) 3
       :hints (("goal" :expand ((:free (curr-val) (bit-scan-rec bit start curr-val n))))))
     (defcong int-equiv equal (bit-scan-rec bit start curr-val n) 4
       :hints (("goal" :expand ((:free (n) (bit-scan-rec bit start curr-val n))))))


     (defthm <-0-forward-to-nat-equiv-0
       (implies (< x 0)
                (nat-equiv x 0))
       :rule-classes :forward-chaining)

     (defthmd equal-of-booleans
       (implies (and (booleanp a) (booleanp b))
                (equal (equal a b)
                       (iff a b))))

     (defthm bit-scan-rec-correct
       (implies (and (natp start)
                     (equal curr-val (logbitp start n)))
                (equal (bit-scan-rec bit start curr-val n)
                       (and (<= (nfix bit) start)
                            (logbitp bit n))))
       :hints (("goal" :induct t
                :in-theory (e/d (nfix ifix)
                                (not (:definition bit-scan-rec)))
                :expand ((:free (bit val) (bit-scan-rec bit start val n))
                         (:free (bit val) (bit-scan-rec bit 0 val n))
                         (:free (val) (bit-scan-rec bit bit val n))))
               '(:cases ((logbitp bit n)))
               (and stable-under-simplificationp
                    '(:in-theory (enable equal-of-booleans)))))

     (defthm logbitp-when-gte-integer-length
       (implies (<= (integer-length n) (nfix i))
                (equal (logbitp i n)
                       (< (ifix n) 0)))
       :hints (("goal" :in-theory (enable* ihsext-inductions
                                           ihsext-recursive-redefs)
                :induct (logbitp i n))))

     (defthm logbitp-of-integer-length-minus-1
       (implies (not (equal 0 (integer-length n)))
                (equal (logbitp (+ -1 (integer-length n)) n)
                       (<= 0 (ifix n))))
       :hints (("goal" :in-theory (enable* ihsext-inductions
                                           ihsext-recursive-redefs)
                :induct (integer-length n))))))

  (defthm open-bit-scan-rec
    (implies (syntaxp (and (quotep start)
                           (quotep curr-val)
                           (quotep n)))
             (equal (bit-scan-rec bit start curr-val n)
                    (let* ((nbit (mbe :logic (nfix bit) :exec bit))
                           (start (mbe :logic (nfix start) :exec start))
                           (curr-val (mbe :logic (and curr-val t) :exec curr-val))
                           (n (mbe :logic (ifix n) :exec n))
                           (next (scan-for-bit start (not curr-val) n)))
                      (cond ((not next)
                             (and curr-val
                                  (if (= start 0)
                                      (zp bit)
                                    (or (not (natp bit))
                                        (<= bit start)))))
                            ((not curr-val)
                             (bit-scan-rec nbit next t n))
                            ((= next (1- (nfix start)))
                             (or (= bit start)
                                 (bit-scan-rec nbit next nil n)))
                            (t (or (and (<= nbit start)
                                        (> nbit next))
                                   (bit-scan-rec nbit next nil n)))))))
    :hints (("goal" :in-theory nil
             :expand ((bit-scan-rec bit start curr-val n)))))

  (defthmd logbitp-of-const-split
    (implies (syntaxp (quotep n))
             (equal (logbitp bit n)
                    (let ((n (ifix n)))
                      (cond ((= n 0) nil)
                            ((= n -1) t)
                            ((< n 0)
                             (or (>= (nfix bit) (integer-length n))
                                 (not (bit-scan-rec
                                       bit
                                       (1- (integer-length n))
                                       t (lognot n)))))
                            (t
                             (bit-scan-rec
                              bit
                              (1- (integer-length n))
                              t n))))))
    :hints(("Goal" :in-theory (e/d () (bit-scan-rec)))
           (and stable-under-simplificationp
                (if (member-equal '(negp n) clause)
                    '(:cases ((< bit (integer-length n))))
                  '(:use ((:instance bit-scan-rec-correct
                           (start (+ -1 (integer-length n)))
                           (curr-val t)
                           (n (lognot n))))
                    :in-theory (e/d ()
                                    (bit-scan-rec
                                     bit-scan-rec-correct)))))))


  (add-wizard-advice :pattern (logbitp x const)
                     :restrict
                     (and (quotep const)
                          (not (let* ((n (ifix (unquote const)))
                                      (len (integer-length n)))
                                 (or (= len 0)
                                     (if (< n 0)
                                         (= n (lognot (ash 1 (1- (integer-length n)))))
                                       (= n (ash 1 (1- (integer-length n)))))
                                     (if (< n 0)
                                         (equal n (lognot (1- (ash 1 (1- (integer-length n))))))
                                       (equal n (1- (ash 1 (1- (integer-length n))))))))))
                     :msg "Possibly enable ~x0 to match ~x1; this may cause ~
                           some case splitting."
                     :args (list 'logbitp-of-const-split
                                 `(logbitp ,x ,const))))


#||


(defstub foo (x) t)

(thm (implies (foo x)
              (logbitp x (lognot #x10001f00)))
     :hints(("Goal" :in-theory (enable logbitp-of-const-split
                                       bit-scan-rec)))
     :otf-flg t)

(thm (implies (foo x)
              (logbitp x #x10001f00))
     :hints(("Goal" :in-theory (enable logbitp-of-const-split
                                       bit-scan-rec)))
     :otf-flg t)


||#


(defsection equal-by-logbitp-hint
  :parents (bitops)
  :short "Basic automation for @(see equal-by-logbitp)."
  :long "<p>The @('equal-by-logbitp-hint') computed hint looks for goals of the
form:</p>

@({
 (implies (and hyp1 hyp2 ...)
          (equal lhs rhs))
})

<p>And automatically generates an appropriate @(':functional-instance') of the
@(see equal-by-logbitp) theorem.  A typical use of this hint might be:</p>

@({
 :hints((\"Goal\"
         :in-theory (enable foo bar))
        (and stable-under-simplificationp
             (equal-by-logbitp-hint)))
})

<p>Note that this hint is very aggressive.  For instance, it doesn't try to
determine whether @('lhs') and @('rhs') are numbers, it'll will try to use
@(see equal-by-logbitp) anyway.  Because of this, you would never want to add
this to the @(see default-hints).</p>"

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
  :short "Rewrite terms like @('(logbitp foo 7)') to @('(or (not (natp
foo)) (member-equal foo '(0 1 2)))')."

  :long "<p>This meta rule targets terms of the form</p>

@({
 (logbitp term const)
})

<p>where @('const') is a quoted constant, typically a number.  We know that
such a term can only be true when @('term') happens to be one of the bit
positions that has a @('1') bit set in @('const'), so we can split into cases
based on which bits of @('const') are set.</p>

<p>Note that this rule basically is going to split into @('n') cases, where
@('n') is the number of @('1') bits in @('const')!  Because of this we keep it
disabled.  But if you see a @('logbitp') term applied to a constant, you might
want to consider enabling this rule.</p>"

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
    (let* ((n (lnfix n))
           (m (lnfix m)))
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






(defsection equal-by-logbitp-hammer
  :parents (equal-by-logbitp)
  :short "Drastic automation for @(see equal-by-logbitp)."

  :long "<p>This is an enhanced version of @(see equal-by-logbitp-hint) that
also enables a bunch of case-splitting rules that allow @(see logbitp) to go
through functions like @(see ash), @(see loghead), @(see install-bit),
etc.</p>"

  (def-ruleset! logbitp-case-splits
    ;; Basic logbitp case-splitting rules to enable first
    '(logbitp-of-ash-split
      logbitp-of-loghead-split
      logbitp-of-logapp-split
      logbitp-of-logsquash-split
      logbitp-of-logrev-split))

  (def-ruleset! logbitp-case-splits+
    ;; Even more case splitting rules to enable after that
    '(logbitp-case-splits
      logbitp-when-bit
      b-not b-and b-ior b-xor b-eqv b-nand b-nor b-andc1 b-andc2
      b-orc1 b-orc2
      nfix ifix bfix))

  (defmacro equal-by-logbitp-hammer ()
    '(and stable-under-simplificationp
          '(:computed-hint-replacement
            ((and stable-under-simplificationp
                  '(:in-theory (e/d* (acl2::logbitp-of-const-split))))
             (and stable-under-simplificationp
                  '(:in-theory (e/d* (logbitp-case-splits
                                      logbitp-when-bit
                                      acl2::logbitp-of-const-split))))
             (and stable-under-simplificationp
                  (equal-by-logbitp-hint))
             (and stable-under-simplificationp
                  '(:in-theory (e/d* (logbitp-case-splits
                                      logbitp-when-bit
                                      acl2::logbitp-of-const-split
                                      b-xor b-ior b-and)))))
            :no-thanks t))))


(defsection equal-by-logbitp-witnessing
  (definstantiate equal-by-logbitp-instancing
    :predicate (equal x y)
    :vars (bit)
    :expr (equal (logbitp bit x) (logbitp bit y))
    :hints ('(:in-theory nil)))

  (defexample equal-by-logbitp-example
    :pattern (logbitp bit x)
    :templates (bit)
    :instance-rules (equal-by-logbitp-instancing))

  (defwitness unequal-by-logbitp-witnessing
    :predicate (not (equal x y))
    :expr (or (not (integerp x))
              (not (integerp y))
              (let ((bit (logbitp-mismatch x y)))
                (not (equal (logbitp bit x)
                            (logbitp bit y)))))
    :generalize (((logbitp-mismatch x y) . wbit))
    :hints ('(:in-theory '(logbitp-mismatch-correct
                           logbitp-mismatch-under-iff
                           ifix-when-integerp))))


  (def-witness-ruleset equal-by-logbitp-rules
    '(equal-by-logbitp-instancing
      equal-by-logbitp-example
      unequal-by-logbitp-witnessing))

  (defmacro logbitp-reasoning ()
    '(let ((witness-hint
            (witness :ruleset equal-by-logbitp-rules)))
       (and witness-hint
            (let* ((hint-body (cddr witness-hint))
                   (chr-forms (cadr witness-hint)))
              `(:computed-hint-replacement
                ,(append chr-forms
                         '((and stable-under-simplificationp
                                '(:in-theory (e/d* (acl2::logbitp-of-const-split))))
                           (and stable-under-simplificationp
                                '(:in-theory (e/d* (logbitp-case-splits
                                                    logbitp-when-bit
                                                    acl2::logbitp-of-const-split))))
                           (and stable-under-simplificationp
                                '(:in-theory (e/d* (logbitp-case-splits
                                                    logbitp-when-bit
                                                    acl2::logbitp-of-const-split
                                                    b-xor b-ior b-and))))))
                . ,hint-body))))))




