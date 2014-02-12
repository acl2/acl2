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
(include-book "logbitp-mismatch")
(include-book "clause-processors/witness-cp" :dir :system)
(include-book "std/util/wizard" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "integer-length"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))

; BOZOs:
;   - Document rulesets
;   - Document logbitp-reasoning and so on.

(defsection bitops/equal-by-logbitp
  :parents (bitops)
  :short "Introduces @('equal-by-logbitp'), a strategy for proving that @('a =
b') by showing that their bits are equal, and computed hints that can automate
the application of this strategy.")

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


(defsection equal-by-logbitp
  :parents (bitops/equal-by-logbitp logbitp)
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
                  (and (zp i)
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
  :parents (bitops/equal-by-logbitp)
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
determine whether @('lhs') and @('rhs') are numbers; it will try to use
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
  :parents (bitops/equal-by-logbitp logbitp)
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
  :parents (bitops/equal-by-logbitp)
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




(define logbitp-mismatch? ((x integerp)
                           (y integerp))
  (nfix (logbitp-mismatch x y))
  ///
  (local (in-theory (e/d (logbitp-mismatch)
                         (int-equiv))))
  (defcong int-equiv equal (logbitp-mismatch? x y) 1)
  (defcong int-equiv equal (logbitp-mismatch? x y) 2)
  (defthm logbitp-mismatch?-correct
    (implies (and (integerp x) (integerp y)
                  (not (equal x y)))
             (let ((i (logbitp-mismatch? x y)))
               (not (equal (logbitp i x) (logbitp i y)))))))


(defsection equal-by-logbitp-witnessing-rules
  (definstantiate equal-by-logbitp-instancing
    :predicate (equal x y)
    :vars (bit)
    :expr (equal (logbitp bit x) (logbitp bit y))
    :hints ('(:in-theory nil)))

  ;; (defexample equal-by-logbitp-example
  ;;   :pattern (logbitp bit x)
  ;;   :templates (bit)
  ;;   :instance-rules (equal-by-logbitp-instancing))

  (defwitness unequal-by-logbitp-witnessing
    :predicate (not (equal x y))
    :expr (or (not (integerp x))
              (not (integerp y))
              (let ((bit (hide (logbitp-mismatch x y))))
                (and (natp bit)
                     (not (equal (logbitp bit x)
                                 (logbitp bit y))))))
    :generalize (((hide (logbitp-mismatch x y)) . wbit))
    :hints ('(:in-theory (enable logbitp-mismatch-correct
                                 logbitp-mismatch-under-iff
                                 ifix-when-integerp)
              :expand ((:free (x) (hide x)))))))


(defines eqbylbp-collect-terms
  :verify-guards nil
  :prepwork ((local (defthm pseudo-term-listp-of-union
                      (implies (and (pseudo-term-listp a)
                                    (pseudo-term-listp b))
                               (pseudo-term-listp (union-equal a b))))))
  (define eqbylbp-collect-terms ((x pseudo-termp))
    :returns (terms pseudo-term-list-listp :hyp :guard)
    (b* (((when (or (atom x) (eq (car x) 'quote))) nil)
         (rest (eqbylbp-collect-terms-list (cdr x))))
      (if (eq (car x) 'logbitp)
          (cons (cdr x) rest)
        rest)))
  (define eqbylbp-collect-terms-list ((x pseudo-term-listp))
    :returns (terms pseudo-term-list-listp :hyp :guard)
    (if (atom x)
        nil
      (union-equal (eqbylbp-collect-terms (car x))
                   (eqbylbp-collect-terms-list (cdr x)))))
  ///
  (local (defthm pseudo-term-listp-implies-true-listp
           (implies (pseudo-term-list-listp x)
                    (true-listp x))))
  (verify-guards eqbylbp-collect-terms))

(define eqbylbp-check-witnesses ((x pseudo-term-listp)
                                   (rule wcp-witness-rule-p)
                                   (restriction-term pseudo-termp)
                                   state)
  :returns (mv (apply-witness-list boolean-listp)
               (new-terms pseudo-term-listp))
  (b* (((when (atom x)) (mv nil nil))
       ((wcp-witness-rule rule) rule)
       ((mv rest-apply rest-terms)
        (eqbylbp-check-witnesses (cdr x) rule restriction-term state))
       ((unless (mbt (and (pseudo-termp (car x))
                          (wcp-witness-rule-p rule))))
        (mv (cons nil rest-apply)
            rest-terms))
       ((mv unify-ok alist)
        (simple-one-way-unify rule.term (car x) nil))
       ((unless unify-ok)
        (mv (cons nil rest-apply)
            rest-terms))
       ((mv er val)
        (if (equal restriction-term ''t)
            (mv nil t)
          (witness-eval-restriction restriction-term alist state)))
       (- (and er
               (raise "Restriction term evaluation failed! ~x0" er)))
       ((when (or er (not val)))
        (mv (cons nil rest-apply)
            rest-terms))
       (new-term (substitute-into-term rule.expr alist)))
    (mv (cons t rest-apply) (cons new-term rest-terms)))
  ///
  (defthm eqbylbp-check-witnesses-len-of-apply-list
    (equal (len (mv-nth 0 (eqbylbp-check-witnesses x rule restriction state)))
           (len x))))

(define eqbylbp-simplify-each ((x pseudo-term-listp)
                               hint
                               state)
  :mode :program
  (b* (((when (atom x)) (value nil))
       ((er first) (easy-simplify-term1-fn
                    (car x) nil hint 'iff t t 1000 1000 state))
       ((er rest) (eqbylbp-simplify-each (cdr x) hint state)))
    (value (cons first rest))))

(define eqbylbp-is-var ((x pseudo-termp)
                        (var symbolp))
  (or (eq x var)
      (and (consp x)
           (eq (car x) 'nfix)
           (eq (cadr x) var))))

(define eqbylbp-solve-for-var ((x pseudo-termp)
                               (var symbolp)
                               (target pseudo-termp))
  :returns (mv ok
               (res pseudo-termp :hyp (and (pseudo-termp x)
                                           (pseudo-termp target))))
  (b* (((when (eqbylbp-is-var x var)) (mv t target))
       ((when (atom x)) (mv nil nil))
       ((when (eq (car x) 'unary--))
        (eqbylbp-solve-for-var (cadr x) var `(unary-- ,target)))
       ((unless (eq (car x) 'binary-+)) (mv nil nil))
       ((when (eqbylbp-is-var (cadr x) var))
        (mv t `(binary-+ ,target (unary-- ,(caddr x))))))
    (eqbylbp-solve-for-var
     (caddr x) var
     `(binary-+ ,target (unary-- ,(cadr x))))))

(define eqbylbp-collect-examples-for-target ((avail-logbitp-args pseudo-term-list-listp)
                                             (var symbolp)
                                             (target-logbitp-args pseudo-term-listp)
                                             (examples pseudo-term-listp))
  :verify-guards nil
  :returns (new-examples pseudo-term-listp
                         :hyp (and (pseudo-term-listp examples)
                                   (pseudo-term-list-listp avail-logbitp-args)
                                   (pseudo-term-listp target-logbitp-args)))
  (b* (((when (atom avail-logbitp-args)) examples)
       ((unless (equal (cadr (car avail-logbitp-args))
                       (cadr target-logbitp-args)))
        (eqbylbp-collect-examples-for-target
         (cdr avail-logbitp-args) var target-logbitp-args examples))
       ((mv ok res) (eqbylbp-solve-for-var (car (car avail-logbitp-args))
                                           var
                                           `(nfix ,(car target-logbitp-args))))
       ((unless ok)
        (eqbylbp-collect-examples-for-target
         (cdr avail-logbitp-args) var target-logbitp-args examples))
       (rest (eqbylbp-collect-examples-for-target
              (cdr avail-logbitp-args) var target-logbitp-args examples)))
    (if (member-equal res rest) rest (cons res rest)))
  ///
  (local (defthm true-listp-when-pseudo-term-listp
           (implies (pseudo-term-listp x)
                    (true-listp x))))
  (verify-guards eqbylbp-collect-examples-for-target))

(define eqbylbp-collect-examples-targets ((avail-logbitp-args pseudo-term-list-listp)
                                          (var symbolp)
                                          (target-logbitp-args pseudo-term-list-listp)
                                          (examples pseudo-term-listp))
  ;; Avail-logbitp-args are the (n x) from calls (logbitp n x) available by
  ;; instantiating an equality with logbitp by var.  We look for ways to
  ;; instantiate var such that these match similar pairs from
  ;; target-logbitp-args.  Returns the list of such terms (that we can
  ;; substitute for var to make some available term match a target term).
  :returns (new-examples pseudo-term-listp
                         :hyp (and (pseudo-term-listp examples)
                                   (pseudo-term-list-listp avail-logbitp-args)
                                   (pseudo-term-list-listp target-logbitp-args)))
  (if (atom target-logbitp-args)
      examples
    (eqbylbp-collect-examples-targets
     avail-logbitp-args var (cdr target-logbitp-args)
     (eqbylbp-collect-examples-for-target
      avail-logbitp-args var (car target-logbitp-args) examples))))


(define eqbylbp-eval-example ((rule wcp-instance-rule-p)
                              (alist pseudo-term-val-alistp)
                              (example pseudo-termp)
                              hint state)
  :mode :program
  :guard (eql (len (wcp-instance-rule->vars rule)) 1)
  ;; Tries instantiating rule using alist + binding of rule.vars (singleton) to example.
  ;; Returns the list of logbitp args present in the simplification of the result.
  (b* (((wcp-instance-rule rule) rule)
       (alist1 (append (pairlis$ rule.vars (list example))
                       alist))
       (newterm (wcp-beta-reduce-term (substitute-into-term rule.expr alist1)))
       ; (- (cw "Term: ~x0~%" newterm))
       ((mv erp newterm-rw state)
        (easy-simplify-term1-fn
         newterm nil hint 'iff t t 1000 1000 state))
       ; (- (cw "Rewritten: ~x0~%" newterm-rw))
       ((when erp)
        (raise "Error simplifying: ~x0" erp)
        (mv nil nil state))
       (includep (equal newterm-rw ''t)
        ;; nil
        )
       )
    (mv includep (eqbylbp-collect-terms newterm-rw) state)))
  

(define eqbylbp-try-example ((rule wcp-instance-rule-p)
                             (alist pseudo-term-val-alistp)
                             (example pseudo-termp)
                             (target-logbitp-args pseudo-term-list-listp)
                             hint state)
  :mode :program
  :guard (eql (len (wcp-instance-rule->vars rule)) 1)
  ;; :returns (mv (example? wcp-example-appsp)
  ;;              (new-logbitp-args pseudo-term-list-listp
  ;;                                :hyp (and (wcp-instance-rule-p rule)
  ;;                                          (pseudo-term-val-alistp alist)
  ;;                                          (pseudo-termp example)
  ;;                                          (pseudo-term-list-listp target-logbitp-args)))
  ;;              state1)
  (b* (((mv includep new-logbitp-args state)
        (eqbylbp-eval-example rule alist example hint state))
       ; (- (cw "Logbitp args for ~x0: ~x1~%" example new-logbitp-args))
       (intersection (intersection-equal new-logbitp-args target-logbitp-args))
       ((unless (or includep intersection))
        ; (cw "Rejected: ~x0 (produced: ~x1)~%" example new-logbitp-args)
        (mv nil target-logbitp-args state))
       (new-targets (set-difference-equal new-logbitp-args intersection)))
    (mv (list (make-wcp-example-app :instrule rule
                                    :bindings (list example)))
        (append new-targets target-logbitp-args)
        state)))

(define eqbylbp-try-examples ((rule wcp-instance-rule-p)
                              (alist pseudo-term-val-alistp)
                              (examples pseudo-term-listp)
                              (target-logbitp-args pseudo-term-list-listp)
                              hint state)
  ;; Examples are terms that we think might cause an instantiation of rule
  ;; (using substition alist) to match some target-logbitp-args.  We check each
  ;; such example and return:
  ;;  - a list of wcp-example-appsp derived from the examples that did
  ;;  - a new target-logbitp-args that includes any additional logbitp
  ;;  instances we accidentally introduced.
  :mode :program
  ;; :returns (mv (examples wcp-example-appsp)
  ;;              (new-logbitp-args pseudo-term-list-listp))
  (b* (((when (atom examples))
        (mv nil target-logbitp-args state))
       ((mv first-examples target-logbitp-args state)
        (eqbylbp-try-example rule alist (car examples) target-logbitp-args hint state))
       ((mv rest-examples target-logbitp-args state)
        (eqbylbp-try-examples rule alist (cdr examples) target-logbitp-args hint state)))
    (mv (append first-examples rest-examples) target-logbitp-args state)))
        
                             


(define eqbylbp-decide-examples-lit ((lit pseudo-termp)
                                      (var symbolp)
                                      (target-logbitp-args pseudo-term-list-listp)
                                      (rule wcp-instance-rule-p)
                                      (restriction-term pseudo-termp)
                                      hint
                                      state)
  :guard (eql (len (wcp-instance-rule->vars rule)) 1)
  :mode :program
  (b* (((unless (mbt (and (pseudo-termp lit)
                          (wcp-instance-rule-p rule)
                          (eql (len (wcp-instance-rule->vars rule)) 1))))
        (mv nil target-logbitp-args state))
       ((wcp-instance-rule rule) rule)
       ((mv unify-ok alist)
        (simple-one-way-unify rule.pred lit nil))
       ((unless unify-ok) (mv nil target-logbitp-args state))
       ((mv er res)
        (if (equal restriction-term ''t)
            (mv nil t)
          (witness-eval-restriction restriction-term alist state)))
       (- (and er
               (raise "Restriction term evaluation failed! ~x0" er)))
       ((unless (and (not er) res))
        (mv nil target-logbitp-args state))
       ((mv & avail-logbitp-args state)
        (eqbylbp-eval-example rule alist var hint state))
       ; (- (cw "Available: ~x0~%" avail-logbitp-args))
       (example-terms
        (eqbylbp-collect-examples-targets avail-logbitp-args
                                          var
                                          target-logbitp-args
                                          nil))
       ; (- (cw "Examples: ~x0~%" example-terms))
       ((mv examples target-logbitp-args state)
        (eqbylbp-try-examples rule alist example-terms target-logbitp-args hint state))
       ; (- (cw "Pruned examples: ~x0~%" examples))
       ((when examples)
        (mv examples target-logbitp-args state)))
    ;; Include the example consisting of just var itself, 
    (mv (list (make-wcp-example-app :instrule rule
                                    :bindings (list var)))
        (union-equal avail-logbitp-args target-logbitp-args)
        state)))

(define eqbylbp-decide-examples ((clause pseudo-term-listp)
                                 (var symbolp)
                                 (target-logbitp-args pseudo-term-list-listp)
                                 (rule wcp-instance-rule-p)
                                 (restriction-term pseudo-termp)
                                 hint state)
  :mode :program
  (b* (((when (atom clause)) (mv nil target-logbitp-args state))
       ((mv examples1 target-logbitp-args state)
        (eqbylbp-decide-examples-lit
         (car clause) var target-logbitp-args rule restriction-term hint state))
       ((mv rest-examples target-logbitp-args state)
        (eqbylbp-decide-examples
         (cdr clause) var target-logbitp-args rule restriction-term hint state)))
    (mv (cons examples1 rest-examples) target-logbitp-args state)))

(define eqbylbp-decide-examples-passes ((count posp)
                                        (clause pseudo-term-listp)
                                        (var symbolp)
                                        (target-logbitp-args pseudo-term-list-listp)
                                        (rule wcp-instance-rule-p)
                                        (restriction-term pseudo-termp)
                                        hint state)
  :mode :program
  (b* (((mv examples target-logbitp-args state)
        (eqbylbp-decide-examples
         clause var target-logbitp-args rule restriction-term hint state))
       (count (1- count))
       ((when (zp count))
        (mv examples target-logbitp-args state)))
    (eqbylbp-decide-examples-passes
     count clause var target-logbitp-args rule restriction-term hint state)))

(define wcp-example-apps-listp (x)
  (if (atom x)
      (eq x nil)
    (and (wcp-example-appsp (car x))
         (wcp-example-apps-listp (cdr x))))
  ///
  (defopen wcp-example-apps-listp-when-consp
    (wcp-example-apps-listp x)
    :hyp (consp x)
    :hint (:expand ((wcp-example-apps-listp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define eqbylbp-pair-hints ((witness-apps boolean-listp)
                            (examples wcp-example-apps-listp)
                            (rule wcp-witness-rule-p))
  :guard (eql (len witness-apps) (len examples))
  :returns (actions wcp-lit-actions-listp)
  (if (atom witness-apps)
      nil
    (cons (make-wcp-lit-actions :witnesses (and (car witness-apps)
                                                (mbt (wcp-witness-rule-p rule))
                                                (list rule))
                                :examples (and (mbt (wcp-example-appsp (car examples)))
                                               (car examples)))
          (eqbylbp-pair-hints (cdr witness-apps) (cdr examples) rule))))
  

(define eqbylbp-witness-hints ((clause pseudo-term-listp)
                               restrict
                               (passes posp)
                               simp-hint
                               state)
  :mode :program
  (b* ((witness-rule
        (cdr (assoc 'unequal-by-logbitp-witnessing
                    (table-alist 'witness-cp-witness-rules (w state)))))
       (instance-rule
        (cdr (assoc 'equal-by-logbitp-instancing
                    (table-alist 'witness-cp-instance-rules (w state)))))
       ((mv er restrict-term state)
        (translate restrict t nil t 'logbitp-reasoning (w state) state))
       ((when er)
        (raise "Translate failed: ~x0" er)
        (mv nil state))
       ((mv apply-witnesses new-lits)
        (eqbylbp-check-witnesses clause witness-rule restrict-term state))
       ; (- (cw "Apply-witnesses: ~x0~%New-lits: ~x1~%" apply-witnesses new-lits))
       ((mv er new-lits-simp state)
        (eqbylbp-simplify-each
         (wcp-beta-reduce-list new-lits) simp-hint state))
       ((when er)
        (raise "Simplify failed: ~x0" er)
        (mv nil state))
       (targets (eqbylbp-collect-terms-list (append new-lits-simp clause)))
       ; (- (cw "Targets: ~x0~%" targets))
       ((mv examples ?targets state)
        (eqbylbp-decide-examples-passes
         passes clause 'eqbylbp-index targets instance-rule restrict-term simp-hint state)))
    (mv (eqbylbp-pair-hints apply-witnesses examples witness-rule)
        state)))

(define logbitp-reasoning-fn (clause
                              restrict
                              passes
                              simp-hint
                              add-hints
                              stablep
                              state)
  
  :mode :program
  (b* (((unless stablep) (value nil))
       ((mv cp-hint state)
        (eqbylbp-witness-hints clause restrict passes simp-hint state)))
    (value `(:clause-processor (witness-cp clause ',cp-hint state)
             . ,add-hints))))

(defxdoc logbitp-reasoning
  :parents (bitops)
  :short "A computed hint for proving bit-twiddling theorems by smartly sampling bits"
  :long "<p>@('Logbitp-reasoning') is a computed hint for proving theorems
about bitvector operations.  Example usage:</p>
@({
 (defthm pass-context-of-ash
   (implies (equal (logand (ash mask (- (ifix n))) a1)
                   (logand (ash mask (- (ifix n))) a2))
            (equal (logand mask (ash a1 n))
                   (logand mask (ash a2 n))))
   :hints ((logbitp-reasoning)))
 })

<p>It works by:</p>
<ul>
<li>Creating <i>witnesses</i> for inequality hyps/equality conclusions, replacing
 @('(not (equal a b))') with:
@({
 (implies (and (integerp x) (integerp y))
          (and (natp bit)
               (not (equal (logbitp bit x)
                           (logbitp bit y)))))
 })
where @('bit') is a fresh variable,</li>
<li><i>Instantiating</i> equality hyps/inequality conclusions, replacing
@('(equal a b)') with @('(equal (logbitp bit a) (logbitp bit b))'), for one or
more several values of @('bit').</li>
</ul>

<p>The main work done by this computed hint is to decide how to instantiate
@('bit') for each of the equality hyps/inequality conclusions. To do this
we:</p>
<ol>
<li>Keep track of a list of logbitp term \"targets\", which we think of as
already appearing in our goal either due to witnessing or instantiation.</li>
<li>Try to instantiate equality hyps so as to create more occurrences of
existing targets.</li>
</ol>

<p>We take @('pass-context-of-ash') above as an example.</p>
<ol>

<li>First we find the literals of the clause that we'll create witnesses for --
in this case, the conclusion.  We'll introduce some new variable @('wbit') and
our new conclusion will be (omitting some type info that isn't directly
relevant)
@({
 (equal (logbitp wbit (logand mask (ash a1 n)))
        (logbitp wbit (logand mask (ash a2 n))))
 })
</li>

<li>Next we simplify this new conclusion and extract the logbitp terms that the
simplified term contains:
@({
 (logbitp wbit mask)
 (logbitp (+ (- (ifix n)) wbit) a1)
 (logbitp (+ (- (ifix n)) wbit) a2)
 })
These are now our target terms.</li>

<li>Next we look for instantiations of our hypothesis that, when simplified,
will contain one or more of these target terms.  To do this, we first
instantiate it with a variable @('ibit'), obtaining:
@({
 (equal (logbitp ibit (logand (ash mask (- (ifix n))) a1))
        (logbitp ibit (logand (ash mask (- (ifix n))) a1)))
 })
</li>
<li>Then we simplify the result and extract the resulting logbitp terms:
@({
  (logbitp ibit a1)
  (logbitp ibit a2)
  (logbitp (+ (ifix n) (nfix ibit)) mask)
 })
</li>

<li>Now we try to find values of @('ibit') that will make one or more of these
results match one or more of the target terms.  We immediately find that by
setting @('ibit') to @('(+ (- (nfix n)) wbit)') we create some matches.  So we
decide to instantiate the hyp using this term as our bit index.</li>

<li>All of the above was done just to compute a hint.  The actual hint we
provide is a call to @(see witness-cp), a clause processor that supports this
sort of witness creation and instantiation, with instructions to do the
witnessing and instantiation steps that we've settled on.  Once this clause
processor runs, the resulting proof splits into 8 subgoals that are all quickly
proved.</li>

</ol>

<p>@('Logbitp-reasoning') is a macro that can take a few optional arguments,
but reasonable defaults (in the invocation below) are provided:</p>
@({
 :hints ((logbitp-reasoning
          :restrict t
          :passes 1
          :simp-hint (:in-theory
                       (enable* logbitp-case-splits
                                logbitp-when-bit
                                logbitp-of-const-split))
          :add-hints (:in-theory
                      (enable* logbitp-case-splits
                               logbitp-when-bit
                               logbitp-of-const-split))))
 })

<p>The meanings of these:</p>

<ul> <li>@(':restrict') is a term in the
variables @('x') and @('y') that restricts the equality literals to which we
will apply witnessing/instantiation.  For example,
 @({
   :restrict (or (and (consp x) (eq (car x) 'binary-logand))
                 (and (consp y) (eq (car y) 'binary-logand)))
  })
will cause the hint to ignore any equality literals that don't have an argument
that is a call of logand.</li>
<li>@(':passes') determines the number of passes through the clause we use to
collect instantiations and target terms.  Instantiations can add new targets,
and the more targets there are, the more instantiations may be found.</li>
<li>@(':simp-hint') is the hint given to the simplifier while deciding on the
instantiations.</li>
<li>@(':add-hints') are hints given at the same time as the clause processor hint.</li>
</ul>
")

(defmacro logbitp-reasoning (&key 
                             (restrict 't)
                             (passes '1)
                             (simp-hint '(:in-theory
                                          (enable* logbitp-case-splits
                                                   logbitp-when-bit
                                                   acl2::logbitp-of-const-split)))
                             (add-hints '(:in-theory
                                          (e/d* (logbitp-case-splits
                                                 logbitp-when-bit
                                                 acl2::logbitp-of-const-split)))))
  `(logbitp-reasoning-fn
    clause ',restrict ',passes ',simp-hint ',add-hints
    stable-under-simplificationp state))



;; Demo
(local
 (defthm pass-context-of-logapp
   (implies (and (equal (logand (ash mask (- (nfix n))) b1)
                        (logand (ash mask (- (nfix n))) b2))
                 (equal (logand (loghead n mask) a1)
                        (logand (loghead n mask) a2)))
            (equal (logand mask (logapp n a1 b1))
                   (logand mask (logapp n a2 b2))))
   :hints ((logbitp-reasoning))))

(local
 (defthm pass-context-of-ash
   (implies (equal (logand (ash mask (- (ifix n))) a1)
                   (logand (ash mask (- (ifix n))) a2))
            (equal (logand mask (ash a1 n))
                   (logand mask (ash a2 n))))
   :hints ((logbitp-reasoning))))
       
                               






