; TRUTH - integer truth table representation
; Copyright (C) 2017 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "TRUTH")

(include-book "std/util/define" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/bitops/extra-defs" :dir :system)
(include-book "centaur/bitops/logrepeat" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/bitops/trailing-0-count" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (in-theory (disable unsigned-byte-p logmask)))
(local (std::add-default-post-define-hook :fix))

(defmacro hq (x) `(acl2::hq ,x))

;; NUMVARS is the maximum number of variables we'll use.  Truth tables are
;; integers of 2^NUMVARS bits.

;;

; Matt K. mod: Avoid ACL2(p) error from logapp-right-assoc (clause-processor
; returns more than two values).
(set-waterfall-parallelism nil)

(defxdoc truth
  :parents (acl2::boolean-reasoning)
  :short "Library for reasoning about and computing with integer-encoded truth tables."
  :long "<p>A Boolean function of @('n') variables can be represented using a
bit vector of @('2^n') bits.  Operators such as AND/OR/XOR can then be computed
using @('logand'), @('logior'), and @('logxor'), respectively.  This library
provides utilities for using this encoding of Boolean functions and reasoning
about them.  It is particularly useful in the @(see aignet::rewrite) AIG
transformation.</p>")

(local (xdoc::set-default-parents truth))

(define true  () -1)
(define false () 0)



(define truth-eval ((truth integerp) (env natp) (numvars natp))
  :guard (unsigned-byte-p numvars env)
  (b* ((env (mbe :logic (loghead (nfix numvars) (nfix env)) :exec env)))
    (logbitp env truth))
  ///
  (defthm truth-eval-of-lognot
    (equal (truth-eval (lognot truth) env numvars)
           (not (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable truth-eval))))

  (defthm truth-eval-of-logand
    (equal (truth-eval (logand x y) env numvars)
           (and (truth-eval x env numvars)
                (truth-eval y env numvars)))
  :hints(("Goal" :in-theory (enable truth-eval))))

  (defthm truth-eval-of-logior
    (equal (truth-eval (logior x y) env numvars)
           (or (truth-eval x env numvars)
               (truth-eval y env numvars)))
  :hints(("Goal" :in-theory (enable truth-eval))))

  (defthm truth-eval-of-logxor
    (equal (truth-eval (logxor x y) env numvars)
           (xor (truth-eval x env numvars)
                (truth-eval y env numvars)))
  :hints(("Goal" :in-theory (enable truth-eval))))

  (defthm truth-eval-of-consts
    (and (equal (truth-eval 0 env numvars) nil)
         (equal (truth-eval -1 env numvars) t))))


(define env-lookup ((var natp) (env natp))
  (logbitp (lnfix var) (lnfix env)))

(define env-update ((var natp) (val booleanp) (env natp))
  :returns (new-env natp :rule-classes :type-prescription)
  (bitops::install-bit var (bool->bit val) (lnfix env))
  ///
  (defthm env-lookup-of-env-update-split
    (equal (env-lookup var (env-update var1 val env))
           (if (equal (nfix var) (nfix var1))
               (acl2::bool-fix val)
             (env-lookup var env)))
    :hints(("Goal" :in-theory (enable* env-lookup
                                       (:ruleset arith-equiv-forwarding)))))

  (defthm env-update-of-env-update
    (equal (env-update n x (env-update n y env))
           (env-update n x env)))

  (defthm env-update-swap
    (implies (not (nat-equiv var1 var2))
             (equal (env-update var2 val2 (env-update var1 val1 env))
                    (env-update var1 val1 (env-update var2 val2 env))))
    :hints(("Goal" :in-theory (enable env-update))))

  (defthm env-update-redundant
    (implies (iff (env-lookup n env) val)
             (equal (env-update n val env)
                    (nfix env)))
    :hints(("Goal" :in-theory (enable env-lookup)))))




(local (encapsulate nil
         (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

         (defthm mod-when-less
           (implies (and (natp n) (natp w)
                         (< n w))
                    (equal (mod n w) n)))

         (defthm mod-when-greater
           (implies (and (natp n) (natp w)
                         (<= w n)
                         (syntaxp (not (equal w ''0))))
                    (equal (mod n w)
                           (mod (- n w) w))))

         (defthm natp-of-mod
           (implies (and (natp n) (natp w))
                    (natp (mod n w)))
           :hints(("Goal" :in-theory (disable (force)))))

         (defthm mod-less-than-modulus
           (implies (and (natp n) (posp w))
                    (< (mod n w) w)))))

(local (defthm lognot-of-logapp
         (equal (lognot (logapp w a b))
                (logapp w (lognot a) (lognot b)))
         :hints(("Goal" :in-theory (e/d* (ihsext-inductions)
                                         (bitops::logapp-of-i-0))
                 :induct (logapp w a b)
                 :expand ((:free (a b) (logapp w a b)))))))




;; e.g. variable 0 initially generates 10
;; for numvars=4, we need to generate 1010 1010  1010 1010
;; meaning double it 3 times.  Start with n = 1.
(define var-repetitions ((n natp) (val natp) (numvars natp))
  :guard (and (<= n numvars)
              (unsigned-byte-p (ash 1 n) val))
  ;; :guard-hints (("goal" :Expand ((ash 1 (+ 1 n)))
  ;;                :in-theory (enable logcons)))
  :verify-guards nil
  ;; :measure (nfix (- (nfix numvars) (nfix n)))
  :returns (rep-val natp :rule-classes :type-prescription)
  :enabled t
  (mbe :logic (logrepeat (ash 1 (- (nfix numvars) (nfix n)))
                         (ash 1 (nfix n))
                         (nfix val))
       :exec (b* ((shift (ash 1 n))
                  ((when (mbe :logic (zp (- numvars n))
                              :exec (eql n numvars)))
                   val))
               (var-repetitions (+ 1 n)
                                (logapp shift val val) numvars)))
  ///
  (verify-guards var-repetitions
    :hints(("Goal" :in-theory (e/d* (logcons) (acl2::exponents-add))
            :expand ((ash 1 (+ (- n) numvars))
                     (ash 1 (+ 1 n)))))))

  ;; (local (defthmd loghead-less-than-ash-gen-lemma
  ;;          (implies (natp i)
  ;;                   (< (loghead m x) (ash 1 (+ i (nfix m)))))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
  ;;                                             ihsext-recursive-redefs)))))

  ;; (local (defthm loghead-less-than-ash-gen
  ;;          (implies (<= (nfix m) (ifix n))
  ;;                   (< (loghead m x) (ash 1 n)))
  ;;          :hints (("goal" :use ((:instance loghead-less-than-ash-gen-lemma
  ;;                                 (i (- (ifix n) (nfix m)))))))))

  ;; (local (defthm loghead-when-less-than-ash
  ;;          (implies (and (< (loghead n x) (ash 1 (+ -1 n)))
  ;;                        (posp n))
  ;;                   (equal (loghead n x)
  ;;                          (loghead (1- n) x)))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
  ;;                                             ihsext-recursive-redefs)))))

  ;; (local (defthm logbitp-of-loghead-past-range
  ;;          (implies (< (nfix n) (nfix m))
  ;;                   (equal (logbitp n (loghead m x))
  ;;                          (logbitp n x)))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
  ;;                                            ihsext-recursive-redefs)))))

  ;; (local (defthmd loghead-of-plus-one
  ;;          (implies (posp n)
  ;;                   (equal (loghead n env)
  ;;                          (+ (if (logbitp (1- n) env) (ash 1 (1- n)) 0)
  ;;                             (loghead (1- n) env))))
  ;;          :hints(("Goal" :in-theory (enable* loghead** logbitp**
  ;;                                             ihsext-inductions)
  ;;                  :induct t)
  ;;                 (and stable-under-simplificationp
  ;;                      '(:expand ((ash 1 (+ -1 n)))
  ;;                        :in-theory (enable logcons))))))



  ;; (defret var-repetitions-invar
  ;;   (equal (truth-eval rep-val env numvars)
  ;;          (truth-eval (nfix val) (loghead n (nfix env)) numvars))
  ;;   :hints(("Goal" :in-theory (enable truth-eval
  ;;                                     bitops::logbitp-of-ash-split)
  ;;           :induct t)
  ;;          (and stable-under-simplificationp
  ;;               '(:in-theory (enable loghead-of-plus-one)))))

  ;; (defret var-repetitions-size
  ;;   (implies (and (<= (nfix n) numvars)
  ;;                 (natp numvars)
  ;;                 (unsigned-byte-p (ash 1 (nfix n)) val))
  ;;            (unsigned-byte-p (ash 1 numvars) rep-val))
  ;;   :hints (("goal" :induct t
  ;;            :expand ((ash 1 (+ 1 (nfix n))))
  ;;            :in-theory (enable logcons))))


  ;; (local (defun var-repetitions-masked-size-ind (m n val numvars)
  ;;          (declare (xargs :measure (nfix (- (nfix numvars) (nfix n)))))
  ;;          (b* ((n (lnfix n))
  ;;               (shift (ash 1 n))
  ;;               (val (mbe :logic (loghead shift (nfix val)) :exec val))
  ;;               ((when (mbe :logic (zp (- (nfix numvars) n))
  ;;                           :exec (eql n numvars)))
  ;;                (list m val)))
  ;;            (var-repetitions-masked-size-ind
  ;;             (+ shift m)
  ;;             (+ 1 n)
  ;;             (logapp shift val val)
  ;;             numvars))))


  ;; (local (defthm loghead-of-logapp
  ;;          (implies (<= (nfix w1) (nfix w2))
  ;;                   (equal (loghead w2 (logapp w1 a b))
  ;;                          (logapp w1 a (loghead (- (nfix w2) (nfix w1)) b))))
  ;;          :hints ((bitops::logbitp-reasoning))))

  ;; (local (defthm unsigned-byte-p-implies-width-natp
  ;;          (implies (unsigned-byte-p n x)
  ;;                   (natp n))
  ;;          :hints(("Goal" :in-theory (enable unsigned-byte-p)))
  ;;          :rule-classes :forward-chaining))

  ;; (local (defthm plus-minus-*-n
  ;;          (implies (and (syntaxp (quotep n))
  ;;                        (natp n))
  ;;                   (equal (+ (- x) (* n x))
  ;;                          (* (+ -1 n) x)))))

  ;; (defret var-repetitions-negated-masked-size
  ;;   (implies (and (<= (nfix n) numvars)
  ;;                 (natp numvars)
  ;;                 (unsigned-byte-p m (loghead (ash 1 (nfix n)) (lognot (nfix val)))))
  ;;            (unsigned-byte-p (- (ash 1 numvars) (- (ash 1 (nfix n)) m))
  ;;                             (loghead (ash 1 numvars) (lognot rep-val))))
  ;;   :hints (("goal" :induct (var-repetitions-masked-size-ind m n val numvars)
  ;;            :expand ((ash 1 (+ 1 (nfix n)))
  ;;                     (var-repetitions n val numvars))
  ;;            :in-theory (enable logcons))))

  ;; (local (defthm lognot-equal-ash-implies
  ;;          (implies (and (equal (loghead nn (lognot val))
  ;;                               (ash val m))
  ;;                        (natp nn))
  ;;                   (unsigned-byte-p nn (ash val m)))))


  ;; (local (defthmd ash-is-unsigned-byte-p-implies-x-is-unsigned-byte-p
  ;;          (implies (and (natp m)
  ;;                        (unsigned-byte-p n (ash x m))
  ;;                        (natp x))
  ;;                   (unsigned-byte-p n x))
  ;;          :hints (("goal" :induct (ash x m)
  ;;                   :in-theory (enable* ihsext-inductions
  ;;                                      ihsext-recursive-redefs)))))

  ;; (local (defthm lognot-equal-ash-implies2
  ;;          (implies (and (equal (loghead nn (lognot val))
  ;;                               (ash val m))
  ;;                        (natp m)
  ;;                        (natp nn)
  ;;                        (natp val))
  ;;                   (unsigned-byte-p nn val))
  ;;          :hints (("goal" :use ((:instance ash-is-unsigned-byte-p-implies-x-is-unsigned-byte-p
  ;;                                 (x val) (n nn)))))))

  ;; (local (defthm logapp-of-equal-loghead
  ;;          (implies (and (equal x (loghead n y))
  ;;                        (syntaxp (not (equal x y))))
  ;;                   (equal (logapp n x z)
  ;;                          (logapp n y z)))))

  ;; (local (in-theory (disable loghead-when-less-than-ash)))

  ;; (local (defthm logapp-of-ash-when-unsigned-byte-p
  ;;          (implies (And (natp m)
  ;;                        (equal (loghead nn (ash val m))
  ;;                               (ash val m)))
  ;;                   (equal (ash (logapp nn val val2) m)
  ;;                          (logapp nn (ash val m) (ash val2 m))))
  ;;          :hints ((bitops::logbitp-reasoning :prune-examples nil))))


  ;; (local (defthm ash-of-logapp-lemma
  ;;          (implies (and (equal (loghead nn (lognot val))
  ;;                               (ash val m))
  ;;                        (natp m)
  ;;                        (natp val))
  ;;                   (equal (ash (logapp nn val val) m)
  ;;                          (logapp nn (lognot val) (ash val m))))
  ;;          :hints ((bitops::logbitp-reasoning :prune-examples nil)
  ;;                  '(:do-not-induct t))))


  ;; (local (defthm ash-of-logapp-lemma
  ;;          (implies (and (equal (loghead m val) 0)
  ;;                        (< (nfix m) (nfix nn)))
  ;;                   (equal (logtail m (logapp nn val2 val))
  ;;                          (logapp nn (logtail m (loghead nn val2)) (logtail m val))))
  ;;          :hints ((bitops::logbitp-reasoning :prune-examples nil)
  ;;                  '(:do-not-induct t))
  ;;          :otf-flg t))

  ;; ;; (defthm tail-equals-head-of-lognot-implies-head-0
  ;; ;;   (implies (equal (loghead n (lognot val))
  ;; ;;                   (logtail m val))
  ;; ;;            (equal (loghead m val) 0))
  ;; ;;   :hints ((bitops::logbitp-reasoning :prune-examples nil)))

  ;; (local (defthm loghead-of-logapp-when-less
  ;;          (implies (<= (nfix n) (nfix m))
  ;;                   (equal (loghead n (logapp m a b))
  ;;                          (loghead n a)))
  ;;          :hints ((bitops::logbitp-reasoning))))

  ;; (defret var-repetitions-negated
  ;;   (implies (and (posp n)
  ;;                 (<= n numvars)
  ;;                 (< (nfix m) (ash 1 n))
  ;;                 (natp numvars)
  ;;                 (equal (loghead (ash 1 (nfix n)) (lognot (nfix val)))
  ;;                        (logtail m (nfix val)))
  ;;                 (equal (loghead m (nfix val)) 0))
  ;;            (equal (loghead (ash 1 numvars) (lognot rep-val))
  ;;                   (logtail m rep-val)))
  ;;   :hints (("goal" :induct t
  ;;            :expand ((ash 1 (+ 1 n)))
  ;;            :in-theory (enable logcons)))))

(local (defthm posp-of-ash-1
         (implies (not (negp n))
                  (posp (Ash 1 n)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs)))
         :rule-classes :type-prescription))


(local (defthmd logbitp-in-terms-of-loghead
         (iff (logbitp n x)
              (<= (ash 1 (nfix n)) (loghead (+ 1 (nfix n)) x)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))

(local
 (defthmd ash-1-monotonic
   (implies (and (< a b)
                 (natp a)
                 (integerp b))
            (< (ash 1 a)
               (ash 1 b)))
   :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))
   :rule-classes ((:rewrite) (:linear))))

(local (defthmd loghead-less-than-ash
         (implies (not (negp n))
                  (< (loghead n x) (ash 1 n)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))
         :rule-classes (:rewrite :linear)))

(define var ((n natp) (numvars natp))
  :guard (< n numvars)
  :returns (var-enc natp :rule-classes :type-prescription)
  :guard-hints (("goal" :Expand ((ash 1 (+ 1 n)))
                 :in-theory (enable logcons)))
  :prepwork ((local (defthm plus-minus-*2
                      (equal (+ (- x) (* 2 x))
                             (fix x)))))
  (b* ((n (lnfix n))
       (numvars (lnfix numvars))
       (w (ash 1 n))
       (rep (ash (logmask w) w)))
    (var-repetitions (+ 1 n) rep numvars))
  ///

  (local (defthm loghead-less-than-ash-times-2-linear
           (implies (natp n)
                    (< (loghead (+ 1 n) x) (* 2 (ash 1 n))))
           :hints (("goal" :use ((:instance loghead-less-than-ash
                                  (n (+ 1 n))))
                    :expand ((ash 1 (+ 1 n)))
                    :in-theory (enable logcons)))
           :rule-classes :linear))

  (local (defthm product-of-ash
           (implies (and (natp a) (natp b))
                    (equal (* (ash 1 a) (ash 1 b))
                           (ash 1 (+ a b))))
           :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))))

  (local (defthm mod-of-ash-1-is-loghead
           (implies (and (natp n) (integerp x))
                    (equal (mod x (ash 1 n))
                           (loghead n x)))
           :hints(("Goal" :in-theory (enable loghead
                                             bitops::ash-is-expt-*-x)))))

  (defret logbitp-of-var
    (implies (< (nfix n) (nfix numvars))
             (equal (logbitp env var-enc)
                    (and (< (nfix env) (ash 1 numvars))
                         (logbitp n (nfix env)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ;; truth-eval env-lookup
                                      bitops::logbitp-of-ash-split
                                      loghead-less-than-ash
                                      )))
            (and stable-under-simplificationp
                 '(:in-theory (enable logbitp-in-terms-of-loghead)))))
    ;; :hints (("goal" :use eval-of-var
    ;;          :in-theory (e/d (truth-eval env-lookup)
    ;;                          (eval-of-var var)))))

  (defret eval-of-var
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-eval var-enc env numvars)
                    (env-lookup n env)))
    :hints (("goal" :in-theory (e/d (truth-eval env-lookup
                                                loghead-less-than-ash)
                                    (var)))))

  (defret var-size-basic
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p (ash 1 numvars) var-enc))
    :hints (("goal" :expand ((ash 1 (+ 1 (nfix n)))
                             (ash 1 numvars))
             :in-theory (enable logcons))))

  (defret var-size
    (implies (and (natp m)
                  (<= (ash 1 numvars) m)
                  (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p m var-enc))
    :hints (("goal" :use var-size-basic
             :in-theory (disable var-size-basic))))

  (local (defthm lognot-of-ash
           (implies (natp n)
                    (equal (lognot (ash x n))
                           (logapp n -1 (lognot x))))
           :hints((bitops::logbitp-reasoning))))

  (local (defthm loghead-of-logapp
           (implies (<= (nfix w1) (nfix w2))
                    (equal (loghead w2 (logapp w1 a b))
                           (logapp w1 a (loghead (- (nfix w2) (nfix w1)) b))))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm plus-minus-*-n
           (implies (and (syntaxp (quotep n))
                         (natp n))
                    (equal (+ (- x) (* n x))
                           (* (+ -1 n) x)))))

  (local (defthm plus-*-minus-n
           (implies (and (syntaxp (quotep n))
                         (natp n))
                    (equal (+ x (- (* n x)))
                           (- (* (+ -1 n) x))))))

  (local (defthm loghead-lognot-logmask
           (equal (loghead n (lognot (logmask n))) 0)
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm var-negated-masked-lemma
           (implies (natp n)
                    (equal (LOGHEAD (* 2 n)
                                    (LOGAPP n
                                            -1
                                            (LOGNOT (LOGMASK n))))
                           (logmask n)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm plus-minus-times-2
           (equal (+ n (- (* 2 n)) m)
                  (+ (- n) m))))



  (defret var-negated-masked-size
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p (- (ash 1 numvars) (ash 1 (nfix n)))
                              (loghead (ash 1 numvars) (lognot var-enc))))
    :hints (("Goal" :use ((:instance bitops::size-of-logrepeat-by-data-size
                           (n (+ (ash 1 numvars) (- (ash 1 (nfix n)))))
                           (m (ash 1 (nfix n)))
                           (times (ash 1 (+ -1 numvars (- (nfix n)))))
                           (width (ash 1 (+ 1 (nfix n))))
                           (data (LOGAPP (ASH 1 (NFIX N))
                                      -1
                                      (LOGNOT (LOGMASK (ASH 1 (NFIX N)))))))
                          (:instance var-negated-masked-lemma
                           (n (ash 1 (nfix n)))))
             :expand ((ash 1 (+ 1 (nfix n)))
                      (ash 1 numvars))
             :in-theory (e/d (logcons
                              ash-1-monotonic)
                             (bitops::size-of-logrepeat-by-data-size
                              var-negated-masked-lemma))))
    ;; :hints (("Goal" :use ((:instance var-repetitions-negated-masked-size
    ;;                        (n (+ 1 (nfix n)))
    ;;                        (m (ash 1 (nfix n)))
    ;;                        (val (ash (logmask (ash 1 (nfix n))) (ash 1 (nfix n))))))
    ;;          :expand ((ash 1 (+ 1 (nfix n))))
    ;;          :in-theory (e/d (logcons)
    ;;                          (var-repetitions-negated-masked-size))))
    )

  (local (defthm loghead-of-plus-last-bit
           (implies (and (natp n) (integerp x))
                    (equal (loghead (+ 1 n) (+ x (ash 1 n)))
                           (if (< (loghead (+ 1 n) x) (ash 1 n))
                               (+ (loghead (+ 1 n) x) (ash 1 n))
                             (- (loghead (+ 1 n) x) (ash 1 n)))))
           :hints (("goal" :induct (loghead n x)
                    :in-theory (enable* ihsext-inductions
                                       ihsext-recursive-redefs
                                       logcons)))))

  (local (defun less-when-loghead-less-ind (w n num)
           (if (zp n)
               (list w num)
             (less-when-loghead-less-ind (logcdr w) (1- n) (1- num)))))

  (local (defthm not-even-when-loghead-0
           (implies (and (equal (logcar x) 1)
                         (integerp y))
                    (not (equal (* 2 y) x)))))

  (local (defthm less-when-loghead-less
           (implies (and (integerp w)
                         (natp num) (natp n)
                         (< n num)
                         (< w (ash 1 num))
                         (< (loghead (+ 1 n) w) (ash 1 n)))
                    (< (+ w (ash 1 n)) (ash 1 num)))
           :hints (("goal" :induct (less-when-loghead-less-ind w n num)
                    :expand ((loghead (+ 1 n) w)
                             (loghead 1 w)
                             (ash 1 n)
                             (ash 1 num))
                    :in-theory (enable logcons)))))

  (defret var-negated
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (equal (loghead (ash 1 numvars) (lognot var-enc))
                    (logtail (ash 1 (nfix n)) var-enc)))
    :hints ((bitops::logbitp-reasoning))))

(local (defthmd loghead-less-than-ash-nfix
         (< (loghead n x) (ash 1 (nfix n)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))

(define truth-norm ((truth integerp) (numvars natp))
  :returns (norm-truth)
  (loghead (ash 1 (lnfix numvars)) truth)
  ///
  (local (in-theory (enable loghead-less-than-ash-nfix)))

  (local (defthm logbitp-of-loghead-past-range
           (implies (< (nfix n) (nfix m))
                    (equal (logbitp n (loghead m x))
                           (logbitp n x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs)))))

  (defret truth-eval-of-truth-norm
    (equal (truth-eval (truth-norm truth numvars) env numvars)
           (truth-eval truth env numvars))
    :hints(("Goal" :in-theory (enable truth-eval))))

  (defret truth-norm-of-truth-norm
    (equal (truth-norm (truth-norm truth numvars) numvars)
           (truth-norm truth numvars)))

  (defret size-of-truth-norm
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size norm-truth)))

  (defret truth-eval-of-truth-norm-minus1
    (implies (and (syntaxp (and (quotep truth)
                                (quotep numvars)))
                  (equal truth (truth-norm -1 numvars)))
             (truth-eval truth env numvars))
    :hints(("Goal" :in-theory (disable truth-norm)))))



(local
 (encapsulate nil
   (local (defthmd loghead-of-install-bit-lemma
           (implies (posp i)
                    (Equal (loghead (+ i (nfix n)) (install-bit n v x))
                           (install-bit n v (loghead (+ i (nfix n)) x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs)
                   :induct (logbitp n x))
                  (and stable-under-simplificationp
                       '(:expand ((:free (x) (install-bit n v x))
                                  (:free (x) (install-bit 0 v x)))
                         ;; :in-theory (enable bitops::equal-logcons-strong)
                         )))))

   (defthm loghead-of-install-bit
     (implies (< (nfix n) (nfix w))
              (Equal (loghead w (install-bit n v x))
                     (install-bit n v (loghead w x))))
     :hints(("Goal" :use ((:instance loghead-of-install-bit-lemma
                           (i (- (nfix w) (nfix n))))))))))

(define positive-cofactor ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  :returns (cofactor integerp :rule-classes :type-prescription)
  (B* ((mask (logand (var n numvars) (truth-norm truth numvars))))
    (logior mask (ash mask (- (ash 1 (lnfix n))))))
  ///


  (local (defthm logcons-logcar-plus-logcdr
           (implies (and (equal y (+ (logcdr x) z))
                         (integerp z))
                    (equal (logcons (logcar x) y)
                           (+ (ifix x) (logcons 0 z))))
           :hints(("Goal" :in-theory (enable bitops::equal-logcons-strong)))))

  (local (defthm plus-ash-1-is-install-bit
           (implies (and (not (logbitp n x))
                         (integerp x))
                    (equal (+ (ash 1 (nfix n)) x)
                           (install-bit n 1 x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              install-bit**)
                   :induct (logbitp n x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable bitops::equal-logcons-strong))))))

  ;; (local (defthm logcdr-of-non-integer
  ;;          (implies (not (integerp x))
  ;;                   (equal (logcdr x) 0))
  ;;          :hints (("goal" :in-theory (enable logcdr)))))

  ;; (local (defthmd install-bit-is-plus-ash-1-special
  ;;          (implies (case-split (not (equal (install-bit n 1 x) (ifix x))))
  ;;                   (equal (install-bit n 1 x)
  ;;                          (+ (ash 1 (nfix n)) (ifix x))))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
  ;;                                             ihsext-recursive-redefs
  ;;                                             install-bit**)
  ;;                  :induct (logbitp n x))
  ;;                 (and stable-under-simplificationp
  ;;                      '(:in-theory (enable bitops::equal-logcons-strong))))))

  (local (defthmd logbitp-past-width-lemma
           (implies (and (unsigned-byte-p n x)
                         (natp i))
                    (not (logbitp (+ i n) x)))
           :hints (("goal" :induct (logbitp n x)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))

  (local (defthm not-logbitp-of-var-past-range
           (implies (and (< (nfix n) numvars)
                         (natp numvars)
                         (not (unsigned-byte-p numvars (nfix i))))
                    (not (logbitp i (var n numvars))))
           :hints (("goal" :use ((:instance var-size-basic)
                                 (:instance logbitp-past-width-lemma
                                  (n (ash 1 numvars))
                                  (i (- (nfix i) (ash 1 numvars)))
                                  (x (var n numvars))))
                    :in-theory (e/d (unsigned-byte-p  bitops::expt-2-is-ash)
                                    (var-size-basic))))))

  (local (defthm logbitp-n-of-plus-ash-1-n
           (implies (integerp x)
                    (equal (logbitp n (+ (ash 1 (nfix n)) x))
                           (not (logbitp n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm <-ash-by-unsigned-byte-p
           (implies (unsigned-byte-p n x)
                    (< x (ash 1 n)))
           :hints(("Goal" :in-theory (enable unsigned-byte-p
                                             bitops::ash-is-expt-*-x)))))

  (defret positive-cofactor-correct
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-eval cofactor env numvars)
                    (truth-eval truth (env-update n t env) numvars)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable env-lookup env-update truth-eval
                                     bitops::logbitp-of-ash-split
                                     truth-norm)))
           (and stable-under-simplificationp
                '(:cases ((logbitp n (nfix env)))))
           (and stable-under-simplificationp
                '(:cases ((unsigned-byte-p numvars (+ (ash 1 (nfix n))
                                (loghead numvars (nfix env)))))))))

  (defret positive-cofactor-size-basic
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p (ash 1 numvars) cofactor)))

  (defret positive-cofactor-size
    (implies (and (natp m)
                  (<= (ash 1 numvars) m)
                  (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p m cofactor))
    :hints (("goal" :use positive-cofactor-size-basic
             :in-theory (disable positive-cofactor-size-basic))))

  (defthm positive-cofactor-of-truth-norm
    (equal (positive-cofactor n (truth-norm truth numvars) numvars)
           (positive-cofactor n truth numvars)))

  (defthm truth-norm-of-positive-cofactor
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-norm (positive-cofactor n truth numvars) numvars)
                    (positive-cofactor n truth numvars)))
    :hints(("Goal" :in-theory (e/d (truth-norm) (positive-cofactor))))))

(define negative-cofactor ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  :returns (cofactor integerp :rule-classes :type-prescription)
  (B* ((mask (logand (lognot (var n numvars))
                     (loghead (ash 1 (lnfix numvars)) truth))))
    (logior mask (ash mask (ash 1 (lnfix n)))))
  ///
  (local (in-theory (disable logmask)))


  (local (defthm logcons-logcar-plus-logcdr
           (implies (and (equal y (+ (logcdr x) z))
                         (integerp z))
                    (equal (logcons (logcar x) y)
                           (+ (ifix x) (logcons 0 z))))
           :hints(("Goal" :in-theory (enable bitops::equal-logcons-strong)))))

  (local (defthmd plus-1-lognot
           (equal (+ 1 (lognot x)) (- (ifix x)))
           :hints(("Goal" :in-theory (enable lognot)))))

  (local (defthmd logcdr-of-minus
           (implies (integerp x)
                    (equal (logcdr (- x))
                           (+ (b-not (logcar x)) (lognot (logcdr x)))))
           :hints(("Goal" :in-theory (enable bitops::minus-to-lognot)))))

  (local (defthm minus-ash-1-is-install-bit
           (implies (and (logbitp n x)
                         (integerp x))
                    (equal (+ (- (ash 1 (nfix n))) x)
                           (install-bit n 0 x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              install-bit**)
                   :induct (logbitp n x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable bitops::equal-logcons-strong
                                            logcdr-of-minus
                                            plus-1-lognot))))))

  (local (defthm install-bit-0-less-than-x
           (implies (natp x)
                    (<= (install-bit n 0 x) x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              install-bit**)
                   :induct (logbitp n x)))
           :rule-classes :linear))

  (local (defthm ash-1-greater-than-loghead
           (implies (natp n)
                    (< (loghead n x) (ash 1 n)))
           :hints (("goal" :in-theory (enable* ihsext-inductions
                                               ihsext-recursive-redefs)))
           :rule-classes :linear))

  ;; (local (defthm logcdr-of-non-integer
  ;;          (implies (not (integerp x))
  ;;                   (equal (logcdr x) 0))
  ;;          :hints (("goal" :in-theory (enable logcdr)))))

  ;; (local (defthmd install-bit-is-plus-ash-1-special
  ;;          (implies (case-split (not (equal (install-bit n 1 x) (ifix x))))
  ;;                   (equal (install-bit n 1 x)
  ;;                          (+ (ash 1 (nfix n)) (ifix x))))
  ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
  ;;                                             ihsext-recursive-redefs
  ;;                                             install-bit**)
  ;;                  :induct (logbitp n x))
  ;;                 (and stable-under-simplificationp
  ;;                      '(:in-theory (enable bitops::equal-logcons-strong))))))

  (local (defthmd logbitp-past-width-lemma
           (implies (and (unsigned-byte-p n x)
                         (natp i))
                    (not (logbitp (+ i n) x)))
           :hints (("goal" :induct (logbitp n x)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))

  (local (defthm not-logbitp-of-var-past-range
           (implies (and (< (nfix n) numvars)
                         (natp numvars)
                         (not (unsigned-byte-p numvars (nfix i))))
                    (not (logbitp i (var n numvars))))
           :hints (("goal" :use ((:instance var-size)
                                 (:instance logbitp-past-width-lemma
                                  (n (ash 1 numvars))
                                  (i (- (nfix i) (ash 1 numvars)))
                                  (x (var n numvars))))
                    :in-theory (e/d (unsigned-byte-p  bitops::expt-2-is-ash)
                                    (var-size))))))

  (local (defthmd minus-of-logcons
           (equal (- (logcons a b))
                  (logcons a (+ (b-not a) (lognot b))))
           :hints(("Goal" :in-theory (enable logcons lognot b-not)))))

  (local (defthm logbitp-n-of-minus-ash-1-n
           (implies (integerp x)
                    (equal (logbitp n (+ (- (ash 1 (nfix n))) x))
                           (not (logbitp n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              minus-of-logcons
                                              plus-1-lognot)))))

  (local (defthm gte-ash-when-logbitp
           (implies (and (logbitp n x)
                         (natp x))
                    (<= (ash 1 (nfix n)) x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defret negative-cofactor-correct
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-eval cofactor env numvars)
                    (truth-eval truth (env-update n nil env) numvars)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable env-lookup env-update truth-eval
                                     bitops::logbitp-of-ash-split
                                     bitops::logbitp-of-loghead-split)))
           (and stable-under-simplificationp
                '(:cases ((logbitp n (nfix env)))))))

  (local (defun size-of-logand-ind (n m a b)
           (if (zp m)
               (list n a b)
             (size-of-logand-ind (1- n) (1- m) (logcdr a) (logcdr b)))))

  (local (defthmd logand-0-by-loghead-lemma
           (implies (and (unsigned-byte-p m a)
                         (equal 0 (loghead m b)))
                    (equal (logand a b) 0))
           :hints (("goal" :induct (size-of-logand-ind m m a b)
                    :expand ((loghead m b)
                             (unsigned-byte-p m a))))))

  (defthmd size-of-logand-by-size-of-loghead
    (implies (and (unsigned-byte-p m a)
                  (unsigned-byte-p n (loghead m b)))
             (unsigned-byte-p n (logand a b)))
    :hints (("goal" :induct (size-of-logand-ind n m a b)
             :expand ((loghead m b)
                      (:free (n a b) (unsigned-byte-p n (logcons a b))))
             :in-theory (enable logand-0-by-loghead-lemma))))

  (defret negative-cofactor-size-basic
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p (ash 1 numvars) cofactor))
    :hints (("goal" :use ((:instance size-of-logand-by-size-of-loghead
                           (a (loghead (ash 1 numvars) truth)) (b (lognot (var n numvars)))
                           (m (ash 1 numvars)) (n (- (ash 1 numvars) (ash 1 (nfix n))))))
             :in-theory (enable ash-1-monotonic))))

  (defret negative-cofactor-size
    (implies (and (natp m)
                  (<= (ash 1 numvars) m)
                  (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p m cofactor))
    :hints (("goal" :use negative-cofactor-size-basic
             :in-theory (disable negative-cofactor-size-basic))))

  (defthm negative-cofactor-of-truth-norm
    (equal (negative-cofactor n (truth-norm truth numvars) numvars)
           (negative-cofactor n truth numvars))
    :hints(("Goal" :in-theory (enable truth-norm))))

  (defthm truth-norm-of-negative-cofactor
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-norm (negative-cofactor n truth numvars) numvars)
                    (negative-cofactor n truth numvars)))
    :hints(("Goal" :in-theory (e/d (truth-norm) (negative-cofactor))))))

;; (define depends-on ((n natp) (truth integerp) (numvars natp))
;;   :guard (< n numvars)
;;   (not (equal (truth-norm (positive-cofactor n truth numvars) numvars)
;;               (truth-norm truth numvars)))
;;   ///
;;   (defthm depends-on-correct
;;     (implies (and (not (depends-on n truth numvars))
;;                   (< (nfix n) (nfix numvars)))
;;              (equal (truth-eval truth (env-update n val env) numvars)
;;                     (truth-eval truth env numvars)))
;;     :hints (("goal" :use ((:instance truth-eval-of-truth-norm
;;                            (env (env-update n val env)))
;;                           (:instance truth-eval-of-truth-norm
;;                            (truth (positive-cofactor n truth numvars))
;;                            (env (env-update n val env)))
;;                           (:instance truth-eval-of-truth-norm)
;;                           (:instance truth-eval-of-truth-norm
;;                            (truth (positive-cofactor n truth numvars))))
;;              :in-theory (disable truth-eval-of-truth-norm)))))

(local (defthmd logcons-logcar-plus-logcdr
         (implies (and (equal y (+ (logcdr x) z))
                       (integerp z))
                  (equal (logcons (logcar x) y)
                         (+ (ifix x) (logcons 0 z))))
         :hints(("Goal" :in-theory (enable bitops::equal-logcons-strong)))))

(local (defthmd plus-ash-1-is-install-bit
         (implies (and (not (logbitp n x))
                       (integerp x))
                  (equal (install-bit n 1 x)
                         (+ (ash 1 (nfix n)) x)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs
                                            install-bit**)
                 :induct (logbitp n x))
                (and stable-under-simplificationp
                     '(:in-theory (enable bitops::equal-logcons-strong))))))



  
(local (defthmd plus-1-lognot
         (equal (+ 1 (lognot x)) (- (ifix x)))
         :hints(("Goal" :in-theory (enable lognot)))))

(local (defthmd logcdr-of-minus
         (implies (integerp x)
                  (equal (logcdr (- x))
                         (+ (b-not (logcar x)) (lognot (logcdr x)))))
         :hints(("Goal" :in-theory (enable bitops::minus-to-lognot)))))

(local (defthmd minus-ash-1-is-install-bit
         (implies (and (logbitp n x)
                       (integerp x))
                  (equal (install-bit n 0 x)
                         (+ (- (ash 1 (nfix n))) x)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs
                                            install-bit**)
                 :induct (logbitp n x))
                (and stable-under-simplificationp
                     '(:in-theory (enable bitops::equal-logcons-strong
                                          logcdr-of-minus
                                          plus-1-lognot))))))

(define depends-on ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  (B* ((var (var n numvars))
       (truth (truth-norm truth numvars)))
    (not (equal (logand (lognot var) truth)
                (ash (logand var truth)
                     (- (ash 1 (lnfix n)))))))
  ///

  (defthm depends-on-of-truth-norm
    (equal (depends-on n (truth-norm truth numvars) numvars)
           (depends-on n truth numvars)))

  (local (in-theory (enable logcons-logcar-plus-logcdr
                            plus-ash-1-is-install-bit
                            minus-ash-1-is-install-bit)))

  (local (defthmd equal-implies-logbitp-equal
           (implies (equal (logand a b) (logand c d))
                    (iff (and (logbitp n a) (logbitp n b))
                         (and (logbitp n c) (logbitp n d))))
           :hints ((acl2::logbitp-reasoning))))


  (local (defun find-equal-logand-terms (clause)
           (if (atom clause)
               nil
             (let ((lit (car clause)))
               (case-match lit
                 (('not ('equal ('binary-logand a b)
                                ('binary-logand c d)))
                  `((a ,a) (b ,b) (c ,c) (d ,d)))
                 (& (find-equal-logand-terms (cdr clause))))))))

  (local (in-theory (enable loghead-less-than-ash)))


  ;; (local (defthm install-bit-redundant
  ;;          (implies (equal (logbit n x) (bfix val))
  ;;                   (equal (install-bit n val x) (ifix x)))
  ;;          :hints (("goal" :in-theory (enable* arith-equiv-forwarding)
  ;;                   :use ((:instance BITOPS::INSTALL-BIT-WHEN-REDUNDANT
  ;;                          (n n) (x x) (b (bfix val))))))))

  (local (defthm logbitp-n-of-plus-ash-1-n
           (implies (integerp x)
                    (equal (logbitp n (+ (ash 1 (nfix n)) x))
                           (not (logbitp n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (in-theory (enable bitops::logbitp-of-loghead-split
                            ash-1-monotonic)))



  (local (defthm gte-ash-when-logbitp
           (implies (and (logbitp n x)
                         (natp x))
                    (<= (ash 1 (nfix n)) x))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))


    (local (defthm loghead-plus-ash-lte-ash-when-not-logbitp
             (implies (and (< (nfix n) numvars)
                           (natp numvars)
                           (not (logbitp n x)))
                      (< (+ (loghead numvars x) (ash 1 (nfix n)))
                         (ash 1 numvars)))
             :hints (("goal" :use ((:instance plus-ash-1-is-install-bit
                                    (x (loghead numvars x)))
                                   (:instance bitops::unsigned-byte-p-of-install-bit
                                    (i n) (n numvars) (x (loghead numvars x)) (v 1)))
                      :in-theory (e/d (unsigned-byte-p
                                       bitops::expt-2-is-ash)
                                      (plus-ash-1-is-install-bit
                                       bitops::unsigned-byte-p-of-install-bit))))
             :rule-classes :linear))

  (defthm depends-on-correct
    (implies (and (not (depends-on n truth numvars))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval truth (env-update n val env) numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable truth-eval env-update truth-norm))
           (and stable-under-simplificationp
                '(:cases ((logbitp n (nfix env)))))
           (and stable-under-simplificationp
                (let ((conjuncts (find-equal-logand-terms clause)))
                  (and conjuncts
                       `(:use ((:instance equal-implies-logbitp-equal
                                (n (loghead numvars (nfix env)))
                                . ,conjuncts)
                               (:instance equal-implies-logbitp-equal
                                (n (install-bit n (bool->bit val)
                                                (loghead numvars (nfix env))))
                                . ,conjuncts))))))
           (and stable-under-simplificationp
                '(:cases ((eql 1 (bool->bit val))))))
    :otf-flg t))


(define depends-on-witness ((n natp) (truth integerp) (numvars natp))
  ;; Returns an env such that the value of truth under that env differs from
  ;; that of the env with the nth bit set to 1.
  :guard (< n numvars)
  :returns (diff-env natp :rule-classes :type-prescription)
  (B* ((var (var n numvars))
       (truth (truth-norm truth numvars))
       (diff (logxor (logand (lognot var) truth)
                     (ash (logand var truth)
                          (- (ash 1 (lnfix n)))))))
    (bitops::trailing-0-count diff))
  ///

  ;; (fty::deffixequiv bitops::trailing-0-count

  ;; (local (defthm logbitp-of-trailing-0-count

  (local (defthmd trailing-0-count-of-logxor-when-not-equal
           (implies (not (equal (ifix x) (ifix y)))
                    (b* ((count (bitops::trailing-0-count (logxor x y))))
                      (iff (logbitp count x)
                           (not (logbitp count y)))))
           :hints (("goal" :induct (logxor x y)
                    :in-theory (enable* bitops::ihsext-recursive-redefs
                                        bitops::ihsext-inductions
                                        bitops::trailing-0-count)))))

  (local (defthmd trailing-0-count-bound-when-unsigned-byte-p
           (implies (and (unsigned-byte-p n x)
                         (posp n))
                    (< (bitops::trailing-0-count x) n))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions
                                               bitops::trailing-0-count)))))

  (local (defthm var-negated-inverse
           (implies (and (< (nfix n) numvars)
                         (natp numvars))
                    (equal (logtail (ash 1 (nfix n)) (var n numvars))
                           (loghead (ash 1 numvars) (lognot (var n numvars)))))))

  (local (in-theory (disable var-negated)))

  ;; (local (defthm unsigned-byte-p-of-logxors
  ;;          (implies (and (unsigned-byte-p n x)
  ;;                        (unsigned-byte-p n y))
  ;;                   (unsigned-byte-p n (logxor x y)))))

  (local (defthm loghead-when-less-than-ash
           (implies (and (natp x) (< x (ash 1 (nfix n))))
                    (equal (loghead n x) x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (in-theory (enable bitops::logbitp-of-loghead-split
                            plus-ash-1-is-install-bit
                            ash-1-monotonic)))

  ;; (local (defun plus-ash-overflow-ind (n numvars x)
  ;;          (if (zp n)
  ;;              (list numvars x)
  ;;            (plus-ash-overflow-ind (1- n) (1- numvars) (logcdr x)))))

  (local (defthmd plus-ash-overflows-implies-logbitp
           (implies (and (not (logbitp n x))
                         (< x (ash 1 numvars))
                         (< n numvars)
                         (natp x) (natp numvars) (natp n))
                    (< (+ (ash 1 n) x) (ash 1 numvars)))
           :hints (("goal" :use ((:instance bitops::unsigned-byte-p-of-install-bit
                                  (n numvars)
                                  (i n) (v 1) (x x)))
                    :in-theory (disable bitops::unsigned-byte-p-of-install-bit))
                   (and stable-under-simplificationp
                        '(:in-theory (enable unsigned-byte-p
                                             bitops::expt-2-is-ash))))))
  
  (defret depends-on-witness-correct
    (implies (and (natp numvars)
                  (< (nfix n) numvars)
                  (depends-on n truth numvars))
             (not (equal (truth-eval truth (env-update n t diff-env) numvars)
                         (truth-eval truth diff-env numvars))))
    :hints (("goal" :in-theory (enable depends-on truth-eval truth-norm env-update))
            (acl2::use-termhint
             (b* ((var (var n numvars))
                  (truth (truth-norm truth numvars))
                  (var-0-part (logand (lognot var) truth))
                  (var-1-part (ash (logand var truth) (- (ash 1 (nfix n)))))
                  (diff (logxor var-0-part var-1-part))
                  (count (bitops::trailing-0-count diff))
                  ((when (<= (ash 1 numvars) count))
                   `'(:use ((:instance trailing-0-count-bound-when-unsigned-byte-p
                             (n (ash 1 numvars)) (x ,(hq diff))))))
                  ((when (and (not (logbitp n count))
                              (<= (+ (ash 1 numvars) (- (ash 1 (nfix n)))) count)))
                   `'(:use ((:instance plus-ash-overflows-implies-logbitp
                             (x ,(hq count)) (n (nfix n)))))))
               `'(:use ((:instance trailing-0-count-of-logxor-when-not-equal
                         (x ,(hq var-0-part)) (y ,(hq var-1-part))))))))))


(defsection depends-on-of-operators

  (defthm depends-on-of-logand
    (implies (and (not (depends-on n x numvars))
                  (not (depends-on n y numvars))
                  (natp numvars)
                  (< (nfix n) numvars))
             (not (depends-on n (logand x y) numvars)))
    :hints (("goal" :use ((:instance depends-on-witness-correct
                           (truth (logand x y))))
             :in-theory (disable depends-on-witness-correct
                                 depends-on-correct))
            (acl2::use-termhint
             (b* ((env (depends-on-witness n (logand x y) numvars))
                  (env1 (env-update n t env))
                  ((unless (equal (truth-eval x env1 numvars) (truth-eval x env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth x) (val t) (env ,(hq env))))))
                  ((unless (equal (truth-eval y env1 numvars) (truth-eval y env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth y) (val t) (env ,(hq env)))))))
               nil))))

  (defthm depends-on-of-logior
    (implies (and (not (depends-on n x numvars))
                  (not (depends-on n y numvars))
                  (natp numvars)
                  (< (nfix n) numvars))
             (not (depends-on n (logior x y) numvars)))
    :hints (("goal" :use ((:instance depends-on-witness-correct
                           (truth (logior x y))))
             :in-theory (disable depends-on-witness-correct
                                 depends-on-correct))
            (acl2::use-termhint
             (b* ((env (depends-on-witness n (logior x y) numvars))
                  (env1 (env-update n t env))
                  ((unless (equal (truth-eval x env1 numvars) (truth-eval x env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth x) (val t) (env ,(hq env))))))
                  ((unless (equal (truth-eval y env1 numvars) (truth-eval y env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth y) (val t) (env ,(hq env)))))))
               nil))))

  (defthm depends-on-of-logxor
    (implies (and (not (depends-on n x numvars))
                  (not (depends-on n y numvars))
                  (natp numvars)
                  (< (nfix n) numvars))
             (not (depends-on n (logxor x y) numvars)))
    :hints (("goal" :use ((:instance depends-on-witness-correct
                           (truth (logxor x y))))
             :in-theory (disable depends-on-witness-correct
                                 depends-on-correct))
            (acl2::use-termhint
             (b* ((env (depends-on-witness n (logxor x y) numvars))
                  (env1 (env-update n t env))
                  ((unless (equal (truth-eval x env1 numvars) (truth-eval x env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth x) (val t) (env ,(hq env))))))
                  ((unless (equal (truth-eval y env1 numvars) (truth-eval y env numvars)))
                   `'(:use ((:instance depends-on-correct
                             (truth y) (val t) (env ,(hq env)))))))
               nil))))

  (defthm depends-on-of-lognot
    (implies (and (natp numvars)
                  (< (nfix n) numvars))
             (iff (depends-on n (lognot x) numvars)
                  (depends-on n x numvars)))
    :hints ((acl2::use-termhint
             (b* (((mv dep indep) (if (depends-on n x numvars)
                                      (mv x (lognot x))
                                    (mv (lognot x) x)))
                  (env (depends-on-witness n dep numvars)))
               `'(:use ((:instance depends-on-witness-correct
                         (truth ,(hq dep)))
                        (:instance depends-on-correct
                         (truth ,(hq indep)) (val t) (env ,(hq env))))
                  :in-theory (disable depends-on-correct
                                      depends-on-witness-correct))))))

  ;; (defthm depends-on-of-truth-norm
  ;;   (implies (and (natp numvars)
  ;;                 (< (nfix n) numvars))
  ;;            (iff (depends-on n (truth-norm x numvars) numvars)
  ;;                 (depends-on n x numvars)))
  ;;   :hints ((acl2::use-termhint
  ;;            (b* (((mv dep indep) (if (depends-on n x numvars)
  ;;                                     (mv x (truth-norm x numvars))
  ;;                                   (mv (truth-norm x numvars) x)))
  ;;                 (env (depends-on-witness n dep numvars)))
  ;;              `'(:use ((:instance depends-on-witness-correct
  ;;                        (truth ,(hq dep)))
  ;;                       (:instance depends-on-correct
  ;;                        (truth ,(hq indep)) (val t) (env ,(hq env))))
  ;;                 :in-theory (disable depends-on-correct
  ;;                                     depends-on-witness-correct))))))
  )


(define env-mismatch-aux ((n natp)
                          (truth integerp)
                          (env1 natp)
                          (env2 natp)
                          (numvars natp))
  :guard (<= n numvars)
  :measure (nfix (- (nfix numvars) (nfix n)))
  :returns (var natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        0)
       ((when (and (depends-on n truth numvars)
                   (xor (env-lookup n env1)
                        (env-lookup n env2))))
        (lnfix n)))
    (env-mismatch-aux (+ 1 (lnfix n)) truth env1 env2 numvars))
  ///
  (defret env-mismatch-aux-bound
    (implies (posp numvars)
             (< var numvars)))

  (defret env-mismatch-aux-when-mismatch
    (implies (and (depends-on m truth numvars)
                  (xor (env-lookup m env1)
                       (env-lookup m env2))
                  (< (nfix m) (nfix numvars))
                  ;; (natp numvars)
                  (<= (nfix n) (nfix m)))
             (and (depends-on var truth numvars)
                  (iff (env-lookup var env1)
                       (not (env-lookup var env2)))
                  (< var numvars)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (local (defthm loghead-plus-1-equal-when-loghead-equal
           (implies (and (iff (env-lookup n env1)
                              (env-lookup n env2))
                         (equal (loghead n (nfix env1))
                                (loghead n (nfix env2))))
                    (equal (equal (loghead (+ 1 (nfix n)) (nfix env1))
                                  (loghead (+ 1 (nfix n)) (nfix env2)))
                           t))
           :hints (("goal" :in-theory (enable env-lookup))
                   (bitops::logbitp-reasoning))))

  (local (in-theory (enable bitops::logbitp-of-install-bit-split)))

  (local (defthm loghead-plus-1-equal-when-loghead-equal-update
           (implies (and (equal (loghead n (nfix env1))
                                (loghead n (nfix env2)))
                         (equal val (env-lookup n env1)))
                    (equal (equal (loghead (+ 1 (nfix n)) (nfix env1))
                                  (loghead (+ 1 (nfix n))
                                           (env-update n val env2)))
                           t))
           :hints (("goal" :in-theory (enable env-lookup env-update))
                   (bitops::logbitp-reasoning))))

  (local (defthm env-mismatch-aux-of-env-update-less
           (implies (< (nfix m) (nfix n))
                    (equal (env-mismatch-aux n truth env1 (env-update m val env2) numvars)
                           (env-mismatch-aux n truth env1 env2 numvars)))))

  (local
   (defun env-mismatch-aux-when-eval-mismatch-ind (n truth env1 env2 numvars)
     (declare (xargs :measure (nfix (- (nfix numvars) (nfix n)))))
     (b* (((when (zp (- (nfix numvars) (nfix n))))
           (list truth env1 env2))
          ((when (and (depends-on n truth numvars)
                      (xor (env-lookup n env1)
                           (env-lookup n env2))))
           (lnfix n))
          ((when (xor (env-lookup n env1)
                      (env-lookup n env2)))
           (env-mismatch-aux-when-eval-mismatch-ind
            (+ 1 (lnfix n)) truth env1 (env-update n (env-lookup n env1) env2) numvars)))
       (env-mismatch-aux-when-eval-mismatch-ind (+ 1 (lnfix n)) truth env1 env2 numvars))))
                             
  (local (defthmd loghead-equal-when-loghead-greater-equal
           (implies (and (equal (loghead n x) (loghead n y))
                         (<= (nfix m) (nfix n)))
                    (equal (loghead m x) (loghead m y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm truth-eval-equal-when-loghead-equal
           (implies (and (<= (nfix numvars) (nfix n))
                         (equal (loghead n (nfix env1))
                                (loghead n (nfix env2))))
                    (equal (equal (truth-eval truth env1 numvars)
                                  (truth-eval truth env2 numvars))
                           t))
           :hints (("goal" :in-theory (enable truth-eval)
                    :use ((:instance loghead-equal-when-loghead-greater-equal
                           (m numvars) (x (nfix env1)) (y (nfix env2))))))))
  
  (defret env-mismatch-aux-when-eval-mismatch
    (implies (and (not (equal (truth-eval truth env1 numvars)
                              (truth-eval truth env2 numvars)))
                  (equal (loghead n (nfix env1)) (loghead n (nfix env2))))
             (and (depends-on var truth numvars)
                  (iff (env-lookup var env1)
                       (not (env-lookup var env2)))
                  (< var (nfix numvars))
                  (implies (natp numvars)
                           (< var numvars))))
    :hints (("goal" :induct (env-mismatch-aux-when-eval-mismatch-ind
                             n truth env1 env2 numvars)))))

(define env-mismatch ((truth integerp)
                      (env1 natp)
                      (env2 natp)
                      (numvars natp))
  :returns (var natp :rule-classes :type-prescription)
  (env-mismatch-aux 0 truth env1 env2 numvars)
  ///
  (defret env-mismatch-bound
    (implies (posp numvars)
             (< var numvars))
    :rule-classes (:rewrite :linear))

  (defret env-mismatch-when-mismatch
    (implies (and (depends-on m truth numvars)
                  (xor (env-lookup m env1)
                       (env-lookup m env2))
                  (< (nfix m) (nfix numvars)))
             (and (depends-on var truth numvars)
                  (iff (env-lookup var env1)
                       (not (env-lookup var env2)))
                  (< var (nfix numvars))
                  (implies (natp numvars)
                           (< var numvars)))))

  (defret env-mismatch-when-eval-mismatch
    (implies (and (not (equal (truth-eval truth env1 numvars)
                              (truth-eval truth env2 numvars))))
             (and (depends-on var truth numvars)
                  (iff (env-lookup var env1)
                       (not (env-lookup var env2)))
                  (< var (nfix numvars))
                  (implies (natp numvars)
                           (< var numvars))))))
             
  
    

    


(define is-xor-with-var ((n natp) (truth integerp) (numvars natp))
  :short "Checks whether the given truth table is the xor of variable n with something.
           If so, the other input to the xor is the negative cofactor of the truth
          table with n."
  :guard (< n numvars)
  (equal (truth-norm (positive-cofactor n truth numvars) numvars)
         (truth-norm (lognot (negative-cofactor n truth numvars)) numvars))
  ///
  (defthm is-xor-with-var-correct
    (implies (and (is-xor-with-var n truth numvars)
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval (logxor (negative-cofactor n truth numvars) (var n numvars)) env numvars)
                    (truth-eval truth env numvars)))
    :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                           (truth (positive-cofactor n truth numvars)))
                          (:instance truth-eval-of-truth-norm
                           (truth (lognot (negative-cofactor n truth numvars)))))
             :in-theory (disable truth-eval-of-truth-norm)
             :cases ((env-lookup n env)))))

  (defthm is-xor-with-var-of-truth-norm
    (equal (is-xor-with-var n (truth-norm truth numvars) numvars)
           (is-xor-with-var n truth numvars))))


;; (define swap-vars ((n natp) (m natp) (truth integerp) (numvars natp))
;;   :guard (and (< n numvars) (< m numvars))
;;   :returns (swapped-truth integerp :rule-classes :type-prescription)
;;   (b* ((xn1 (positive-cofactor n truth numvars))
;;        (xn0 (negative-cofactor n truth numvars))
;;        (xn1m1 (positive-cofactor m xn1 numvars))
;;        (xn1m0 (negative-cofactor m xn1 numvars))
;;        (xn0m1 (positive-cofactor m xn0 numvars))
;;        (xn0m0 (negative-cofactor m xn0 numvars))
;;        (mvar (var m numvars))
;;        (nvar (var n numvars))
;;        (~mvar (lognot mvar))
;;        (~nvar (lognot nvar))
;;        ;; want (if n (if m xn1m1 xn0m1) (if m xn1m0 xn0m0))
;;        (n1case (logior (logand mvar xn1m1)
;;                        (logand ~mvar xn0m1)))
;;        (n0case (logior (logand mvar xn1m0)
;;                        (logand ~mvar xn0m0))))
;;     (logior (logand nvar n1case)
;;             (logand ~nvar n0case)))
;;   ///
;;   (defret eval-of-swap-vars
;;     (implies (and (< (nfix n) (nfix numvars))
;;                   (< (nfix m) (nfix numvars)))
;;              (equal (truth-eval swapped-truth env numvars)
;;                     (truth-eval truth
;;                                 (env-update n (env-lookup m env)
;;                                             (env-update m (env-lookup n env) env))
;;                                 numvars)))))


(defsection logbitp-loghead-of-add-theory
  (local (defun logbitp-of-plus-ind (n c a b)
           (if (zp n)
               (list a b c)
             (logbitp-of-plus-ind
              (1- n) (b-ior (b-and (logcar a) (logcar b))
                            (b-ior (b-and c (logcar a))
                                   (b-and c (logcar b))))
              (logcdr a) (logcdr b)))))

  (local (defthm logbitp-of-plus-lemma
           (implies (and (integerp a) (integerp b) (bitp c))
                    (Equal (logbitp n (+ c a b))
                           (equal 1 (b-xor (logbit n a)
                                           (b-xor (logbit n b)
                                                  (bool->bit
                                                   (<= (ash 1 (nfix n))
                                                       (+ c (loghead n a)
                                                          (loghead n b)))))))))
           :hints (("goal" :induct (logbitp-of-plus-ind n c a b)
                    :in-theory (e/d* (logcons
                                      bool->bit b-and bitp)
                                     ( ;; loghead-by-bounds
                                      acl2::loghead-identity
                                      bitops::logbitp-when-bitmaskp))
                    :expand ((:free (x) (logbitp n x))
                             (:free (x) (loghead n x))
                             (:free (x) (logbitp 0 x))
                             (ash 1 (nfix n))
                             (ash 1 n))))))

  (defthmd logbitp-of-plus
    (implies (and (integerp a) (integerp b))
             (Equal (logbitp n (+ a b))
                    (equal 1 (b-xor (logbit n a)
                                    (b-xor (logbit n b)
                                           (bool->bit
                                            (<= (ash 1 (nfix n))
                                                (+ (loghead n a)
                                                   (loghead n b)))))))))
    :hints (("Goal" :use ((:instance logbitp-of-plus-lemma
                           (c 0))))))


  (local (defthm loghead-of-plus-lemma
           (implies (and (integerp a) (integerp b) (bitp c))
                    (Equal (loghead n (+ c a b))
                           (let ((sum (+ c (loghead n a) (loghead n b))))
                             (if (<= (ash 1 (nfix n)) sum)
                                 (- sum (ash 1 (nfix n)))
                               sum))))
           :hints (("goal" :induct (logbitp-of-plus-ind n c a b)
                    :in-theory (e/d* (
                                     logcons
                                     bool->bit b-and bitp)
                                     ( ;; loghead-by-bounds
                                      acl2::loghead-identity))
                    :expand ((:free (x) (loghead n x))
                             (ash 1 (nfix n))
                             (ash 1 n))))))

  (defthmd loghead-of-plus
    (implies (and (integerp a) (integerp b))
             (Equal (loghead n (+ a b))
                    (let ((sum (+ (loghead n a) (loghead n b))))
                      (if (<= (ash 1 (nfix n)) sum)
                          (- sum (ash 1 (nfix n)))
                        sum))))
    :hints (("Goal" :use ((:instance loghead-of-plus-lemma
                           (c 0)))))))


;; BOZO consider moving these to shareable books
(local
 (defsection logbitp-of-plus-nonoverlap-theory

   (local (defun logbitp-ash-ind (n m x)
            (if (zp n)
                (list m x)
              (logbitp-ash-ind (1- n) (1- m) (logcdr x)))))

   (defthm logbitp-of-plus-ash-unset
     (implies (and (integerp x)
                   (natp m)
                   (not (logbitp (double-rewrite m) x)))
              (equal (logbitp n (+ x (ash 1 m)))
                     (or (equal (nfix n) m) (logbitp n x))))
     :hints (("goal" :induct (logbitp-ash-ind n m x)
              :in-theory (enable* ihsext-recursive-redefs))))

   (local (defthm logcdr-minus-logcons-0
            (equal (logcdr (- (logcons 0 x)))
                   (- (ifix x)))
            :hints(("Goal" :in-theory (enable bitops::minus-to-lognot)))))

   (defthm logbitp-of-plus-ash-unset-2
     (implies (and (integerp x)
                   (natp m)
                   (not (logbitp (double-rewrite m) x)))
              (equal (logbitp n (+ (ash 1 m) x))
                     (or (equal (nfix n) m) (logbitp n x)))))

   (defthm logbitp-of-plus-ash-unset-3
     (implies (and (integerp x) (integerp y)
                   (natp m)
                   (not (logbitp (double-rewrite m) (+ x y))))
              (equal (logbitp n (+ x (ash 1 m) y))
                     (or (equal (nfix n) m) (logbitp n (+ x y)))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash-unset-2
                            (x (+ x y)))))))

   (defthm logbitp-of-minus-ash-set
     (implies (and (integerp x)
                   (natp m)
                   (logbitp (double-rewrite m) x))
              (equal (logbitp n (+ x (- (ash 1 m))))
                     (and (not (equal (nfix n) m)) (logbitp n x))))
     :hints (("goal" :induct (logbitp-ash-ind n m x)
              :in-theory (enable* ihsext-recursive-redefs)
              :expand ((:free (x) (logbitp n x))
                       (:free (x) (logbitp m x))))))


   (defthm logbitp-of-minus-ash-set-2
     (implies (and (integerp x)
                   (natp m)
                   (logbitp (double-rewrite m) x))
              (equal (logbitp n (+ (- (ash 1 m)) x))
                     (and (not (equal (nfix n) m)) (logbitp n x)))))

   (defthm logbitp-of-minus-ash-set-3
     (implies (and (integerp x) (integerp y)
                   (natp m)
                   (logbitp (double-rewrite m) (+ x y)))
              (equal (logbitp n (+ x (- (ash 1 m)) y))
                     (and (not (equal (nfix n) m)) (logbitp n (+ x y)))))
     :hints (("Goal" :use ((:instance logbitp-of-minus-ash-set-2
                            (x (+ x y)))))))

   (defthm loghead-of-plus-ash-unset
     (implies (and (integerp x)
                   (natp m)
                   (not (logbitp (double-rewrite m) x)))
              (equal (loghead n (+ x (ash 1 m)))
                     (+ (if (<= (nfix n) m) 0 (ash 1 m))
                        (loghead n x))))
     :hints (("goal" :induct (logbitp-ash-ind n m x)
              :in-theory (enable* ihsext-recursive-redefs logcons))))


   (defthm loghead-of-plus-ash-unset-2
     (implies (and (integerp x)
                   (natp m)
                   (not (logbitp (double-rewrite m) x)))
              (equal (loghead n (+ (ash 1 m) x))
                     (+ (if (<= (nfix n) m) 0 (ash 1 m))
                        (loghead n x)))))

   (defthm loghead-of-plus-ash-unset-3
     (implies (and (integerp x) (integerp y)
                   (natp m)
                   (not (logbitp (double-rewrite m) (+ x y))))
              (equal (loghead n (+ x (ash 1 m) y))
                     (+ (if (<= (nfix n) m) 0 (ash 1 m))
                        (loghead n (+ x y)))))
     :hints (("Goal" :use ((:instance loghead-of-plus-ash-unset-2
                            (x (+ x y)))))))


   (local (defthm logcdr-minus-2x
            (implies (integerp x)
                     (equal (logcdr (- (* 2 x)))
                            (- x)))
            :hints(("Goal" :use ((:instance bitops::logcdr-of-logcons
                                  (x (- x)) (b 0)))
                    :in-theory (e/d (logcons) (bitops::logcdr-of-logcons))))))

   (defthm loghead-of-minus-ash-set
     (implies (and (integerp x)
                   (natp m)
                   (logbitp (double-rewrite m) x))
              (equal (loghead n (+ x (- (ash 1 m))))
                     (+ (if (<= (nfix n) m) 0 (- (ash 1 m)))
                        (loghead n x))))
     :hints (("goal" :induct (logbitp-ash-ind n m x)
              :in-theory (enable* ihsext-recursive-redefs logcons)
              :expand ((:free (x) (loghead n x))
                       (:free (x) (loghead m x))))))


   (defthm loghead-of-minus-ash-set-2
     (implies (and (integerp x)
                   (natp m)
                   (logbitp (double-rewrite m) x))
              (equal (loghead n (+ (- (ash 1 m)) x))
                     (+ (if (<= (nfix n) m) 0 (- (ash 1 m)))
                        (loghead n x)))))

   (defthm loghead-of-minus-ash-set-3
     (implies (and (integerp x) (integerp y)
                   (natp m)
                   (logbitp (double-rewrite m) (+ x y)))
              (equal (loghead n (+ x (- (ash 1 m)) y))
                     (+ (if (<= (nfix n) m) 0 (- (ash 1 m)))
                        (loghead n (+ x y)))))
     :hints (("Goal" :use ((:instance loghead-of-minus-ash-set-2
                            (x (+ x y)))))))

   ))

(local
 (defsection logbitp-of-plus-ash-same-theory

   (local (defthm logbitp-of-plus-ash-base
            (implies (and (integerp x))
                     (equal (logbitp m (+ x (ash 1 (nfix m))))
                            (not (logbitp m x))))
            :hints(("Goal" :in-theory (enable* ihsext-inductions
                                               ihsext-recursive-redefs)))))

   (defthm logbitp-of-plus-ash
     (implies (and (equal mm (nfix m))
                   (integerp x))
              (equal (logbitp m (+ x (ash 1 mm)))
                     (not (logbitp m x)))))
     

   (defthm logbitp-of-plus-ash-1
     (implies (and (equal mm (nfix m))
                   (integerp x))
              (equal (logbitp m (+ (ash 1 mm) x))
                     (not (logbitp m x))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash
                            (x x)))
              :in-theory (disable logbitp-of-plus-ash))))

   (defthm logbitp-of-plus-ash-2
     (implies (and (equal mm (nfix m))
                   (integerp x) (integerp y))
              (equal (logbitp m (+ x (ash 1 mm) y))
                     (not (logbitp m (+ x y)))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash
                            (x (+ x y))))
              :in-theory (disable logbitp-of-plus-ash))))

   (defthm logbitp-of-plus-ash-3
     (implies (and (equal mm (nfix m))
                   (integerp x) (integerp y))
              (equal (logbitp m (+ x y (ash 1 mm)))
                     (not (logbitp m (+ x y)))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash
                            (x (+ x y))))
              :in-theory (disable logbitp-of-plus-ash))))

   (defthm logbitp-of-minus-ash-base
     (implies (and (integerp x))
              (equal (logbitp m (+ x (- (ash 1 (nfix m)))))
                     (not (logbitp m x))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash-base
                            (x (+ x (- (ash 1 (nfix m)))))))
              :in-theory (disable logbitp-of-plus-ash-base))))

   (defthm logbitp-of-minus-ash
     (implies (and (equal mm (nfix m))
                   (integerp x))
              (equal (logbitp m (+ x (- (ash 1 mm))))
                     (not (logbitp m x)))))

   (defthm logbitp-of-minus-ash-1
     (implies (and (equal mm (nfix m))
                   (integerp x))
              (equal (logbitp m (+ (- (ash 1 mm)) x))
                     (not (logbitp m x))))
     :hints (("Goal" :use ((:instance logbitp-of-minus-ash
                            (x x)))
              :in-theory (disable logbitp-of-minus-ash))))

   (defthm logbitp-of-minus-ash-2
     (implies (and (equal mm (nfix m))
                   (integerp x))
              (equal (logbitp m (+ (- (ash 1 mm)) x))
                     (not (logbitp m x))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash
                            (x (+ x (- (ash 1 m))))))
              :in-theory (disable logbitp-of-plus-ash))))

   (defthm logbitp-of-minus-ash-3
     (implies (and (equal mm (nfix m))
                   (integerp x) (integerp y))
              (equal (logbitp m (+ x (- (ash 1 mm)) y))
                     (not (logbitp m (+ x y)))))
     :hints (("Goal" :use ((:instance logbitp-of-minus-ash
                            (x (+ x y)) (m mm)))
              :in-theory (disable logbitp-of-minus-ash))))

   (defthmd logbitp-when-less-than-ash
     (implies (and (natp n) (< n (ash 1 m))
                   (natp m))
              (not (logbitp m n)))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))))

(defsection complements-related-by-shift


  (local (defun loghead-of-plus-ash-ind (m n x)
           (if (zp m)
               (list x n)
             (loghead-of-plus-ash-ind (1- m) (1- (nfix n)) (logcdr x)))))

  (local (defthm logbitp-of-plus-ash-greater
           (implies (and (< (nfix m) n)
                         (natp n)
                         (integerp x))
                    (equal (logbitp m (+ x (ash 1 n)))
                           (logbitp m x)))
           :hints(("Goal" :induct (loghead-of-plus-ash-ind m n x)
                   :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthm logbitp-of-minus-ash-greater
           (implies (and (< (nfix m) n)
                         (natp n)
                         (integerp x))
                    (equal (logbitp m (+ x (- (ash 1 n))))
                           (logbitp m x)))
           :hints(("Goal" :use ((:instance logbitp-of-plus-ash-greater
                                 (x (+ x (- (ash 1 n))))))
                   :in-theory (disable logbitp-of-plus-ash-greater)))))

  (local (defthm logbitp-of-plus-lesser-when-not-logbitp
           (implies (and (< (nfix m) n)
                         (natp n)
                         (integerp x)
                         (not (logbitp (double-rewrite m) x)))
                    (equal (logbitp n (+ x (ash 1 m)))
                           (logbitp n x)))
           :hints (("goal" :induct (loghead-of-plus-ash-ind m n x)
                    :in-theory (enable* ihsext-recursive-redefs)
                    :expand ((:free (x) (logbitp n x)))))))

  (local (in-theory (enable ash-1-monotonic)))

  (local (defthm loghead-by-bounds
           (implies (and (<= (ash 1 num) b)
                         (< b (* 2 (ash 1 num)))
                         (natp num)
                         (integerp b))
                    (equal (loghead num b) (- b (ash 1 num))))
           :hints(("Goal" :in-theory (enable loghead
                                             bitops::ash-is-expt-*-x)))))



  (local (defthm logbitp-when-bounded-lemma
           (implies (and (< b (+ (ash 1 n) (- (ash 1 m))))
                         (natp b) (natp n) (natp m)
                         (not (logbitp (double-rewrite m) b)))
                    (not (logbitp n b)))
           :hints (("Goal" :induct (loghead-of-plus-ash-ind m n b)
                    :in-theory (enable* ihsext-recursive-redefs
                                        logcons
                                        logbitp-when-less-than-ash)))))

  (local (defthm logbitp-when-bounded-lemma2
           (implies (and (< (+ b (- (ash 1 n)) (ash 1 m))
                            (ash 1 num))
                         (natp b) (natp n) (natp m) (< m n)
                         (natp num) (< n num)
                         (<= (ash 1 num) b)
                         (not (logbitp (double-rewrite m) b)))
                    (not (logbitp n b)))
           :hints (("goal" :use ((:instance bitops::logbitp-of-loghead-in-bounds
                                  (pos m) (i b) (size num))
                                 (:instance bitops::logbitp-of-loghead-in-bounds
                                  (pos n) (i b) (size num))
                                 (:instance logbitp-when-bounded-lemma
                                  (b (loghead num b))))
                    :in-theory (e/d (ash-1-monotonic)
                                    (bitops::logbitp-of-loghead-in-bounds
                                     ;; logbitp-of-minus-ash-greater
                                     ))))))

  (defthmd complements-related-by-shift
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (< (nfix m) (nfix n)))
             (equal (logand (var n numvars) (lognot (var m numvars)))
                    (ash (logand (var m numvars) (lognot (var n numvars)))
                         (- (ash 1 (nfix n)) (ash 1 (nfix m))))))
    :hints ((bitops::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:cases ((< bitops::wbit0 (- (ash 1 n) (ash 1 (nfix m))))))))
    :otf-flg t)


  (local (defthm ash-of-logand
           (equal (ash (logand a b) sh)
                  (logand (ash a sh) (ash b sh)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))


  (defthm complements-related-by-shift-unshift
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (equal mm (nfix m))
                  (< (nfix m) (nfix n)))
             (equal (logand (ash (var m numvars) (+ (ash 1 n) (- (ash 1 mm))))
                            (ash (lognot (var n numvars)) (+ (ash 1 n) (- (ash 1 mm)))))
                    (logand (var n numvars) (lognot (var m numvars)))))
    :hints (("goal" :use ((:instance complements-related-by-shift))
             :in-theory (disable complements-related-by-shift)))
    :otf-flg t)

  (defthm complements-related-by-shift-unshift2
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (equal mm (nfix m))
                  (< (nfix m) (nfix n)))
             (equal (logand (ash (var m numvars) (+ (- (ash 1 mm)) (ash 1 n)))
                            (ash (lognot (var n numvars)) (+ (- (ash 1 mm)) (ash 1 n))))
                    (logand (var n numvars) (lognot (var m numvars)))))
    :hints (("goal" :use ((:instance complements-related-by-shift))
             :in-theory (disable complements-related-by-shift)))
    :otf-flg t)

  (defthm complements-related-by-shift-unshift3
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (equal mm (nfix m))
                  (< (nfix m) (nfix n)))
             (equal (logand (ash (var m numvars) (+ (ash 1 n) (- (ash 1 mm))))
                            (ash (lognot (var n numvars)) (+ (ash 1 n) (- (ash 1 mm))))
                            z)
                    (logand (var n numvars) (lognot (var m numvars))
                            z)))
    :hints (("goal" :use ((:instance complements-related-by-shift))
             :in-theory (disable complements-related-by-shift)))
    :otf-flg t)

  (defthm complements-related-by-shift-untail
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (< (nfix m) (nfix n)))
             (equal (logand (logtail (+ (ash 1 n) (- (ash 1 (nfix m)))) (var n numvars))
                            (lognot (logtail (+ (ash 1 n) (- (ash 1 (nfix m)))) (var m numvars))))
                    (logand (var m numvars) (lognot (var n numvars)))))
    :hints (("goal" :use ((:instance ash-of-logand
                           (a (var n numvars)) (b (lognot (var m numvars)))
                           (sh (- (+ (ash 1 n) (- (ash 1 (nfix m))))))))
             :in-theory (e/d (complements-related-by-shift))))
    :otf-flg t)

  (defthm complements-related-by-shift-untail3
    (implies (and (< (nfix n) numvars)
                  (natp numvars)
                  (< (nfix m) (nfix n)))
             (equal (logand (logtail (+ (ash 1 n) (- (ash 1 (nfix m)))) (var n numvars))
                            (lognot (logtail (+ (ash 1 n) (- (ash 1 (nfix m)))) (var m numvars)))
                            z)
                    (logand (var m numvars) (lognot (var n numvars)) z)))
    :hints (("goal" :use ((:instance complements-related-by-shift-untail))
             :in-theory (disable complements-related-by-shift-untail)))
    :otf-flg t))

(define index-swap ((n natp "first element to swap")
                      (m natp "second element to swap")
                      (x natp "index to apply the swap to"))
  :returns (swap natp :rule-classes :type-prescription)
  (b* ((x (lnfix x))
       (n (lnfix n))
       (m (lnfix m)))
    (cond ((eql x n) m)
          ((eql x m) n)
          (t x)))
  ///
  (defthm index-swap-commute
    (equal (index-swap m n x)
           (index-swap n m x))
    :rule-classes ((:rewrite :loop-stopper ((n m)))))

  (defthm index-swap-inverse
    (equal (index-swap n m (index-swap n m x))
           (nfix x)))

  (defthm index-swap-n
    (equal (index-swap n m n)
           (nfix m)))

  (defthm index-swap-m
    (equal (index-swap n m m)
           (nfix n)))

  (defthm index-swap-unaffected
    (implies (and (not (nat-equiv n x))
                  (not (nat-equiv m x)))
             (equal (index-swap n m x)
                    (nfix x))))

  (defthm index-swap-self
    (equal (index-swap n n x)
           (nfix x)))

  (defthm index-swap-unique
    (iff (equal (index-swap n m x) (index-swap n m y))
         (equal (nfix x) (nfix y)))))

(define env-swap-vars ((n natp "first element to swap")
                       (m natp "second element to swap")
                       (env natp "env to apply the swap to"))
  :returns (swap-env natp :rule-classes :type-prescription)
  (b* ((env (lnfix env))
       (n (lnfix n))
       (m (lnfix m)))
    (env-update n (env-lookup m env)
                (env-update m (env-lookup n env) env)))
  ///
  (local (in-theory (enable* bitops::logbitp-of-install-bit-split
                             acl2::arith-equiv-forwarding)))

  (defthm env-swap-vars-commute
    (equal (env-swap-vars m n x)
           (env-swap-vars n m x))
    :hints(("Goal" :in-theory (enable env-update env-lookup))
           (acl2::logbitp-reasoning))
    :rule-classes ((:rewrite :loop-stopper ((n m)))))

  (defret lookup-in-env-swap-vars
    (equal (env-lookup k swap-env)
           (env-lookup (index-swap n m k) env))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm env-swap-vars-inverse
    (equal (env-swap-vars n m (env-swap-vars n m env))
           (nfix env))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm env-swap-vars-self
    (equal (env-swap-vars n n env)
           (nfix env))))



(define swap-vars-aux ((n natp) (m natp) (truth integerp) (numvars natp))
  :guard (and (< n numvars) (< m n))
  :returns (swapped-truth integerp :rule-classes :type-prescription)
  (b* ((truth (loghead (ash 1 (lnfix numvars)) truth))
       (varn (var n numvars))
       (varm (var m numvars))
       (same (logeqv varn varm))
       (n&~m (logand varn (lognot varm)))
       (m&~n (logand varm (lognot varn)))
       (shift (- (ash 1 (lnfix n)) (ash 1 (lnfix m)))))
    (logior (logand same truth)
            (ash (logand n&~m truth) (- shift))
            (ash (logand m&~n truth) shift)))
  ///
  (local (defthm loghead-over-install-bit
           (implies (< (nfix n) (nfix w))
                    (equal (loghead w (install-bit n b x))
                           (install-bit n b (loghead w x))))
           :hints ((bitops::logbitp-reasoning)
                   (and stable-under-simplificationp
                        '(:in-theory (enable bitops::logbitp-of-install-bit-split
                                             bitops::logbitp-of-loghead-split))))))

  (local (defthmd logcdr-when-not-integerp
           (implies (not (integerp x))
                    (equal (logcdr x) 0))
           :hints(("Goal" :in-theory (enable logcdr)))))
  (local (defthmd logcar-when-not-integerp
           (implies (not (integerp x))
                    (equal (logcar x) 0))
           :hints(("Goal" :in-theory (enable logcar)))))

  (local (defthmd install-bit-1-when-not-set
           (implies (not (logbitp n x))
                    (equal (install-bit n 1 x)
                           (+ (Ash 1 (nfix n)) (ifix x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              install-bit**
                                              logcons
                                              logcar-when-not-integerp
                                              logcdr-when-not-integerp)))))



  (local (defthmd install-bit-0-when-set
           (implies (logbitp n x)
                    (equal (install-bit n 0 x)
                           (+ (- (Ash 1 (nfix n))) (ifix x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs
                                              install-bit**
                                              logcons
                                              logcar-when-not-integerp
                                              logcdr-when-not-integerp)))))



  (local (defthm loghead->=-ash-when-logbitp
           (implies (and (logbitp n env)
                         (natp n) (natp numvars)
                         (< n numvars))
                    (<= (ash 1 n) (loghead numvars env)))
           :hints (("goal" :use ((:instance bitops::logbitp-of-loghead-in-bounds
                                  (pos n) (i env) (size numvars)))
                    :in-theory (e/d (logbitp-when-less-than-ash)
                                    (bitops::logbitp-of-loghead-in-bounds))))
           :rule-classes :linear))


  (local (defthmd swap-bits-is-add
           (implies (and (equal b1 (bool->bit (logbitp m x)))
                         (equal b2 (bool->bit (logbitp n x))))
                    (equal (install-bit n b1 (install-bit m b2 x))
                           (if (xor (logbitp n x)
                                    (logbitp m x))
                               (if (logbitp n x)
                                   (+ (- (ash 1 (nfix n))) (ash 1 (nfix m)) (ifix x))
                                 (+ (ash 1 (nfix n)) (- (ash 1 (nfix m))) (ifix x)))
                             (ifix x))))
           :hints(("goal" :use ((:instance install-bit-0-when-set
                                 (x (install-bit m (bool->bit (logbitp n x))
                                                     x)))
                                (:instance install-bit-1-when-not-set
                                 (x (install-bit m (bool->bit (logbitp n x))
                                                     x))))
                   :in-theory (enable bitops::logbitp-of-install-bit-split))
                  (and stable-under-simplificationp
                       '(:use ((:instance install-bit-0-when-set
                                (n m))
                               (:instance install-bit-1-when-not-set
                                (n m))))))))

  (local (defthm ash-of-logand
           (equal (ash (logand a b) sh)
                  (logand (ash a sh) (ash b sh)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (in-theory (disable BITOPS::INSTALL-BIT-OF-INSTALL-BIT-DIFF
                             BITOPS::LOGTAIL-OF-LOGHEAD)))

  (local (defthmd truth-eval-with-loghead
           (equal (truth-eval truth env numvars)
                  (logbitp (loghead (nfix numvars) (nfix env))
                           (loghead (ash 1 (nfix numvars)) truth)))
           :hints (("Goal" :use truth-eval-of-truth-norm
                    :in-theory (e/d (truth-eval truth-norm)
                                    (truth-eval-of-truth-norm))))
           :rule-classes ((:definition :install-body t))))

  (defret eval-of-swap-vars-aux
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix n)))
             (equal (truth-eval swapped-truth env numvars)
                    (truth-eval truth
                                (env-swap-vars n m env)
                                numvars)))
    :hints(("Goal" :in-theory (e/d (ash-1-monotonic env-swap-vars)
                                   (truth-eval-of-logand
                                    truth-eval-of-logior
                                    truth-eval-of-lognot
                                    truth-eval-of-logxor)))
           (and stable-under-simplificationp
                '(:in-theory (enable env-update env-lookup
                                     loghead-less-than-ash
                                     ash-1-monotonic)
                  :expand ((:with truth-eval (:free (x) (truth-eval x env numvars)))
                           (:with truth-eval-with-loghead (:free (env) (truth-eval truth env numvars))))))
           (and stable-under-simplificationp
                '(:in-theory (enable swap-bits-is-add
                                     bitops::logbitp-of-loghead-split
                                     loghead-less-than-ash
                                     ash-1-monotonic)))
           (and stable-under-simplificationp
                '(:in-theory (enable loghead-less-than-ash)
                  :use ((:instance ash-1-monotonic
                         (a (nfix m)) (b n))))))
    :otf-flg t)

  (local (defret size-of-swap-vars-lemma
           (implies (and (< (nfix n) (nfix numvars))
                         (< (nfix m) (nfix n)))
                    (unsigned-byte-p (ash 1 numvars) swapped-truth))
           :hints(("Goal" :in-theory (enable ash-1-monotonic)))))

  (defret size-of-swap-vars-aux
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix n))
                  (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size swapped-truth))
    :hints (("goal" :use size-of-swap-vars-lemma
             :in-theory (disable size-of-swap-vars-lemma swap-vars-aux))))

  (defret truth-norm-of-swap-vars-aux
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix n)))
             (equal (truth-norm swapped-truth numvars)
                    swapped-truth))
    :hints(("Goal" :in-theory (e/d (truth-norm acl2::loghead-identity) (swap-vars-aux)))))

  (defthm swap-vars-aux-of-truth-norm
    (equal (swap-vars-aux n m (truth-norm truth numvars) numvars)
           (swap-vars-aux n m truth numvars))
    :hints(("Goal" :in-theory (enable truth-norm)))))

(define swap-vars ((n natp) (m natp) (truth integerp) (numvars natp))
  :guard (and (< n numvars) (< m numvars))
  :returns (swapped-truth integerp :rule-classes :type-prescription)
  (cond ((< (lnfix n) (lnfix m)) (swap-vars-aux m n truth numvars))
        ((< (lnfix m) (lnfix n)) (swap-vars-aux n m truth numvars))
        (t (truth-norm truth numvars)))
  ///
  (defret swap-vars-commute
    (equal (swap-vars m n truth numvars)
           (swap-vars n m truth numvars))
    :rule-classes ((:rewrite :loop-stopper ((n m)))))

  (defret eval-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix numvars)))
             (equal (truth-eval swapped-truth env numvars)
                    (truth-eval truth
                                (env-swap-vars n m env)
                                numvars)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret size-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix numvars))
                  (natp size)
                  (<= (ash 1 numvars) size))
             (unsigned-byte-p size swapped-truth)))

  (defret swap-vars-self
    (equal (swap-vars n n truth numvars)
           (truth-norm truth numvars)))

  (defret truth-norm-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix numvars))) 
             (equal (truth-norm swapped-truth numvars)
                    swapped-truth)))

  (defthm swap-vars-of-truth-norm
    (equal (swap-vars n m (truth-norm truth numvars) numvars)
           (swap-vars n m truth numvars))))





(local (defthm logcount-of-loghead-+-1
         (implies (natp n)
                  (equal (logcount (loghead (+ 1 n) mask))
                         (+ (logbit n mask)
                            (logcount (loghead n mask)))))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))

(local (defthm logcount-of-loghead-bound
         (<= (logcount (loghead n x)) (nfix n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))
         :rule-classes :linear))

;; Widening representations: Suppose we have a truth table wherein only the
;; first (say) 3 out of 5 variables are relevant, i.e. depends-on of variables
;; 0,1,2 is true and of 3,4 is false.  Suppose we want to change its
;; representation so that the relevant variables are now 0,2,4 instead.  (One
;; possible reason: we want to, say, AND it with another truth table whose
;; variables 0,2,4 represent the same thing as our 0,1,2 but whose 1,3
;; represent other things.) Permuting this representation under the permute
;; mask #b10101 accomplishes this.

(define index-move-up ((m natp) (n natp) (x natp))
  :guard (<= m n)
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-idx natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (lnfix x))
       (next (1+ (lnfix m)))
       (x (lnfix x))
       (x (index-swap next m x)))
    (index-move-up next n x))
  ///

  (local (in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1)))

  (defthmd index-move-up-redef
    (equal (index-move-up m n x)
           (b* ((x (nfix x))
                (m (nfix m))
                (n (nfix n)))
             (cond ((<= n m) x)
                   ((< x m) x)
                   ((eql x m) n)
                   ((<= x n) (1- x))
                   (t x))))
    :hints(("Goal" :in-theory (enable index-swap)))))

(define index-move-down ((m natp) (n natp) (x natp))
  :guard (<= m n)
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-idx natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (lnfix x))
       (next (1+ (lnfix m)))
       (x (lnfix x))
       (x (index-move-down next n x)))
    (index-swap next m x))
  ///
  (local (in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-2
                             ACL2::INEQUALITY-WITH-NFIX-HYP-1
                             acl2::nfix-equal-to-nonzero)))

  (defthmd index-move-down-redef
    (equal (index-move-down m n x)
           (b* ((x (nfix x))
                (m (nfix m))
                (n (nfix n)))
             (cond ((<= n m) x)
                   ((< x m) x)
                   ((< x n) (1+ x))
                   ((eql x n) m)
                   (t x))))
    :hints(("Goal" :in-theory (enable index-swap))))

  (defthm index-move-up-of-index-move-down
    (equal (index-move-up n m (index-move-down n m x))
           (nfix x))
    :hints(("Goal" :in-theory (enable index-move-up-redef
                                      index-move-down-redef))))

  (local (defthm posp-of-nfix-when-greater
           (implies (and (<= (nfix x) (nfix y))
                         (not (equal (nfix x) (nfix y))))
                    (posp (nfix y)))))

  (defthm index-move-down-of-index-move-up
    (equal (index-move-down n m (index-move-up n m x))
           (nfix x))
    :hints(("Goal" :in-theory (enable index-move-up-redef
                                      index-move-down-redef)
            :do-not-induct t))))

(define index-permute-stretch ((n natp)
                               (count)
                               (mask natp)
                               (x natp)
                               (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-index natp :rule-classes :type-prescription)
  ;; Fill in the value for set bits >= n. Equivalently, move bits between
  ;; (count n) and (count numvars) into position.
  ;; To do this, recursively do so for n+1, then if the nth bit is set, move up
  ;; the (count n)th value into the nth slot.

  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (x (index-permute-stretch (1+ n) (+ bit count) mask x numvars)))
    (if (eql bit 1)
        (index-move-up count n x)
      x))
  ///
  (defret index-permute-stretch-bound
    (implies (< (nfix x) (nfix numvars))
             (< perm-index (nfix numvars)))
    :hints(("Goal" :in-theory (enable index-move-up-redef)))
    :rule-classes :linear)

  (defthm index-permute-stretch-normalize-count
    (implies (syntaxp (not (equal count ''nil)))
             (equal (index-permute-stretch n count mask x numvars)
                    (index-permute-stretch n nil mask x numvars)))
    :hints (("goal" :expand ((:free (count) (index-permute-stretch n count mask x numvars)))))))


(define index-permute-shrink ((n natp)
                              (count)
                              (mask natp)
                              (x natp)
                              (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-index natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (x (if (eql bit 1)
              (index-move-down count n x)
            x)))
    (index-permute-shrink (1+ n) (+ bit count) mask x numvars))
  ///
  (defret index-permute-shrink-bound
    (implies (< (nfix x) (nfix numvars))
             (< perm-index (nfix numvars)))
    :hints(("Goal" :in-theory (enable index-move-down-redef)))
    :rule-classes :linear)

  (defthm index-permute-shrink-normalize-count
    (implies (syntaxp (not (equal count ''nil)))
             (equal (index-permute-shrink n count mask x numvars)
                    (index-permute-shrink n nil mask x numvars)))
    :hints (("goal" :expand ((:free (count) (index-permute-shrink n count mask x numvars))))))

  (defthm index-permute-shrink-of-index-permute-stretch
    (equal (index-permute-shrink n count mask (index-permute-stretch n count2 mask x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable index-permute-stretch)
            :induct (index-permute-stretch n count2 mask x numvars)
            :expand ((:free (count2) (index-permute-stretch n count2 mask x numvars))
                     (:free (count x) (index-permute-shrink n count mask x numvars))))))

  (defthm index-permute-stretch-of-index-permute-shrink
    (equal (index-permute-stretch n count mask (index-permute-shrink n count2 mask x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable index-permute-stretch)
            :induct (index-permute-shrink n count2 mask x numvars)
            :expand ((:free (count x) (index-permute-stretch n count mask x numvars))
                     (:free (count2) (index-permute-shrink n count2 mask x numvars))))))

  (defthm index-permute-stretch-one-to-one
    (implies (not (equal (nfix x) (nfix y)))
             (not (equal (index-permute-stretch n count mask x numvars)
                         (index-permute-stretch n count2 mask y numvars))))
    :hints (("goal" :use ((:instance index-permute-shrink-of-index-permute-stretch
                           (count2 count) (x x))
                          (:instance index-permute-shrink-of-index-permute-stretch
                           (count2 count2) (x y)))
             :in-theory (disable index-permute-shrink-of-index-permute-stretch
                                 index-permute-shrink))))

  (defthm index-permute-shrink-one-to-one
    (implies (not (equal (nfix x) (nfix y)))
             (not (equal (index-permute-shrink n count mask x numvars)
                         (index-permute-shrink n count2 mask y numvars))))
    :hints (("goal" :use ((:instance index-permute-stretch-of-index-permute-shrink
                           (count2 count) (x x))
                          (:instance index-permute-stretch-of-index-permute-shrink
                           (count2 count2) (x y)))
             :in-theory (disable index-permute-stretch-of-index-permute-shrink
                                 index-permute-shrink))))


  

  (defretd index-permute-shrink-redef
    (implies (<= (nfix n) (nfix numvars))
             (equal perm-index
                    (cond ((< (nfix x) (logcount (loghead n (nfix mask))))
                           (nfix x))
                          ((< (nfix x) (nfix n))
                           (+ (nfix x)
                              (- (logcount (loghead numvars (nfix mask)))
                                 (logcount (loghead n (nfix mask))))))
                          ((and (< (nfix x) (nfix numvars))
                                (logbitp x (nfix mask)))
                           (logcount (loghead x (nfix mask))))
                          (t (+ (nfix x)
                                (- (logcount (loghead x (loghead numvars (nfix mask)))))
                                (logcount (loghead numvars (nfix mask))))))))
    :hints (("goal" :induct <call> ;;(index-permute-shrink-redef-ind n mask env numvars k)
             :in-theory (enable* arith-equiv-forwarding
                                 index-move-down-redef)
             :expand ((:free (count) <call>)))))


  (local (defthm logcount-loghead-lognot
           (equal (logcount (loghead n (lognot x)))
                  (- (nfix n)
                     (logcount (loghead n x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::loghead**
                                              bitops::logcount**)))))
                                              

  (defthmd index-permute-shrink-redef-base
    (equal (index-permute-shrink 0 count mask x numvars)
           (b* ((x (nfix x))
                (numvars (nfix numvars))
                (mask (nfix mask)))
             (cond ((and (< x numvars) (logbitp x mask))
                    (logcount (loghead x mask)))
                   ((<= numvars x) x)
                   (t (+ (logcount (loghead x (lognot mask)))
                         (logcount (loghead numvars mask)))))))
    :hints(("Goal" :in-theory (enable index-permute-shrink-redef)))))



(define nth-set-bit-pos ((n natp)
                         (x integerp))
  :returns (pos (or (natp pos) (not pos))
                :rule-classes
                ((:type-prescription :typed-term pos)))
  :measure (+ (integer-length x) (nfix n))
  :hints(("Goal" :in-theory (enable integer-length**)))
  (if (zip x)
      nil
    (b* ((bit (logcar x))
         ((when (and (zp n) (eql bit 1))) 0)
         (rest (nth-set-bit-pos (- (lnfix n) bit) (logcdr x))))
      (and rest (+ 1 rest))))
  ///
  (defthm nth-set-bit-pos-of-negp
    (implies (negp x)
             (nth-set-bit-pos k x))
    :hints(("Goal" :in-theory (enable nth-set-bit-pos)))
    :rule-classes (:rewrite :type-prescription))

  (defthm nth-set-bit-pos-exists-when-logcount
    (implies (< (nfix n) (logcount x))
             (truth::nth-set-bit-pos n x))
    :hints(("Goal" :in-theory (enable bitops::logcount**)
            ;; :in-theory (enable truth::nth-set-bit-pos-when-logcount
                   ;;                    (:i truth::nth-set-bit-pos))
            :induct (truth::nth-set-bit-pos n x))))

  (defthm nth-set-bit-pos-types
    (and (iff (acl2-numberp (truth::nth-set-bit-pos n x))
              (truth::nth-set-bit-pos n x))
         (iff (rationalp (truth::nth-set-bit-pos n x))
              (truth::nth-set-bit-pos n x))
         (iff (integerp (truth::nth-set-bit-pos n x))
              (truth::nth-set-bit-pos n x))
         (iff (natp (truth::nth-set-bit-pos n x))
              (truth::nth-set-bit-pos n x))))

  ;; (defthmd nth-set-bit-pos-when-logcount
  ;;   (implies (and (< (nfix n) (logcount x))
  ;;                 (natp x))
  ;;            (equal (nth-set-bit-pos n x)
  ;;                   (if (and (zp n) (eql (logcar x) 1))
  ;;                       0
  ;;                     (+ 1 (nth-set-bit-pos (- (lnfix n) (logcar x))
  ;;                                           (logcdr x))))))
  ;;   :hints(("Goal" :in-theory (enable logcount**)
  ;;           :induct (nth-set-bit-pos n x)))
  ;;   :rule-classes
  ;;   ((:definition :controller-alist ((nth-set-bit-pos t t)))))

  

  (defthm logcount-of-nth-set-bit-pos
    (implies (nth-set-bit-pos k x)
             (equal (logcount (loghead (nth-set-bit-pos k x) x))
                    (nfix k)))
    :hints(("Goal" :induct (nth-set-bit-pos k x)
            :expand ((:with nth-set-bit-pos (nth-set-bit-pos k x)))
            :in-theory (e/d* ((:i nth-set-bit-pos)
                              bitops::loghead**
                              bitops::logcount**
                              acl2::arith-equiv-forwarding)))))


  (local (defthm logcount-of-loghead-lte-full-logcount
           (implies (natp x)
                    (<= (logcount (loghead n x)) (logcount x)))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::logcount**
                                               bitops::loghead**)))
           :rule-classes :linear))

  (defthm logbitp-of-nth-set-bit-pos
    (implies (nth-set-bit-pos n x)
             (logbitp (nth-set-bit-pos n x) x))
    :hints(("Goal" :in-theory (enable (:i nth-set-bit-pos)
                                      bitops::logbitp**)
            :expand ((:with nth-set-bit-pos (nth-set-bit-pos n x))))))

  (defthm logbitp-of-nth-set-bit-pos-lognot
    (implies (nth-set-bit-pos n (lognot x))
             (not (logbitp (nth-set-bit-pos n (lognot x)) x)))
    :hints(("Goal" :use ((:instance logbitp-of-nth-set-bit-pos
                           (x (lognot x))))
            :in-theory (disable logbitp-of-nth-set-bit-pos))))


  (local (defun nth-set-bit-pos-bound-by-logcount-ind (k n x)
           (if (zp n)
               (list k x)
             (nth-set-bit-pos-bound-by-logcount-ind
              (- (nfix k) (logcar x)) (1- n) (logcdr x)))))
  
  (local (defthm nth-set-bit-pos-bound-by-logcount
           (implies (and (< (nfix k) (logcount (loghead (double-rewrite n) x)))
                         (natp n))
                    (< (nth-set-bit-pos k x) n))
           :hints (("goal" :induct (nth-set-bit-pos-bound-by-logcount-ind k n x)
                    :in-theory (enable loghead** logcount**)
                    :expand ((nth-set-bit-pos k x))))))
                         
  (fty::deffixequiv nth-set-bit-pos)

  
  (local (defthm logcount-loghead-of-lognot
           (equal (logcount (loghead n (lognot x)))
                  (- (nfix n) (logcount (loghead n x))))
           :hints(("Goal" :induct (loghead n x)
                   :in-theory (enable* bitops::ihsext-inductions)
                   :expand ((loghead n (lognot x))
                            (loghead n x)
                            (:free (a b) (logcount (logcons a b))))))))

  (local (defun index-permute-stretch-alt (x mask numvars)
           (b* ((x (nfix x))
                (mask (nfix mask))
                (numvars (nfix numvars)))
             (cond ((< x (logcount (loghead numvars mask)))
                    (nth-set-bit-pos x mask))
                   ((< x numvars)
                    (nth-set-bit-pos (- x (logcount (loghead numvars mask)))
                                     (lognot mask)))
                   (t x)))))
  (local (defthm natp-of-index-permute-stretch-alt
           (natp (index-permute-stretch-alt x mask numvars))
           :rule-classes :type-prescription))

  (local (defthm index-permute-shrink-of-stretch-alt-def
           (b* ((stretch (index-permute-stretch-alt x mask numvars)))
             (equal (index-permute-shrink 0 count mask stretch numvars)
                    (nfix x)))
           :hints(("Goal" :in-theory (e/d (index-permute-shrink-redef-base)
                                          (logcount-of-nth-set-bit-pos))
                   :do-not-induct t)
                  (acl2::use-termhint
                   (b* ((x (nfix x))
                        (mask (nfix mask))
                        (numvars (nfix numvars))
                        ((when (< x (logcount (loghead numvars mask))))
                         `'(:use ((:instance logcount-of-nth-set-bit-pos
                                   (x ,(hq mask))
                                   (k ,(hq x))))))
                        ((when (< x numvars))
                         `'(:use ((:instance logcount-of-nth-set-bit-pos
                                   (x ,(hq (lognot mask)))
                                   (k ,(hq (- x (logcount (loghead numvars mask))))))))))
                     nil)))
           :otf-flg t
           :rule-classes nil))

  (local (defthm index-permute-stretch-alt-def1
           (equal (index-permute-stretch 0 count mask x numvars)
                  (index-permute-stretch-alt x mask numvars))
    :hints (("goal" :in-theory (disable index-permute-stretch-of-index-permute-shrink
                                        index-permute-stretch-alt
                                        index-permute-shrink-redef-base))
            (acl2::use-termhint
             (b* ((?spec (index-permute-stretch 0 count mask x numvars))
                  (impl (index-permute-stretch-alt x mask numvars))
                  (shrink-impl (index-permute-shrink 0 count mask impl numvars))
                  ((unless (equal shrink-impl (nfix x)))
                   `'(:use ((:instance index-permute-shrink-of-stretch-alt-def))))
                  (stretch-shrink (index-permute-stretch
                                   0 count mask shrink-impl numvars))
                  ((unless (equal stretch-shrink impl))
                   `'(:use ((:instance index-permute-stretch-of-index-permute-shrink
                             (n 0)
                             (x ,(hq impl)))))))
               nil)))))

  (defthmd index-permute-stretch-redef
    (equal (index-permute-stretch 0 count mask x numvars)
           (b* ((x (nfix x))
                (mask (nfix mask))
                (numvars (nfix numvars)))
             (cond ((< x (logcount (loghead numvars mask)))
                    (nth-set-bit-pos x mask))
                   ((< x numvars)
                    (nth-set-bit-pos (- x (logcount (loghead numvars mask)))
                                     (lognot mask)))
                   (t x))))
    :hints(("Goal" :in-theory (enable index-permute-stretch-alt)))))




(define env-move-var-up ((m natp) (n natp) (env natp))
  :guard (<= m n)
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-env natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (lnfix env))
       (next (1+ (lnfix m)))
       (env (env-update next (env-lookup m env)
                        (env-update m (env-lookup next env) env))))
    (env-move-var-up next n env))
  ///
  (defret lookup-in-env-move-var-up
    (equal (env-lookup k perm-env)
           (env-lookup (index-move-down m n k) env))
    :hints(("Goal" :in-theory (enable index-move-down)))))


(define env-move-var-down ((m natp) (n natp) (env natp))
  :guard (<= m n)
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-env natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (lnfix env))
       (next (1+ (lnfix m)))
       (env (env-move-var-down next n env)))
    (env-update next (env-lookup m env)
                (env-update m (env-lookup next env) env)))
  ///
  (defret lookup-in-env-move-var-down
    (equal (env-lookup k perm-env)
           (env-lookup (index-move-up m n k) env))
    :hints(("Goal" :in-theory (enable index-move-up index-swap))))
                       


  (defthm env-move-var-down-of-env-move-var-up
    (implies (<= (nfix m) (nfix n))
             (equal (env-move-var-down m n (env-move-var-up m n env))
                    (nfix env)))
    :hints (("goal" :induct (env-move-var-up m n env)
             :in-theory (enable (:i env-move-var-up))
             :expand ((env-move-var-up m n env)
                      (:free (env) (env-move-var-up m n env))))))

  (defthm env-move-var-up-of-env-move-var-down
    (implies (<= (nfix m) (nfix n))
             (equal (env-move-var-up m n (env-move-var-down m n env))
                    (nfix env)))
    :hints (("goal" :induct (env-move-var-down m n env)
             :expand ((env-move-var-down m n env)
                      (:free (env) (env-move-var-up m n env)))))))



(define permute-var-up ((m natp) (n natp) (truth integerp) (numvars natp))
  :guard (and (<= m n)
              (< n numvars))
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-truth natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (truth-norm truth numvars))
       (next (1+ (lnfix m)))
       (truth (swap-vars next m truth numvars)))
    (permute-var-up next n truth numvars))
  ///
  (defret eval-of-permute-var-up-with-env-move-var-up
    (implies (and (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval perm-truth
                                (env-move-var-up m n env)
                                numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-move-var-up env-swap-vars))))

  (defret eval-of-permute-var-up
    (implies (and (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval perm-truth env numvars)
                    (truth-eval truth (env-move-var-down m n env) numvars)))
    :hints(("Goal" :in-theory (e/d ()
                                   (permute-var-up
                                    eval-of-permute-var-up-with-env-move-var-up))
            :use ((:instance eval-of-permute-var-up-with-env-move-var-up
                   (env (env-move-var-down m n env)))))))

  (defret size-of-permute-var-up
    (implies (and (< (nfix n) (nfix numvars))
                  (natp size)
                  (<= (ash 1 numvars) size))
             (unsigned-byte-p size perm-truth))
    :hints(("Goal" :in-theory (enable truth-norm))))

  (defthm permute-var-up-of-truth-norm
    (equal (permute-var-up m n (truth-norm truth numvars) numvars)
           (permute-var-up m n truth numvars))))



(define permute-var-down ((m natp) (n natp) (truth integerp) (numvars natp))
  :guard (and (<= m n) (< n numvars))
  :measure (nfix (- (nfix n) (nfix m)))
  :returns (perm-truth natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
        (truth-norm truth numvars))
       (next (1+ (lnfix m)))
       (truth (permute-var-down next n truth numvars)))
    (swap-vars next m truth numvars))
  ///
  (defret eval-of-permute-var-down-with-env-move-var-down
    (implies (and (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval perm-truth
                                (env-move-var-down m n env)
                                numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-move-var-down env-swap-vars))))

  (defret eval-of-permute-var-down
    (implies (and (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval perm-truth env numvars)
                    (truth-eval truth (env-move-var-up m n env) numvars)))
    :hints(("Goal" :in-theory (e/d ()
                                   (permute-var-down
                                    eval-of-permute-var-down-with-env-move-var-down))
            :use ((:instance eval-of-permute-var-down-with-env-move-var-down
                   (env (env-move-var-up m n env)))))))

  (defret size-of-permute-var-down
    (implies (and (< (nfix n) (nfix numvars))
                  (natp size)
                  (<= (ash 1 numvars) size))
             (unsigned-byte-p size perm-truth))
    :hints(("Goal" :in-theory (enable truth-norm))))

  (defthm permute-var-down-of-truth-norm
    (equal (permute-var-down m n (truth-norm truth numvars) numvars)
           (permute-var-down m n truth numvars))))


(define env-diff-index ((env1 natp) (env2 natp))
  :returns (idx natp :rule-classes :type-prescription)
  :prepwork 
  ((defchoose env-diff-index1 (idx) (env1 env2)
     (not (equal (env-lookup idx env1)
                 (env-lookup idx env2)))))

  (b* ((idx (nfix (env-diff-index1 (lnfix env1) (lnfix env2)))))
    (if (equal (env-lookup idx env1)
               (env-lookup idx env2))
        0
      idx))
  ///

  (local (include-book "centaur/bitops/logbitp-mismatch" :dir :system))

  (defthm env-diff-index-correct
    (implies (not (equal (nfix env1) (nfix env2)))
             (b* ((idx (env-diff-index env1 env2)))
               (equal (env-lookup idx env1)
                      (not (env-lookup idx env2)))))
    :hints(("Goal" :in-theory (enable env-lookup)
            :use ((:instance env-diff-index1
                   (idx (acl2::logbitp-mismatch (nfix env1) (nfix env2)))
                   (env1 (nfix env1))
                   (env2 (nfix env2))))))))


(define env-permute-stretch ((n natp)
                             (count)
                             (mask natp)
                             (env natp)
                             (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-env natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix env))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (env (env-permute-stretch (1+ n) (+ bit count) mask env numvars)))
    (if (eql bit 1)
        (env-move-var-up count n env)
      env))
  ///

  (defret normalize-count-of-env-permute-stretch
    (implies (syntaxp (not (equal count ''nil)))
             (equal <call>
                    (let ((count nil)) <call>))))


  (defret lookup-in-env-permute-stretch
    (equal (env-lookup k perm-env)
           (env-lookup (index-permute-shrink n nil mask k numvars) env))
    :hints(("Goal" :in-theory (enable index-permute-shrink))))

  (local (defthm equals-of-index-permute-shrink
           (iff (equal (index-permute-shrink n count mask x numvars) y)
                (and (natp y)
                     (equal (nfix x) (index-permute-stretch n nil mask y numvars))))
           :hints (("goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                            (index-permute-shrink-of-index-permute-stretch))
                    :use ((:instance index-permute-shrink-of-index-permute-stretch
                           (x y)))))
           :otf-flg t))

  (defret env-permute-stretch-of-env-update
    (equal (env-permute-stretch n count mask (env-update k val env) numvars)
           (env-update (index-permute-stretch n nil mask k numvars)
                       val 
                       (env-permute-stretch n count mask env numvars)))
    :hints (("goal" :use ((:instance env-diff-index-correct
                           (env1 (env-permute-stretch n count mask (env-update k val env) numvars))
                           (env2 (env-update (index-permute-stretch n nil mask k numvars)
                                             val 
                                             (env-permute-stretch n count mask env numvars)))))
             :in-theory (disable env-diff-index-correct
                                 env-permute-stretch)))))








(define env-permute-shrink ((n natp)
                            (count)
                            (mask natp)
                            (env natp)
                            (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-env natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix env))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (env (if (eql bit 1)
                (env-move-var-down count n env)
              env)))
    (env-permute-shrink (1+ n) (+ bit count) mask env numvars))
  ///

  (defret normalize-count-of-env-permute-shrink
    (implies (syntaxp (not (equal count ''nil)))
             (equal <call>
                    (let ((count nil)) <call>))))



  (defthm env-permute-shrink-of-env-permute-stretch
    (equal (env-permute-shrink n count1 mask (env-permute-stretch n count mask env numvars) numvars)
           (nfix env))
    :hints(("Goal" :in-theory (enable (:i env-permute-stretch))
            :induct (env-permute-stretch n count mask env numvars)
            :expand ((:free (count) (env-permute-stretch n count mask env numvars))
                     (:free (count env) (env-permute-shrink n count mask env numvars))))))

  (defthm env-permute-stretch-of-env-permute-shrink
    (equal (env-permute-stretch n count1 mask (env-permute-shrink n count mask env numvars) numvars)
           (nfix env))
    :hints(("Goal"
            :induct (env-permute-shrink n count mask env numvars)
            :expand ((:free (count env) (env-permute-stretch n count mask env numvars))
                     (:free (count) (env-permute-shrink n count mask env numvars))))))


  (defret lookup-in-env-permute-shrink
    (equal (env-lookup k perm-env)
           (env-lookup (index-permute-stretch n nil mask k numvars) env))
    :hints(("Goal" :in-theory (enable index-permute-stretch))))


  (local (defthm equals-of-index-permute-shrink
           (iff (equal (index-permute-shrink n count mask x numvars) y)
                (and (natp y)
                     (equal (nfix x) (index-permute-stretch n nil mask y numvars))))
           :hints (("goal" :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                            (index-permute-shrink-of-index-permute-stretch))
                    :use ((:instance index-permute-shrink-of-index-permute-stretch
                           (x y)))))
           :otf-flg t))

  (defret env-permute-shrink-of-env-update
    (equal (env-permute-shrink n count mask (env-update k val env) numvars)
           (env-update (index-permute-shrink n nil mask k numvars)
                       val 
                       (env-permute-shrink n count mask env numvars)))
    :hints (("goal" :use ((:instance env-diff-index-correct
                           (env1 (env-permute-shrink n count mask (env-update k val env) numvars))
                           (env2 (env-update (index-permute-shrink n nil mask k numvars)
                                             val 
                                             (env-permute-shrink  n count mask env numvars)))))
             :in-theory (disable env-diff-index-correct
                                 env-permute-shrink)))))













(define permute-stretch ((n natp)
                             (count)
                             (mask natp)
                             (truth integerp)
                             (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-truth natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (truth-norm truth numvars))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (truth (permute-stretch (1+ n) (+ bit count) mask truth numvars)))
    (if (eql bit 1)
        (permute-var-up count n truth numvars)
      truth))

  ///
  (defret normalize-count-of-permute-stretch
    (implies (syntaxp (not (equal count ''nil)))
             (equal <call>
                    (let ((count nil)) <call>))))

  (defret eval-of-permute-stretch-with-env-permute-stretch
    (implies (<= (nfix n) (nfix numvars))
             (equal (truth-eval perm-truth
                                (env-permute-stretch n count mask env numvars)
                                numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-permute-stretch)
            :induct <call>
            :expand ((:free (count) <call>)
                     (:free (count) (env-permute-stretch n count mask env numvars))))))

  (defret eval-of-permute-stretch
    (implies (<= (nfix n) (nfix numvars))
             (equal (truth-eval perm-truth env numvars)
                    (truth-eval truth
                                (env-permute-shrink n count mask env numvars) numvars)))
    :hints(("Goal" :use ((:instance eval-of-permute-stretch-with-env-permute-stretch
                          (env (env-permute-shrink n count mask env numvars))))
            :in-theory (disable eval-of-permute-stretch-with-env-permute-stretch))))

  (defret size-of-permute-stretch
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size perm-truth))
    :hints(("Goal" :in-theory (enable truth-norm))))

  (defthm depends-on-of-permute-stretch
    (implies (and (natp numvars)
                  (< (nfix n) numvars)
                  (not (depends-on (index-permute-shrink 0 nil mask n numvars) truth numvars)))
             (not (depends-on n (permute-stretch 0 count mask truth numvars) numvars)))
    :hints ((acl2::use-termhint
             (b* ((perm (permute-stretch 0 count mask truth numvars))
                  (env (depends-on-witness n perm numvars))
                  (env1 (env-update n t env))
                  (?shr-env (env-permute-shrink 0 nil mask env numvars))
                  (?shr-env1 (env-permute-shrink 0 nil mask env1 numvars)))
               `'(:use ((:instance depends-on-witness-correct
                         (truth ,(hq perm))))
                  :in-theory (disable depends-on-witness-correct))))))

  (defthm permute-stretch-of-truth-norm
    (equal (permute-stretch n count mask (truth-norm truth numvars) numvars)
           (permute-stretch n count mask truth numvars))))
                  



(define permute-shrink ((n natp)
                            (count)
                            (mask natp)
                            (truth integerp)
                            (numvars natp))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :guard (and (<= n numvars)
              (eql count (logcount (loghead n mask))))
  :returns (perm-truth natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (truth-norm truth numvars))
       (n (lnfix n))
       (count (mbe :logic (logcount (loghead n (lnfix mask)))
                   :exec count))
       (bit (logbit n (lnfix mask)))
       (truth (if (eql bit 1)
                (permute-var-down count n truth numvars)
              truth)))
    (permute-shrink (1+ n) (+ bit count) mask truth numvars))
  ///

  (defret normalize-count-of-permute-shrink
    (implies (syntaxp (not (equal count ''nil)))
             (equal <call>
                    (let ((count nil)) <call>))))

  (local (defun eval-of-permute-shrink-ind (n mask env truth numvars)
           (declare (xargs :measure (nfix (- (nfix numvars) (nfix n)))))
           (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                            :exec (eql n numvars)))
                 (list truth numvars env))
                (n (lnfix n))
                (count (logcount (loghead n (lnfix mask))))
                (bit (logbit n (lnfix mask)))
                (truth (if (eql bit 1)
                           (permute-var-down count n truth numvars)
                         truth))
                (env (if (eql bit 1)
                         (env-move-var-down count n env)
                       env)))
             (eval-of-permute-shrink-ind (1+ n) mask env truth numvars))))

  (defret eval-of-permute-shrink-with-env-permute-shrink
    (implies (<= (nfix n) (nfix numvars))
             (equal (truth-eval perm-truth
                                (env-permute-shrink n count mask env numvars)
                                numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-permute-shrink)
            :induct (eval-of-permute-shrink-ind n mask env truth numvars)
            :expand ((:free (count) <call>)
                     (:free (count) (env-permute-shrink n count mask env numvars))))))

  (defret eval-of-permute-shrink
    (implies (<= (nfix n) (nfix numvars))
             (equal (truth-eval perm-truth env numvars)
                    (truth-eval truth
                                (env-permute-stretch n count mask env numvars) numvars)))
    :hints(("Goal" :use ((:instance eval-of-permute-shrink-with-env-permute-shrink
                          (env (env-permute-stretch n count mask env numvars))))
            :in-theory (disable eval-of-permute-shrink-with-env-permute-shrink))))

  (defret size-of-permute-shrink
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size perm-truth))
    :hints(("Goal" :in-theory (enable truth-norm))))

  (defthm depends-on-of-permute-shrink
    (implies (and (natp numvars)
                  (< (nfix n) numvars)
                  (not (depends-on (index-permute-stretch 0 nil mask n numvars) truth numvars)))
             (not (depends-on n (permute-shrink 0 count mask truth numvars) numvars)))
    :hints ((acl2::use-termhint
             (b* ((perm (permute-shrink 0 count mask truth numvars))
                  (env (depends-on-witness n perm numvars))
                  (env1 (env-update n t env))
                  (?shr-env (env-permute-stretch 0 nil mask env numvars))
                  (?shr-env1 (env-permute-stretch 0 nil mask env1 numvars)))
               `'(:use ((:instance depends-on-witness-correct
                         (truth ,(hq perm))))
                  :in-theory (disable depends-on-witness-correct))))))

  (defthm permute-shrink-of-truth-norm
    (equal (permute-shrink n count mask (truth-norm truth numvars) numvars)
           (permute-shrink n count mask truth numvars))))


(define index-listp (x (numvars natp))
  (if (atom x)
      (eq x nil)
    (and (natp (car x))
         (< (car x) (lnfix numvars))
         (index-listp (cdr x) numvars)))
  ///
  (defthmd natp-nth-of-index-listp
    (implies (and (index-listp x numvars)
                  (< (nfix n) (len x)))
             (natp (nth n x))))

  (defthmd nfix-nth-in-index-list-bound
    (implies (and (index-listp x numvars)
                  (posp numvars))
             (< (nfix (nth n x)) numvars))
    :rule-classes (:rewrite :linear))

  (defthmd nth-in-index-list-bound
    (implies (and (index-listp x numvars)
                  (natp numvars)
                  (natp (nth n x)))
             (< (nth n x) numvars))
    :rule-classes (:rewrite :linear))

  (defthmd nat-listp-when-index-listp
    (implies (index-listp x numvars)
             (nat-listp x)))

  (defthm true-listp-when-index-listp
    (implies (index-listp x numvars)
             (true-listp x))
    :rule-classes :forward-chaining))


(local (in-theory (enable nfix-nth-in-index-list-bound
                          nth-in-index-list-bound
                          nat-listp-when-index-listp
                          natp-nth-of-index-listp)))

(define index-perm ((n natp "current position in the list")
                    (perm nat-listp "indices to permute")
                    (x natp "index to permute")
                    (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-idx natp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (x (index-swap n (nth n perm) x)))
    (index-perm (1+ (lnfix n)) perm x numvars))
  ///
  (defret bound-of-index-perm
    (implies (and (< (nfix x) (nfix numvars))
                  (index-listp perm numvars))
             (< perm-idx (nfix numvars)))
    :hints(("Goal" :in-theory (enable* index-swap acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defthm index-perm-unique
    (iff (equal (index-perm n perm x numvars)
                (index-perm n perm y numvars))
         (equal (nfix x) (nfix y)))))

(define index-perm-rev ((n natp "current position in the list")
                        (perm nat-listp "indices to permute")
                        (x natp "index to permute")
                        (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-idx natp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (x (index-perm-rev (1+ (lnfix n)) perm x numvars)))
    (index-swap n (nth n perm) x))
  ///
  (defthm index-perm-of-index-perm-rev
    (equal (index-perm n perm (index-perm-rev n perm x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable index-perm))))

  (defthm index-perm-rev-of-index-perm
    (equal (index-perm-rev n perm (index-perm n perm x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable index-perm))))

  (defret bound-of-index-perm-rev
    (implies (and (< (nfix x) (nfix numvars))
                  (index-listp perm numvars))
             (< perm-idx (nfix numvars)))
    :hints(("Goal" :in-theory (enable* index-swap acl2::arith-equiv-forwarding)))
    :rule-classes :linear)

  (defthm index-perm-rev-unique
    (iff (equal (index-perm-rev n perm x numvars)
                (index-perm-rev n perm y numvars))
         (equal (nfix x) (nfix y)))))



(define env-perm ((n natp "current position in the list")
                  (perm nat-listp "indices to permute")
                  (x natp "env to permute")
                  (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-env natp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (x (env-swap-vars n (nth n perm) x)))
    (env-perm (1+ (lnfix n)) perm x numvars))
  ///
  (defthm lookup-index-perm-in-env-perm
    (equal (env-lookup (index-perm n perm k numvars) (env-perm n perm env numvars))
           (env-lookup k env))
    :hints(("Goal" :in-theory (enable index-perm))))

  (defthm lookup-in-env-perm
    (equal (env-lookup k (env-perm n perm env numvars))
           (env-lookup (index-perm-rev n perm k numvars) env))
    :hints(("Goal" :in-theory (enable index-perm-rev)))))

(define env-perm-rev ((n natp "current position in the list")
                      (perm nat-listp "indices to permute")
                      (x natp "env to permute")
                      (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-env natp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix x))
       (x (env-perm-rev (1+ (lnfix n)) perm x numvars)))
    (env-swap-vars n (nth n perm) x))
  ///
  (defthm lookup-index-perm-rev-in-env-perm-rev
    (equal (env-lookup (index-perm-rev n perm k numvars) (env-perm-rev n perm env numvars))
           (env-lookup k env))
    :hints(("Goal" :in-theory (enable index-perm-rev))))

  (defthm lookup-in-env-perm-rev
    (equal (env-lookup k (env-perm-rev n perm env numvars))
           (env-lookup (index-perm n perm k numvars) env))
    :hints(("Goal" :in-theory (enable index-perm))))

  (defthm env-perm-of-env-perm-rev
    (equal (env-perm n perm (env-perm-rev n perm x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable env-perm))))

  (defthm env-perm-rev-of-env-perm
    (equal (env-perm-rev n perm (env-perm n perm x numvars) numvars)
           (nfix x))
    :hints(("Goal" :in-theory (enable env-perm)))))





(define truth-perm ((n natp "current position in the list")
                    (perm (index-listp perm numvars) "indices to permute")
                    (truth integerp "truth table to permute")
                    (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-truth integerp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (truth-norm truth numvars))
       (truth (swap-vars n (nth n perm) truth numvars)))
    (truth-perm (1+ (lnfix n)) perm truth numvars))
  ///
  (defthm eval-of-truth-perm-with-env-perm
    (implies (index-listp perm numvars)
             (equal (truth-eval (truth-perm n perm truth numvars) (env-perm n perm env numvars) numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-perm))))

  (defthm eval-of-truth-perm
    (implies (index-listp perm numvars)
             (equal (truth-eval (truth-perm n perm truth numvars) env numvars)
                    (truth-eval truth (env-perm-rev n perm env numvars) numvars)))
    :hints(("Goal" :in-theory (enable env-perm-rev))))

  (defret size-of-truth-perm-basic
    (unsigned-byte-p (ash 1 (nfix numvars)) perm-truth))

  (defret size-of-truth-perm
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size perm-truth))
    :hints (("goal" :use size-of-truth-perm-basic
             :in-theory (disable size-of-truth-perm-basic)
             :do-not-induct t))))

(define truth-perm-rev ((n natp "current position in the list")
                        (perm (index-listp perm numvars) "indices to permute")
                        (truth integerp "truth table to permute")
                        (numvars natp))
  :guard (and (<= n numvars)
              (eql (len perm) numvars))
  :returns (perm-truth integerp :rule-classes :type-prescription)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (truth-norm truth numvars))
       (truth (truth-perm-rev (1+ (lnfix n)) perm truth numvars)))
    (swap-vars n (nth n perm) truth numvars))
  ///
  (defthm eval-of-truth-perm-rev-with-env-perm-rev
    (implies (index-listp perm numvars)
             (equal (truth-eval (truth-perm-rev n perm truth numvars) (env-perm-rev n perm env numvars) numvars)
                    (truth-eval truth env numvars)))
    :hints(("Goal" :in-theory (enable env-perm-rev))))

  (defthm eval-of-truth-perm-rev
    (implies (index-listp perm numvars)
             (equal (truth-eval (truth-perm-rev n perm truth numvars) env numvars)
                    (truth-eval truth (env-perm n perm env numvars) numvars)))
    :hints(("Goal" :in-theory (enable env-perm))))

  (defret size-of-truth-perm-rev-basic
    (implies (index-listp perm numvars)
             (unsigned-byte-p (ash 1 (nfix numvars)) perm-truth)))

  (defret size-of-truth-perm-rev
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size)
                  (index-listp perm numvars))
             (unsigned-byte-p size perm-truth))
    :hints (("goal" :use size-of-truth-perm-rev-basic
             :in-theory (disable size-of-truth-perm-rev-basic)
             :do-not-induct t))))



(define env-swap-polarity ((n natp)
                           (env natp))
  :returns (new-env natp :rule-classes :type-prescription)
  (env-update n (not (env-lookup n env)) env)
  ///
  (defret lookup-in-env-swap-polarity-same
    (equal (env-lookup n new-env)
           (not (env-lookup n env))))

  (defret lookup-in-env-swap-polarity-diff
    (implies (not (nat-equiv n m))
             (equal (env-lookup m new-env)
                    (env-lookup m env))))

  (defret lookup-in-env-swap-polarity-split
    (equal (env-lookup m new-env)
           (if (nat-equiv n m)
               (not (env-lookup n env))
             (env-lookup m env))))

  (defret env-swap-polarity-reverse
    (equal (env-swap-polarity n new-env)
           (nfix env)))

  (local (in-theory (enable* bitops::logbitp-of-install-bit-split
                             acl2::arith-equiv-forwarding)))

  (defret env-swap-polarity-commute
    (equal (env-swap-polarity n (env-swap-polarity m env))
           (env-swap-polarity m (env-swap-polarity n env)))
    :hints(("Goal" :in-theory (enable env-update env-lookup)
            :cases ((equal (nfix n) (nfix m))))
           (acl2::logbitp-reasoning))
    :rule-classes ((:rewrite :loop-stopper ((n m))))))

(define swap-polarity ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  :returns (new-truth integerp :rule-classes :type-prescription)
  (b* ((truth (truth-norm truth numvars))
       (var (var n numvars))
       (shift (ash 1 (lnfix n))))
    (logior (ash (logand var truth) (- shift))
            (ash (logand (lognot var) (loghead (ash 1 (lnfix numvars)) truth))
                 shift)))
  ///
  
  (local (defthm minus-ash-1-is-install-bit-rev
           (implies (and (logbitp (double-rewrite n) x) (integerp x) (natp n))
                    (equal (+ (- (ash 1 n)) x)
                           (install-bit n 0 x)))
           :hints(("Goal" :in-theory (enable minus-ash-1-is-install-bit)))))

  (local (defthm plus-ash-1-is-install-bit-rev
           (implies (and (not (logbitp (double-rewrite n) x)) (integerp x) (natp n))
                    (equal (+ (ash 1 n) x)
                           (install-bit n 1 x)))
           :hints(("Goal" :in-theory (enable plus-ash-1-is-install-bit)))))

  (local (in-theory (enable loghead-less-than-ash)))

  (local (defthm lower-bound-by-logbitp
           (implies (and (logbitp n x)
                         (natp x))
                    (<= (ash 1 (nfix n)) x))
           :hints (("goal" :induct (logbitp n x)
                    :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)))))

  (local (defthm install-bit-bound
           (implies (and (< x (ash 1 size))
                         (natp x)
                         (natp size)
                         (< (nfix n) size))
                    (< (install-bit n v x) (ash 1 size)))
           :hints (("goal" :use ((:instance bitops::unsigned-byte-p-of-install-bit
                                  (n size) (i n) (v v) (x x)))
                    :in-theory (e/d (unsigned-byte-p bitops::expt-2-is-ash)
                                    (bitops::unsigned-byte-p-of-install-bit))))))

  (defret swap-polarity-correct
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-eval new-truth env numvars)
                    (truth-eval truth (env-swap-polarity n env) numvars)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable env-lookup env-swap-polarity env-update truth-eval
                                     bitops::logbitp-of-ash-split
                                     truth-norm)))))

  (defthmd size-of-logand-by-size-of-loghead-2
    (implies (and (unsigned-byte-p m a)
                  (unsigned-byte-p n (loghead m b)))
             (unsigned-byte-p n (logand b a)))
    :hints(("Goal" :in-theory (enable size-of-logand-by-size-of-loghead))))

  (defthmd size-of-logand-with-loghead
    (implies (unsigned-byte-p n (loghead m b))
             (unsigned-byte-p n (logand b (loghead m a))))
    :hints (("goal" :use ((:instance size-of-logand-by-size-of-loghead-2
                           (a (loghead m a)) (m (nfix m)))))))

  (defret swap-polarity-size-basic
    (implies (< (nfix n) (nfix numvars))
             (unsigned-byte-p (ash 1 numvars) new-truth))
    :hints(("Goal" :in-theory (enable size-of-logand-with-loghead
                                      ash-1-monotonic
                                      truth-norm)
            :do-not-induct t)))

  (defret swap-polarity-size
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size)
                  (< (nfix n) (nfix numvars)))
             (unsigned-byte-p size new-truth))
    :hints (("goal" :use swap-polarity-size-basic
             :in-theory (disable swap-polarity-size-basic))))

  (defthm swap-polarity-of-truth-norm
    (equal (swap-polarity n (truth-norm truth numvars) numvars)
           (swap-polarity n truth numvars))
    :hints(("Goal" :in-theory (enable truth-norm)))))

(define env-permute-polarity ((n natp)
                              (mask integerp)
                              (env natp)
                              (numvars natp))
  :guard (<= n numvars)
  :measure (nfix (- (nfix numvars) (nfix n)))
  :returns (new-env natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (lnfix env))
       (env (if (logbitp n mask)
                (env-swap-polarity n env)
              env)))
    (env-permute-polarity (1+ (lnfix n)) mask env numvars))
  ///
  (local (in-theory (enable* acl2::arith-equiv-forwarding)))

  (defret lookup-in-env-permute-polarity-split
    (equal (env-lookup m new-env)
           (if (and (<= (nfix n) (nfix m))
                    (< (nfix m) (nfix numvars)))
               (xor (env-lookup m env) (logbitp m mask))
             (env-lookup m env))))


  (defret lookup-in-env-permute-polarity-set
    (implies (and (logbitp m mask)
                  (< (nfix m) (nfix numvars)))
             (equal (env-lookup m (env-permute-polarity 0 mask env numvars))
                    (not (env-lookup m env)))))

  (defret lookup-in-env-permute-polarity-unset
    (implies (and (not (logbitp m mask))
                  (< (nfix m) (nfix numvars)))
             (equal (env-lookup m (env-permute-polarity n mask env numvars))
                    (env-lookup m env))))

  (defret env-permute-polarity-of-swap-polarity
    (equal (env-permute-polarity n mask (env-swap-polarity m env) numvars)
           (env-swap-polarity m (env-permute-polarity n mask env numvars))))

  (local (defthm equal-of-env-swap-polarity
           (equal (equal (env-swap-polarity n x) (env-swap-polarity n y))
                  (nat-equiv x y))
           :hints (("goal" :use ((:instance env-swap-polarity-reverse
                                  (env x))
                                 (:instance env-swap-polarity-reverse
                                  (env y)))
                    :in-theory (disable env-swap-polarity-reverse)))))

  (defret env-permute-polarity-reverse
    (equal (env-permute-polarity n mask new-env numvars)
           (nfix env))
    :hints (("goal" :induct <call>
             :expand ((:free (env) <call>))))))

(define permute-polarity ((n natp)
                          (mask integerp)
                          (truth integerp)
                          (numvars natp))
  :guard (<= n numvars)
  :measure (nfix (- (nfix numvars) (nfix n)))
  :returns (new-truth integerp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        (truth-norm truth numvars))
       (truth (if (logbitp n mask)
                  (swap-polarity n truth numvars)
                truth)))
    (permute-polarity (1+ (lnfix n)) mask truth numvars))
  ///
  (defret eval-of-permute-polarity-with-env-permute-polarity
    (equal (truth-eval new-truth (env-permute-polarity n mask env numvars) numvars)
           (truth-eval truth env numvars))
    :hints(("Goal" :in-theory (enable env-permute-polarity))))

  (defret eval-of-permute-polarity
    (equal (truth-eval new-truth env numvars)
           (truth-eval truth (env-permute-polarity n mask env numvars) numvars))
    :hints (("goal" :use ((:instance eval-of-permute-polarity-with-env-permute-polarity
                           (env (env-permute-polarity n mask env numvars))))
             :in-theory (disable eval-of-permute-polarity-with-env-permute-polarity))))


  (defret permute-polarity-size-basic
    (unsigned-byte-p (ash 1 (nfix numvars)) new-truth)
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret permute-polarity-size
    (implies (and (natp size)
                  (<= (ash 1 (nfix numvars)) size))
             (unsigned-byte-p size new-truth))
    :hints (("goal" :use permute-polarity-size-basic
             :in-theory (disable permute-polarity-size-basic))))

  (defret permute-polarity-identity
    (equal (permute-polarity n 0 truth numvars)
           (truth-norm truth numvars)))

  (defthm permute-polarity-of-truth-norm
    (equal (permute-polarity n mask (truth-norm truth numvars) numvars)
           (permute-polarity n mask truth numvars))))
