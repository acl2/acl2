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
(include-book "centaur/fty/fixequiv" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable unsigned-byte-p logmask)))
(local (std::add-default-post-define-hook :fix))

;; NUMVARS is the maximum number of variables we'll use.  Truth tables are
;; integers of 2^NUMVARS bits.

;;

; Matt K. mod: Avoid ACL2(p) error from logapp-right-assoc (clause-processor
; returns more than two values).
(set-waterfall-parallelism nil)

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
  :hints(("Goal" :in-theory (enable truth-eval)))))


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


;; BOZO consider moving this to shareable book
(define logrepeat ((times natp) (width natp) (data integerp))
  :returns (reps natp :rule-classes :type-prescription)
  (if (zp times)
      0
    (logapp width data (logrepeat (1- times) width data)))
  ///
  (local (defret size-of-logrepeat-lemma
           (unsigned-byte-p (* (nfix width) (nfix times)) reps)))

  (defret size-of-logrepeat
    (implies (and (<= (* (nfix width) (nfix times)) n)
                  (natp n))
             (unsigned-byte-p n reps)))

  (local (defthm unsigned-byte-p-implies-natp-width
           (implies (unsigned-byte-p m data)
                    (natp m))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))
           :rule-classes :forward-chaining))

  (local (defret size-of-logrepeat-by-data-size-lemma
           (implies (and (unsigned-byte-p m (loghead width data))
                         (<= m (nfix width))
                         (posp times))
                    (unsigned-byte-p (+ m (- (nfix width))
                                        (* (nfix width) (nfix times)))
                                     reps))
           :hints (("goal" :induct <call>
                    :expand ((:free (data) <call>))))))

  (defret size-of-logrepeat-by-data-size
    (implies (and (unsigned-byte-p m (loghead width data))
                  (<= (+ m (- (nfix width))
                         (* (nfix width) (nfix times))) n)
                  (<= m (nfix width))
                  (natp n))
             (unsigned-byte-p n reps))
    :hints (("goal" :use ((:instance size-of-logrepeat-by-data-size-lemma))
             :in-theory (disable size-of-logrepeat-by-data-size-lemma))))

  (local (defun logbitp-of-logrepeat-ind (n width times)
           (if (zp times)
               (list n width)
             (logbitp-of-logrepeat-ind (- (nfix n) (nfix width)) width (1- (nfix times))))))

  (defret logbitp-of-logrepeat
    (equal (logbitp n reps)
           (and (< (nfix n) (* (nfix width) (nfix times)))
                (logbitp (mod (nfix n) (nfix width)) data)))
    :hints(("Goal" :in-theory (enable bitops::logbitp-of-logapp-split)
            :induct (logbitp-of-logrepeat-ind n width times))))

  (defthm logrepeat-1
    (equal (logrepeat 1 width data)
           (loghead width data))
    :hints (("goal" :expand ((logrepeat 1 width data)) )))


  (local (defun mod-less-ind (n width)
           (declare (Xargs :measure (nfix n)))
           (if (zp n)
               width
             (mod-less-ind (- n (* 2 (acl2::pos-fix width))) width))))

  (local (defthm plus-two-minuses
           (equal (+ (- x) (- x))
                  (- (* 2 x)))))

  (local (defthm mod-when-less-than-half
           (implies (and (natp n) (natp w)
                         (< (mod n (* 2 w)) w))
                    (equal (mod n (* 2 w))
                           (mod n w)))
           :hints (("goal"
                   :induct (mod-less-ind n w))
                   (and stable-under-simplificationp
                        '(:cases ((posp w))))
                   (and stable-under-simplificationp
                        '(:cases ((< n (* 2 w))))))))

  (local (defthm mod-when-greater-than-half
           (implies (and (natp n) (natp w)
                         (<= w (mod n (* 2 w))))
                    (equal (mod n (* 2 w))
                           (+ (mod n w) w)))
           :hints (("goal"
                   :induct (mod-less-ind n w))
                   (and stable-under-simplificationp
                        '(:cases ((posp w))))
                   (and stable-under-simplificationp
                        '(:cases ((< n (* 2 w))))))))

  (defthm logrepeat-2x
    (implies (natp width)
             (equal (logrepeat times (* 2 width) (logapp width data data))
                    (logrepeat (* 2 (nfix times)) width data)))
    :hints (("goal" :in-theory (disable logrepeat)
             :do-not-induct t)
            (bitops::equal-by-logbitp-hammer)))

  (defthm logapp-right-assoc
    (implies (<= (nfix w2) (nfix w1))
             (equal (logapp w1 (logapp w2 a b) c)
                    (logapp w2 a
                            (logapp (- (nfix w1) (nfix w2)) b c))))
    :hints ((bitops::logbitp-reasoning)))

  (defthm lognot-of-logrepeat
    (equal (lognot (logrepeat times width data))
           (logapp (* (nfix times) (nfix width))
                   (logrepeat times width (lognot data))
                   -1))))



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
    :hints (("Goal" :use ((:instance size-of-logrepeat-by-data-size
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
                             (size-of-logrepeat-by-data-size
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
    :hints(("Goal" :in-theory (enable truth-eval)))))



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
  (B* ((mask (logand (var n numvars) truth)))
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
                                     bitops::logbitp-of-ash-split)))
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
             :in-theory (disable positive-cofactor-size-basic)))))

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
             :in-theory (disable negative-cofactor-size-basic)))))

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


(define depends-on ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  (B* ((var (var n numvars))
       (truth (truth-norm truth numvars)))
    (not (equal (logand (lognot var) truth)
                (ash (logand var truth)
                     (- (ash 1 (lnfix n)))))))
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

  (local (defthm minus-ash-1-is-install-bit
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
             :cases ((env-lookup n env))))))


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

   (defthm logbitp-of-plus-ash
     (implies (and (integerp x))
              (equal (logbitp m (+ x (ash 1 (nfix m))))
                     (not (logbitp m x))))
     :hints(("Goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs))))

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

   (defthm logbitp-of-minus-ash
     (implies (and (natp m) (integerp x))
              (equal (logbitp m (+ x (- (ash 1 m))))
                     (not (logbitp m x))))
     :hints (("Goal" :use ((:instance logbitp-of-plus-ash
                            (x (+ x (- (ash 1 m))))))
              :in-theory (disable logbitp-of-plus-ash))))

   (defthm logbitp-of-minus-ash-2
     (implies (and (natp m) (integerp x))
              (equal (logbitp m (+ (- (ash 1 m)) x))
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

(define swap-vars ((n natp) (m natp) (truth integerp) (numvars natp))
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

  (defret eval-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix n)))
             (equal (truth-eval swapped-truth env numvars)
                    (truth-eval truth
                                (env-update n (env-lookup m env)
                                            (env-update m (env-lookup n env) env))
                                numvars)))
    :hints(("Goal" :in-theory (e/d (ash-1-monotonic)
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

  (defret size-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix n))
                  (natp size)
                  (<= (ash 1 numvars) size))
             (unsigned-byte-p size swapped-truth))
    :hints (("goal" :use size-of-swap-vars-lemma
             :in-theory (disable size-of-swap-vars-lemma swap-vars)))))




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
           (cond ((< (nfix k) (nfix m)) (env-lookup k env))
                 ((< (nfix k) (nfix n)) (env-lookup (+ 1 (nfix k)) env))
                 ((eql (nfix k) (nfix n)) (env-lookup m env))
                 (t (env-lookup k env))))
    :hints(("Goal" :in-theory (enable* arith-equiv-forwarding))))

  ;; (local (defthm install-bit-redef
  ;;          (equal (install-bit n bit val)
  ;;                 (logapp n val (logapp 1 (bfix bit) (logtail (+ 1 (nfix n))
  ;;                                                             val))))
  ;;          :hints ((logbitp-reasoning))))

  ;; (local (encapsulate nil
  ;;          (defthm lemma4
  ;;            (equal (logapp 1 (bool->bit (logbitp n x)) y)
  ;;                   (logapp 1 (logtail n x) y))
  ;;            :hints ((logbitp-reasoning)))

  ;;          (defthm lemma1
  ;;            (EQUAL (LOGAPP M (NFIX ENV)
  ;;                           (LOGAPP 1 (LOGTAIL M (NFIX ENV))
  ;;                                   (LOGTAIL (+ 1 (NFIX M)) (NFIX ENV))))
  ;;                   (NFIX ENV))
  ;;            :hints ((logbitp-reasoning)))

  ;;          (defthm lemma2
  ;;            (implies (and (natp n)
  ;;                          (< (nfix m) n))
  ;;                     (equal (LOGAPP 1 (LOGTAIL (+ 1 (NFIX M)) (NFIX ENV))
  ;;                                    (LOGAPP (+ -1 N (- (NFIX M)))
  ;;                                            (LOGTAIL (+ 2 (NFIX M)) (NFIX ENV))
  ;;                                            x))
  ;;                            (LOGAPP (+ N (- (NFIX M)))
  ;;                                    (LOGTAIL (+ 1 (NFIX M)) (NFIX ENV))
  ;;                                    x)))
  ;;            :hints ((logbitp-reasoning)))))


  ;; (defretd env-move-var-up-arith
  ;;   (implies (<= (nfix m) (nfix n))
  ;;            (equal perm-env
  ;;                   (let ((env (nfix env)))
  ;;                     (logapp m env
  ;;                             (logapp (- (nfix n) (nfix m))
  ;;                                     (logtail (+ 1 (nfix m)) env)
  ;;                                     (logapp 1 (logbit m env)
  ;;                                             (logtail (+ 1 (nfix n)) env)))))))
  ;;   :hints(("Goal" :in-theory (e/d* (arith-equiv-forwarding
  ;;                                    env-update env-lookup)
  ;;                                   ((:d env-move-var-up)))
  ;;           :induct <call>
  ;;           :expand <call>)))
  )


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
  (local (defun lookup-in-env-move-var-down-ind (m n k env)
           (declare (Xargs :measure (nfix (- (nfix n) (nfix m)))))
           (b* (((when (mbe :logic (zp (- (nfix n) (nfix m)))
                   :exec (eql n m)))
                 (list k env))
                (next (1+ (lnfix m))))
             (lookup-in-env-move-var-down-ind
              next n
              (cond ((< (nfix k) (nfix m)) k)
                    ((eql (nfix k) (nfix m)) (+ 1 (nfix m)))
                    ((eql (nfix k) (+ 1 (nfix m))) (nfix m))
                    (t k))
              env))))

  (local (defthm not-equal-incr-of-nfix
           (not (equal m (+ 1 (nfix m))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret lookup-in-env-move-var-down
    (implies (<= (nfix m) (nfix n))
             (equal (env-lookup k perm-env)
                    (cond ((< (nfix k) (nfix m)) (env-lookup k env))
                          ((eql (nfix k) (nfix m)) (env-lookup n env))
                          ((<= (nfix k) (nfix n)) (env-lookup (+ -1 (nfix k)) env))
                          (t (env-lookup k env)))))
    :hints(("Goal" :in-theory (enable* arith-equiv-forwarding)
            :induct (lookup-in-env-move-var-down-ind m n k env))))



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
    :hints(("Goal" :in-theory (enable env-move-var-up))))

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
    :hints(("Goal" :in-theory (enable truth-norm)))))



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
    :hints(("Goal" :in-theory (enable env-move-var-down))))

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
    :hints(("Goal" :in-theory (enable truth-norm)))))



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


  (local (defun lookup-in-env-permute-stretch-ind (n mask env numvars k)
           (declare (xargs :measure (nfix (- (nfix numvars) (nfix n)))))
           (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                            :exec (eql n numvars)))
                 (list k env))
                (n (lnfix n))
                (count (logcount (loghead n (lnfix mask))))
                (bit (logbit n (lnfix mask))))
             ;; (equal (env-lookup k (env-move-var-up m n env))
             ;; (cond ((< (nfix k) (nfix m)) (env-lookup k env))
             ;;       ((< (nfix k) (nfix n)) (env-lookup (+ 1 (nfix k)) env))
             ;;       ((eql (nfix k) (nfix n)) (env-lookup m env))
             ;;       (t (env-lookup k env))))
             (lookup-in-env-permute-stretch-ind
              (1+ n) mask env numvars
              (if (eql bit 1)
                  (cond ((< (nfix k) count) k)
                        ((< (nfix k) (nfix n)) (+ 1 (nfix k)))
                        ((eql (nfix k) (nfix n)) count)
                        (t k))
                k)))))

  (defret lookup-in-env-permute-stretch
    (implies (<= (nfix n) (nfix numvars))
             (equal (env-lookup k perm-env)
                    (cond ((< (nfix k) (logcount (loghead n (nfix mask))))
                           (env-lookup k env))
                          ((< (nfix k) (nfix n))
                           (env-lookup (+ (nfix k)
                                          (- (logcount (loghead numvars (nfix mask)))
                                             (logcount (loghead n (nfix mask)))))
                                       env))
                          ((and (< (nfix k) (nfix numvars))
                                (logbitp k (nfix mask)))
                           (env-lookup (logcount (loghead k (nfix mask))) env))
                          (t (env-lookup (+ (nfix k)
                                            (- (logcount (loghead k (loghead numvars (nfix mask)))))
                                            (logcount (loghead numvars (nfix mask))))
                                         env)))))
    :hints (("goal" :induct (lookup-in-env-permute-stretch-ind n mask env numvars k)
             :in-theory (enable* arith-equiv-forwarding)
             :expand ((:free (count) <call>))))))



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
  (defthmd nth-set-bit-pos-when-logcount
    (implies (and (< (nfix n) (logcount x))
                  (natp x))
             (equal (nth-set-bit-pos n x)
                    (if (and (zp n) (eql (logcar x) 1))
                        0
                      (+ 1 (nth-set-bit-pos (- (lnfix n) (logcar x))
                                            (logcdr x))))))
    :hints(("Goal" :in-theory (enable logcount**)
            :induct (nth-set-bit-pos n x)))
    :rule-classes
    ((:definition :controller-alist ((nth-set-bit-pos t t))))))




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

  ;; input:  01 23 45 67 8
  ;; mask:   10 10 11 10 1
  ;; n=4          ^
  ;; ncnt=2    ^
  ;; tcnt=6          ^
  ;; tcnt+n-ncnt=8      ^
  ;; res:    01 45 68 23 7
  ;;         ^^ unchanged
  ;;            ^^ ^^ n+bitpos(k-ncnt,tail(n,mask))
  ;;                  ^^  k-tcnt+ncnt
  ;;                     ^ n+bitpos(k-(tcnt+n-ncnt), tail(n,mask))

  ;; input:  01 23 4 56 78
  ;; mask:   10 10 1 01 01
  ;; n=4          ^
  ;; ncnt=2    ^
  ;; tcnt=5         ^
  ;; tcnt+n-ncnt=7     ^
  ;; res:    01 46 8 23 57
  ;;         ^^ unchanged
  ;;            ^^ ^ n+bitpos(k-ncnt,tail(n,mask))
  ;;                 ^^  k-tcnt+ncnt
  ;;                    ^^ n+bitpos(k-(tcnt+n-ncnt), tail(n,mask))


  ;; input:  012 34 5 67 8
  ;; mask:   101 01 0 10 1
  ;; n=6             ^
  ;; ncnt=3     ^
  ;; tcnt=5        ^
  ;; tcnt+n-ncnt=8      ^
  ;; res:    012 68 3 45 7
  ;;         ^^ unchanged
  ;;             ^^ n+bitpos(k-ncnt,tail(n,mask))
  ;;                ^ ^^  k-tcnt+ncnt
  ;;                     ^ n+bitpos(k-(tcnt+n-ncnt), tail(n,mask))

  (local (in-theory (disable bitops::logtail-of-loghead)))

  (defthm logcount-of-logtail
    (implies (not (negp x))
             (equal (logcount (logtail n x))
                    (- (logcount x)
                       (logcount (loghead n x)))))
    :hints(("Goal" :in-theory (enable* ihsext-inductions
                                       ihsext-recursive-redefs
                                       logcount**))))

;;   ;; (local (defthm nth-set-bit-pos-0-when-not-zip
;;   ;;          (implies (not (zip x))
;;   ;;                   (natp (nth-set-bit-pos 0 x)))
;;   ;;          :hints (("goal" :induct (integer-length x)
;;   ;;                   :in-theory (enable* nth-set-bit-pos
;;   ;;                                       ihsext-inductions)))
;;   ;;          :rule-classes :type-prescription))

  (local (defthm nth-set-bit-pos-of-logcdr
           (implies (and (natp x)
                         (< (nfix n) (logcount (logcdr x))))
                    (equal (nth-set-bit-pos n (logcdr x))
                           (- (nth-set-bit-pos (+ (logcar x) (nfix n)) x)
                              1)))
           :hints (("goal" :expand
                    ((:with nth-set-bit-pos-when-logcount
                      (nth-set-bit-pos (+ (logcar x) (nfix n)) x))
                     (:with nth-set-bit-pos-when-logcount
                      (nth-set-bit-pos n (logcdr x)))
                     (:with nth-set-bit-pos-when-logcount
                      (nth-set-bit-pos 0 (logcdr x)))
                     (logcount x))))))

;;   ;; (local (defthm nfix-of-minus-1
;;   ;;          (<= (nfix (+ -1 x)) (nfix x))
;;   ;;          :hints(("Goal" :in-theory (enable nfix)))
;;   ;;          :rule-classes :linear))

;;   ;; (local (defthm nfix-minus-1-equal
;;   ;;          (iff (equal (nfix (+ -1 x)) (nfix x))
;;   ;;               (zp x))
;;   ;;          :hints(("Goal" :in-theory (enable nfix)))))

;;   ;; (local (defthm integer-length-and-zero-logtail-implies-logbitp
;;   ;;          (implies (and (<= (integer-length x) (nfix k))
;;   ;;                        (not (logbitp k x)))
;;   ;;                   (equal (equal (logtail k x) 0) t))
;;   ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions ihsext-recursive-redefs)))))

;;   ;; (local (defun nth-set-bit-pos-of-logtail-ind (k n x)
;;   ;;          (declare (xargs :measure (+ (integer-length (logtail k x)) (nfix n))
;;   ;;                          :hints(("Goal" :in-theory (enable bool->bit)))))
;;   ;;          (if (zip (logtail k x))
;;   ;;              nil
;;   ;;            (b* ((bit (logcar (logtail k x)))
;;   ;;                 ((when (and (zp n) (eql bit 1))) 0))
;;   ;;              (nth-set-bit-pos-of-logtail-ind (+ 1 (nfix k)) (- (lnfix n) bit) x)))))

;;   ;; (local (defthm nth-set-bit-pos-of-logcount-when-logbitp
;;   ;;          (implies (logbitp k x)
;;   ;;                   (equal (nth-set-bit-pos (logcount (loghead k x)) x)
;;   ;;                          (nfix k)))
;;   ;;          :hints(("Goal" :in-theory (enable* ihsext-inductions
;;   ;;                                             ihsext-recursive-redefs
;;   ;;                                             nth-set-bit-pos)))))

  (defthm nth-set-bit-pos-of-logtail
    (implies (and (natp x)
                  (< (nfix n) (logcount (logtail k x))))
             (equal (nth-set-bit-pos n (logtail k x))
                    (- (nth-set-bit-pos (+ (logcount (loghead k x)) (nfix n))
                                        x)
                       (nfix k))))
    :hints (("goal" :induct (logtail k x)
             :in-theory (enable* ihsext-inductions
                                 ihsext-recursive-redefs
                                 logcount**)
             )
            (and stable-under-simplificationp
                 '(:expand ((:with nth-set-bit-pos-when-logcount
                             (nth-set-bit-pos n x)))))))

  (local (defthm logcount-of-logcdr
           (implies (natp x)
                    (equal (logcount (logcdr x))
                           (- (logcount x) (logcar x))))
           :hints (("goal" :expand ((logcount x))))))


  (local (defthm logcount->-logcount-loghead
           (implies (and (natp x)
                         (logbitp n x))
                    (< (logcount (loghead n x)) (logcount x)))
           :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                            ihsext-recursive-redefs
                                            logcount**)
                                           (logcount-of-logcdr))))
           :rule-classes :linear))

;;   (local (defthm logcount->=-logcount-loghead
;;            (implies (natp x)
;;                     (<= (logcount (loghead n x)) (logcount x)))
;;            :hints(("Goal" :in-theory (e/d* (ihsext-inductions
;;                                             ihsext-recursive-redefs
;;                                             logcount**)
;;                                            (logcount-of-logcdr))))
;;            :rule-classes :linear))


;;   (local (defthm logcount-loghead-monotonic
;;            (implies (and (natp x)
;;                          (<= (nfix n1) (nfix n2)))
;;                     (<= (logcount (loghead n1 x)) (logcount (loghead n2 x))))
;;            :hints (("goal" :use ((:instance logcount->=-logcount-loghead
;;                                   (n n1) (x (loghead n2 x))))
;;                     :in-theory (disable logcount->=-logcount-loghead)))
;;            :rule-classes :linear))

;;   (local (defthm logcount-loghead-monotonic-strong
;;            (implies (and (natp x)
;;                          (< (nfix n1) (nfix n2))
;;                          (logbitp n1 x))
;;                     (< (logcount (loghead n1 x)) (logcount (loghead n2 x))))
;;            :hints (("goal" :use ((:instance logcount->-logcount-loghead
;;                                   (n n1) (x (loghead n2 x))))
;;                     :in-theory (disable logcount->=-logcount-loghead)))
;;            :rule-classes :linear))

  (local (defthm logcount-when-logbitp
           (implies (and (natp x)
                         (logbitp n x))
                    (< 0 (logcount x)))
           :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                            ihsext-recursive-redefs
                                            logcount**)
                                           (logcount-of-logcdr))))
           :rule-classes :linear))

  (local (defthm nth-set-bit-pos-of-logcount-of-loghead-lemma
           (implies (and (logbitp n x)
                         (natp x))
                    (equal (nth-set-bit-pos (logcount (loghead n x)) x)
                           (nfix n)))
           :hints (("goal" :in-theory (e/d* (ihsext-inductions
                                               ihsext-recursive-redefs
                                               logcount**)
                                            (nth-set-bit-pos-of-logcdr
                                             logcount-of-logcdr))
                    :expand ((:with nth-set-bit-pos-when-logcount
                              (:Free (n) (nth-set-bit-pos n x)))
                             (logcount x))
                    :induct (loghead n x)))))

  (local (defthm nth-set-bit-pos-of-logcount-of-loghead
           (implies (and (bind-free (case-match y
                                      (('ACL2::LOGHEAD$INLINE N &)
                                       `((n . ,n))))
                                    (n))
                         (equal y (loghead n x))
                         (logbitp n x)
                         (natp x))
                    (equal (nth-set-bit-pos (logcount y) x)
                           (nfix n)))))

  (local (defthm nth-set-bit-pos-of-logcount-of-loghead2
           (implies (and (equal y (logcount (loghead n x2)))
                         (equal (loghead n x2) (loghead n x))
                         (logbitp n x)
                         (natp x))
                    (equal (nth-set-bit-pos y x)
                           (nfix n)))))

  (local (defthm loghead-of-nfix
           (equal (loghead (nfix n) x)
                  (loghead n x))))

  (local (defthm logcount-equal-0-when-logcar
           (implies (and (equal (logcar x) 1)
                         (natp x))
                    (equal (equal (logcount (loghead n x)) 0)
                           (zp n)))
           :hints (("goal" :expand ((loghead n x))
                    :in-theory (enable logcount**)))))




;; ;; dynamic validation:
;; ;; (loop for k from 0 to 6 always (loop for mask from 0 to 31 always (loop for env from 0 to 31 always (loop for n from 0 to 5 always
;; ;; (let* ((numvars 5) (count (logcount (loghead n mask)))
;; ;;        (perm-env (env-permute-shrink n count mask env numvars)))
;; ;;        (cw "k ~x0 mask ~x1 env ~x2 n ~x3~%" k mask env n)
;; ;;        (equal (env-lookup k perm-env)
;; ;;                     (cond ((< (nfix k) (logcount (loghead n (nfix mask))))
;; ;;                            (env-lookup k env))
;; ;;                           ((< (nfix k) (logcount (loghead numvars (nfix mask))))
;; ;;                            (env-lookup (+ (nfix n)
;; ;;                                           (nth-set-bit-pos
;; ;;                                            (- (nfix k) (logcount (loghead n (nfix mask))))
;; ;;                                            (logtail n (loghead numvars (nfix mask)))))
;; ;;                                        env))
;; ;;                           ((<= (nfix numvars) (nfix k))
;; ;;                            (env-lookup k env))
;; ;;                           ((< (nfix k) (+ (logcount (loghead numvars (nfix mask)))
;; ;;                                           (nfix n)
;; ;;                                           (- (logcount (loghead n (nfix mask))))))
;; ;;                            (env-lookup (+ (nfix k)
;; ;;                                           (- (logcount (loghead numvars (nfix mask))))
;; ;;                                           (logcount (loghead n (nfix mask))))
;; ;;                                        env))
;; ;;                           (t
;; ;;                            (env-lookup (+ (nfix n)
;; ;;                                           (nth-set-bit-pos
;; ;;                                            (- (nfix k)
;; ;;                                               (+ (logcount (loghead numvars (nfix mask)))
;; ;;                                                  (nfix n)
;; ;;                                                  (- (logcount (loghead n (nfix mask))))))
;; ;;                                            (logtail n (loghead numvars (lognot (nfix mask))))))
;; ;;                                        env)))))))))

  (local (defthm nth-set-bit-pos-gte-k
           (implies (and (natp x)
                         (< (nfix k) (logcount X)))
                    (<= (nfix k) (nth-set-bit-pos k x)))
           :hints(("Goal" :in-theory (enable nth-set-bit-pos logcount**)))
           :rule-classes :linear))


;;   (local (defthm loghead-numvars-when-<=-k
;;            (implies (and (<= (logcount (loghead numvars x)) k)
;;                          (equal k (logcount (loghead n x)))
;;                          (<= (nfix n) (nfix numvars))
;;                          (natp x)
;;                          (syntaxp (not (equal n numvars))))
;;                     (equal (logcount (loghead numvars x))
;;                            (logcount (loghead n x))))
;;            ;; :hints (("goal" :use ((:instance logcount-loghead-monotonic
;;            ;;                        (n1 n) (n2 numvars)))
;;            ;;          :in-theory (disable logcount-loghead-monotonic)))
;;            ))

;;   (local (defthm logcount-gt-k-when-equal-lesser-logcount
;;            (implies (and (equal k (logcount (loghead n x)))
;;                          (< (nfix n) (nfix numvars))
;;                          (logbitp n x)
;;                          (natp x))
;;                     (> (logcount (loghead numvars x)) k))))
;;            ;; :hints (("goal" :use ((:instance logcount-loghead-monotonic-strong
;;            ;;                        (n1 n) (n2 numvars)))
;;            ;;          :in-theory (disable logcount-loghead-monotonic-strong)))))


;;   (local (defthm logcount-loghead-lognot
;;            (equal (logcount (loghead n (lognot x)))
;;                   (- (nfix n) (logcount (loghead n x))))
;;            :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                               ihsext-recursive-redefs
;;                                               logcount**)))))



  (defret lookup-in-env-permute-shrink
    (implies (and (<= (nfix n) (nfix numvars))
                  (< (nfix k) (logcount (loghead numvars (nfix mask)))))
             (equal (env-lookup k perm-env)
                    (cond ((< (nfix k) (logcount (loghead n (nfix mask))))
                           (env-lookup k env))
                          (t ;;(< (nfix k) (logcount (loghead numvars (nfix mask))))
                           (env-lookup (+ (nfix n)
                                          (nth-set-bit-pos
                                           (- (nfix k) (logcount (loghead n (nfix mask))))
                                           (logtail n (loghead numvars (nfix mask)))))
                                       env))
                          ;; ((<= (nfix numvars) (nfix k))
                          ;;  (env-lookup k env))
                          ;; ((< (nfix k) (+ (logcount (loghead numvars (nfix mask)))
                          ;;                 (nfix n)
                          ;;                 (- (logcount (loghead n (nfix mask))))))
                          ;;  (env-lookup (+ (nfix k)
                          ;;                 (- (logcount (loghead numvars (nfix mask))))
                          ;;                 (logcount (loghead n (nfix mask))))
                          ;;              env))
                          ;; (t
                          ;;  (env-lookup (+ (nfix n)
                          ;;                 (nth-set-bit-pos
                          ;;                  (- (nfix k)
                          ;;                     (+ (logcount (loghead numvars (nfix mask)))
                          ;;                        (nfix n)
                          ;;                        (- (logcount (loghead n (nfix mask))))))
                          ;;                  (logtail n (loghead numvars (lognot (nfix mask))))))
                          ;;              env))
                          )))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding)
             :do-not-induct t
             :expand ((:free (count) <call>)
                      (:with nth-set-bit-pos-when-logcount
                       (NTH-SET-BIT-POS K (LOGHEAD NUMVARS (NFIX MASK))))
                      (:with nth-set-bit-pos-when-logcount
                       (NTH-SET-BIT-POS 0 (LOGHEAD NUMVARS (NFIX MASK))))
                      ;; (:with nth-set-bit-pos-when-logcount
                      ;;  (nth-set-bit-pos (+ (NFIX K)
                      ;;                      (- (LOGCOUNT (LOGHEAD N (NFIX MASK)))))
                      ;;                   (loghead (+ numvars (- (nfix n)))
                      ;;                            (logtail n (nfix mask)))))
                      ;; (:with nth-set-bit-pos-when-logcount
                      ;;  (nth-set-bit-pos (+ K (- (NFIX N))
                      ;;                      (LOGCOUNT (LOGHEAD N (NFIX MASK)))
                      ;;                      (- (LOGCOUNT (LOGHEAD NUMVARS (NFIX MASK)))))
                      ;;                   (LOGHEAD (+ NUMVARS (- (NFIX N)))
                      ;;                            (LOGTAIL N (NFIX MASK)))))
                      )))))














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
    :hints(("Goal" :in-theory (enable truth-norm)))))



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
    :hints(("Goal" :in-theory (enable truth-norm)))))

