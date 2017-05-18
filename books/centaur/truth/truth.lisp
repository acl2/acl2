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





(define positive-cofactor ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  :returns (cofactor integerp :rule-classes :type-prescription)
  (B* ((mask (logand (var n numvars) truth)))
    (logior mask (ash mask (- (ash 1 (lnfix n))))))
  ///
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

  (local (defthm loghead-of-install-bit
           (implies (< (nfix n) (nfix w))
                    (Equal (loghead w (install-bit n v x))
                           (install-bit n v (loghead w x))))
           :hints(("Goal" :use ((:instance loghead-of-install-bit-lemma
                                 (i (- (nfix w) (nfix n)))))))))


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

  (local (defthm loghead-of-install-bit
           (implies (< (nfix n) (nfix w))
                    (Equal (loghead w (install-bit n v x))
                           (install-bit n v (loghead w x))))
           :hints(("Goal" :use ((:instance loghead-of-install-bit-lemma
                                 (i (- (nfix w) (nfix n)))))))))


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


(define depends-on ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  (not (equal (truth-norm (positive-cofactor n truth numvars) numvars)
              (truth-norm truth numvars)))
  ///
  (defthm depends-on-correct
    (implies (and (not (depends-on n truth numvars))
                  (< (nfix n) (nfix numvars)))
             (equal (truth-eval truth (env-update n val env) numvars)
                    (truth-eval truth env numvars)))
    :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                           (env (env-update n val env)))
                          (:instance truth-eval-of-truth-norm
                           (truth (positive-cofactor n truth numvars))
                           (env (env-update n val env)))
                          (:instance truth-eval-of-truth-norm)
                          (:instance truth-eval-of-truth-norm
                           (truth (positive-cofactor n truth numvars))))
             :in-theory (disable truth-eval-of-truth-norm)))))

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

