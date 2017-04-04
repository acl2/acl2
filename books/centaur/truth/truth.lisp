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


;; e.g. variable 0 initially generates 10
;; for numvars=4, we need to generate 1010 1010  1010 1010
;; meaning double it 3 times.  Start with n = 1.

(define var-repetitions ((n natp) (val natp) (numvars natp))
  :guard (and (<= n numvars)
              (unsigned-byte-p (ash 1 n) val))
  :guard-hints (("goal" :Expand ((ash 1 (+ 1 n)))
                 :in-theory (enable logcons)))
  :measure (nfix (- (nfix numvars) (nfix n)))
  :returns (rep-val natp :rule-classes :type-prescription)
  (b* ((n (lnfix n))
       (shift (ash 1 n))
       (val (mbe :logic (loghead shift (nfix val)) :exec val))
       ((when (mbe :logic (zp (- (nfix numvars) n))
                   :exec (eql n numvars)))
        val))
    (var-repetitions (+ 1 n)
                     (logapp shift val val)
                     numvars))
  ///

  (local (defthmd loghead-less-than-ash-gen-lemma
           (implies (natp i)
                    (< (loghead m x) (ash 1 (+ i (nfix m)))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm loghead-less-than-ash-gen
           (implies (<= (nfix m) (ifix n))
                    (< (loghead m x) (ash 1 n)))
           :hints (("goal" :use ((:instance loghead-less-than-ash-gen-lemma
                                  (i (- (ifix n) (nfix m)))))))))

  (local (defthm loghead-when-less-than-ash
           (implies (and (< (loghead n x) (ash 1 (+ -1 n)))
                         (posp n))
                    (equal (loghead n x)
                           (loghead (1- n) x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm logbitp-of-loghead-past-range
           (implies (< (nfix n) (nfix m))
                    (equal (logbitp n (loghead m x))
                           (logbitp n x)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs)))))

  (local (defthmd loghead-of-plus-one
           (implies (posp n)
                    (equal (loghead n env)
                           (+ (if (logbitp (1- n) env) (ash 1 (1- n)) 0)
                              (loghead (1- n) env))))
           :hints(("Goal" :in-theory (enable* loghead** logbitp**
                                              ihsext-inductions)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:expand ((ash 1 (+ -1 n)))
                         :in-theory (enable logcons))))))



  (defret var-repetitions-invar
    (equal (truth-eval rep-val env numvars)
           (truth-eval (nfix val) (loghead n (nfix env)) numvars))
    :hints(("Goal" :in-theory (enable truth-eval
                                      bitops::logbitp-of-ash-split)
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable loghead-of-plus-one)))))

  (defret var-repetitions-size
    (implies (and (<= (nfix n) numvars)
                  (natp numvars)
                  (unsigned-byte-p (ash 1 (nfix n)) val))
             (unsigned-byte-p (ash 1 numvars) rep-val))
    :hints (("goal" :induct t
             :expand ((ash 1 (+ 1 (nfix n))))
             :in-theory (enable logcons)))))

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
  
  (local (defthmd loghead-less-than-ash
           (implies (not (negp n))
                    (< (loghead n x) (ash 1 n)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm loghead-less-than-ash-times-2-linear
           (implies (natp n)
                    (< (loghead (+ 1 n) x) (* 2 (ash 1 n))))
           :hints (("goal" :use ((:instance loghead-less-than-ash
                                  (n (+ 1 n))))
                    :expand ((ash 1 (+ 1 n)))
                    :in-theory (enable logcons)))
           :rule-classes :linear))

  (defret eval-of-var
    (implies (< (nfix n) (nfix numvars))
             (equal (truth-eval var-enc env numvars)
                    (env-lookup n env)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable truth-eval env-lookup
                                      bitops::logbitp-of-ash-split)))
            (and stable-under-simplificationp
                 '(:in-theory (enable logbitp-in-terms-of-loghead)))))

  (defret logbitp-of-var
    (implies (and (< (nfix n) (nfix numvars))
                  (unsigned-byte-p numvars env))
             (equal (logbitp env var-enc)
                    (logbitp n env)))
    :hints (("goal" :use eval-of-var
             :in-theory (e/d (truth-eval env-lookup)
                             (eval-of-var var)))))

  (defret var-size
    (implies (and (< (nfix n) numvars)
                  (natp numvars))
             (unsigned-byte-p (ash 1 numvars) var-enc))
    :hints (("goal" :expand ((ash 1 (+ 1 (nfix n))))
             :in-theory (enable logcons)))))


(define truth-norm ((truth integerp) (numvars natp))
  :returns (norm-truth)
  (loghead (ash 1 (lnfix numvars)) truth)
  ///
  (local (defthm loghead-less-than-ash-nfix
           (< (loghead n x) (ash 1 (nfix n)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

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
           :hints (("goal" :use ((:instance var-size)
                                 (:instance logbitp-past-width-lemma
                                  (n (ash 1 numvars))
                                  (i (- (nfix i) (ash 1 numvars)))
                                  (x (var n numvars))))
                    :in-theory (e/d (unsigned-byte-p  bitops::expt-2-is-ash)
                                    (var-size))))))

  (local (defthm logbitp-n-of-plus-ash-1-n
           (implies (integerp x)
                    (equal (logbitp n (+ (ash 1 (nfix n)) x))
                           (not (logbitp n x))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

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
                                (loghead numvars (nfix env))))))))))

(define negative-cofactor ((n natp) (truth integerp) (numvars natp))
  :guard (< n numvars)
  :returns (cofactor integerp :rule-classes :type-prescription)
  (B* ((mask (logand (lognot (var n numvars)) truth)))
    (logior mask (ash mask (ash 1 (lnfix n)))))
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
                                     bitops::logbitp-of-ash-split)))
           (and stable-under-simplificationp
                '(:cases ((logbitp n (nfix env))))))))


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
         
  
(define swap-vars ((n natp) (m natp) (truth integerp) (numvars natp))
  :guard (and (< n numvars) (< m numvars))
  :returns (swapped-truth integerp :rule-classes :type-prescription)
  (b* ((xn1 (positive-cofactor n truth numvars))
       (xn0 (negative-cofactor n truth numvars))
       (xn1m1 (positive-cofactor m xn1 numvars))
       (xn1m0 (negative-cofactor m xn1 numvars))
       (xn0m1 (positive-cofactor m xn0 numvars))
       (xn0m0 (negative-cofactor m xn0 numvars))
       (mvar (var m numvars))
       (nvar (var n numvars))
       (~mvar (lognot mvar))
       (~nvar (lognot nvar))
       ;; want (if n (if m xn1m1 xn0m1) (if m xn1m0 xn0m0))
       (n1case (logior (logand mvar xn1m1)
                       (logand ~mvar xn0m1)))
       (n0case (logior (logand mvar xn1m0)
                       (logand ~mvar xn0m0))))
    (logior (logand nvar n1case)
            (logand ~nvar n0case)))
  ///
  (defret eval-of-swap-vars
    (implies (and (< (nfix n) (nfix numvars))
                  (< (nfix m) (nfix numvars)))
             (equal (truth-eval swapped-truth env numvars)
                    (truth-eval truth
                                (env-update n (env-lookup m env)
                                            (env-update m (env-lookup n env) env))
                                numvars)))))
