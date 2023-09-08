; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")


(include-book "override-transparency")
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "alist-thms"))
(local (include-book "std/alists/alist-keys" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define svar-overridekeys-envs-ok ((x svar-p)
                                   (params svarlist-p)
                                   (overridekeys svarlist-p)
                                   (impl-env svex-env-p)
                                   (spec-env svex-env-p)
                                   (spec-outs svex-env-p))
  :returns (agree)
  (cond ((and (or (svar-override-p x :test)
                  (svar-override-p x :val))
              (svarlist-member-nonoverride x overridekeys))
         (and (4vec-override-mux-<<= (svex-env-lookup (svar-change-override x :test) impl-env)
                                     (svex-env-lookup (svar-change-override x :val) impl-env)
                                     (svex-env-lookup (svar-change-override x :test) spec-env)
                                     (svex-env-lookup (svar-change-override x :val) spec-env)
                                     (svex-env-lookup (svar-change-override x nil) spec-outs))
              (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override x :test) spec-env)
                                    (svex-env-lookup (svar-change-override x :test) impl-env))))
        ((member-equal (svar-fix x) (svarlist-fix params))
         (equal (svex-env-lookup x impl-env)
                (svex-env-lookup x spec-env)))
        (t (4vec-<<= (svex-env-lookup x impl-env)
                     (svex-env-lookup x spec-env))))
  ///
  (local (in-theory (enable svar-override-p-when-other)))
  
  (defretd 4vec-muxtest-subsetp-when-<fn>-test
    (implies (and agree
                  (svar-override-p x :test)
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup x spec-env)
                                   (svex-env-lookup x impl-env))))

  (defretd 4vec-muxtest-subsetp-when-<fn>-val
    (implies (and agree
                  (svar-override-p x :val)
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override x :test) spec-env)
                                   (svex-env-lookup (svar-change-override x :test) impl-env))))

  (defretd 4vec-override-mux-<<=-when-<fn>-val
    (implies (and agree
                  (svar-override-p x :val)
                  (equal (svar-fix testvar) (svar-change-override x :test))
                  (equal (svar-fix refvar) (svar-change-override x nil))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-override-mux-<<= (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup x impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup x spec-env)
                                   (svex-env-lookup refvar spec-outs))))

  (defretd 4vec-override-mux-<<=-when-<fn>-test
    (implies (and agree
                  (svar-override-p x :test)
                  (equal (svar-fix valvar) (svar-change-override x :val))
                  (equal (svar-fix refvar) (svar-change-override x nil))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-override-mux-<<= (svex-env-lookup x impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup x spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs))))

  (local (defthm 4vec-override-mux-implies-ite-<<=
           (implies (and (4vec-override-mux-<<= impl-test impl-val spec-test spec-val ref-val)
                         (4vec-muxtest-subsetp spec-test impl-test))
                    (4vec-<<= (4vec-bit?! impl-test impl-val ref-val)
                              (4vec-bit?! spec-test spec-val ref-val)))
           :hints(("Goal" :in-theory (enable 4vec-bit?!
                                             4vec-bitmux
                                             4vec-muxtest-subsetp
                                             4vec-override-mux-<<=
                                             4vec-<<=))
                  (acl2::logbitp-reasoning))))
  
  (defretd 4vec-bit?!-ok-when-<fn>-test
    (implies (and agree
                  (svar-override-p x :test)
                  (equal (svar-fix valvar) (svar-change-override x :val))
                  (equal refval (svex-env-lookup (svar-change-override x nil) spec-outs))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-<<= (4vec-bit?! (svex-env-lookup x impl-env) (svex-env-lookup valvar impl-env) refval)
                       (4vec-bit?! (svex-env-lookup x spec-env) (svex-env-lookup valvar spec-env) refval))))

  (defretd 4vec-bit?!-ok-when-<fn>-val
    (implies (and agree
                  (svar-override-p x :val)
                  (equal (svar-fix testvar) (svar-change-override x :test))
                  (equal refval (svex-env-lookup (svar-change-override x nil) spec-outs))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-<<= (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup x impl-env) refval)
                       (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup x spec-env) refval))))

  (defretd nonoverride-params-ok-when-<fn>
    (implies (and agree
                  (member-equal (svar-fix x) (svarlist-fix params))
                  (or (svar-override-p x nil)
                      (and (not (svar-override-p x :test))
                           (not (svar-override-p x :val)))
                      (not (svarlist-member-nonoverride x overridekeys))))
             (equal (svex-env-lookup x impl-env)
                    (svex-env-lookup x spec-env))))

  (defretd nonoverride-vars-ok-when-<fn>
    (implies (and agree
                  (or (svar-override-p x nil)
                      (and (not (svar-override-p x :test))
                           (not (svar-override-p x :val)))
                      (not (svarlist-member-nonoverride x overridekeys))))
             (4vec-<<= (svex-env-lookup x impl-env)
                       (svex-env-lookup x spec-env))))
             

  (defcong svex-envs-similar equal (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 5)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 6)

  (defcong set-equiv equal (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 2)
  (defcong set-equiv equal (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 3))

;; We want to show that if an expr/list/alist is overridekey-transparent AND
;; partially monotonic with the given params, then overridekeys-envs-ok of two
;; envs implies the evaluation on the impl-env <<= the evaluation on the
;; spec-env.  To do this we need to find an intermediate env that satisfies
;; overridekeys-envs-agree with the spec-env/spec-outs, >>= the impl-env, and
;; agrees with the impl-env on the params and tests.  That way we can use
;; overridekey-transparency and partial-monotonicity to complete the proof.


(local
 (progn
   (defthmd normalize-svar-change-override-when-equal-1
     (implies (and (equal (svar-change-override x nil)
                          (svar-change-override var nil))
                   (syntaxp (acl2::<< x var)))
              (equal (svar-change-override var type)
                     (svar-change-override x type)))
     :hints(("Goal" :in-theory (enable equal-of-svar-change-override))))

   (defthmd normalize-svar-change-override-when-equal-2
     (implies (and (equal (svar-change-override x nil)
                          (svar-change-override var nil))
                   (svar-override-p x type))
              (equal (svar-change-override var type)
                     (svar-fix x)))
     :hints(("Goal" :in-theory (enable equal-of-svar-change-override))))

   
   (local (defthm equal-of-logtail-when-loghead
            (implies (equal (loghead n x)
                            (loghead n y))
                     (equal (equal (logtail n x) (logtail n y))
                            (equal (ifix x) (ifix y))))
            :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)
                    :induct t)
                   (and stable-under-simplificationp
                        '(:use ((:instance bitops::equal-logcons-strong
                                 (a (logcar x)) (b (logcdr x)) (i (ifix y)))))))))

   (local (defthm equal-of-ash-same
         (implies (natp n)
                  (equal (equal (ash x n) (ash y n))
                         (equal (ifix x) (ifix y))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                           bitops::ihsext-recursive-redefs)))))
   
   (defthmd svar-equiv-when-equal-svar-change-override
     (implies (and (svar-override-p x type)
                   (svar-override-p var type))
              (equal (equal (svar-change-override x nil)
                            (svar-change-override var nil))
                     (svar-equiv x var)))
     :hints(("Goal" :in-theory (enable svar-override-p svar-change-override
                                       svar-fix-redef
                                       svar->override-test
                                       svar->override-val))))))


(define svar-overridekeys-env-keys ((x svar-p)
                                    (overridekeys svarlist-p))
  :returns (env-keys svarlist-p)
  (if (and (or (svar-override-p x :test)
               (svar-override-p x :val))
           (svarlist-member-nonoverride x overridekeys))
      (list (svar-change-override x :test)
            (svar-change-override x :val))
    (list (svar-fix x)))
  ///
  (defretd svar-overridekeys-envs-ok-when-member-<fn>
    (implies (and (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                  (member-equal (svar-fix v) (svar-overridekeys-env-keys x overridekeys)))
             (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-ok
                                      equal-of-svar-change-override
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override))))

  (defretd svar-overridekeys-envs-agree-when-member-<fn>
    (implies (and (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)
                  (member-equal (svar-fix v) (svar-overridekeys-env-keys x overridekeys)))
             (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree
                                      equal-of-svar-change-override
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override))))

  (defret member-of-<fn>-no-fix
    (iff (member-equal x env-keys)
         (svar-p x)))

  (defret member-of-<fn>
    (member-equal (svar-fix x) env-keys))

  

  (defret member-of-<fn>-when-nonoverride
    (implies (or (svar-override-p v nil)
                 (and (not (svar-override-p v :test))
                      (not (svar-override-p v :val)))
                 (not (svarlist-member-nonoverride v overridekeys)))
             (iff (member-equal v env-keys) (equal v (svar-fix x))))))

(define svar-overridekeys-envs-ok-intermediate-env ((x svar-p)
                                                    (params svarlist-p)
                                                    (overridekeys svarlist-p)
                                                    (impl-env svex-env-p)
                                                    (spec-env svex-env-p)
                                                    (spec-outs svex-env-p))

  :returns (intermed-env svex-env-p)
  (cond ((and (or (svar-override-p x :test)
                  (svar-override-p x :val))
              (svarlist-member-nonoverride x overridekeys))
         (b* ((testvar (svar-change-override x :test))
              (valvar (svar-change-override x :val))
              (impl-test (svex-env-lookup (svar-change-override x :test) impl-env)))
           (list (cons testvar impl-test)
                 (cons valvar (4vec-bit?! impl-test
                                          (4vec-bit?! (svex-env-lookup testvar spec-env)
                                                      (svex-env-lookup valvar spec-env)
                                                      (svex-env-lookup (svar-change-override x nil) spec-outs))
                                          (svex-env-lookup valvar impl-env))))))
        ((member-equal (svar-fix x) (svarlist-fix params))
         (list (cons (svar-fix x) (svex-env-lookup x impl-env))))
        (t (list (cons (svar-fix x) (svex-env-lookup x spec-env)))))
  ///

  
  ;; (local (defthm svar-override-p-when-equal-change-override
  ;;          (implies (equal (svar-fix v) (svar-change-override x type))
  ;;                   (svar-override-p v type))
  ;;          :hints (("goal" :use ((:instance SVAR-OVERRIDE-P-OF-SVAR-CHANGE-OVERRIDE
  ;;                                 (x x) (type type) (other-type type)))))))
  (local (defthm 4vec-override-mux-agrees-of-construct
           (implies (4vec-muxtest-subsetp spec-test impl-test)
                    (4vec-override-mux-agrees impl-test
                                              (4vec-bit?! impl-test
                                                          (4vec-bit?! spec-test spec-val ref-val)
                                                          impl-val)
                                              spec-test spec-val ref-val))
           :hints(("Goal" :in-theory (enable 4vec-override-mux-agrees
                                             4vec-bit?!
                                             4vec-bitmux
                                             4vec-muxtest-subsetp))
                  (acl2::logbitp-reasoning))))

  (local (defthm 4vec-<<=-of-construct
           (implies (and (4vec-muxtest-subsetp spec-test impl-test)
                         (4vec-override-mux-<<= impl-test impl-val spec-test spec-val ref-val))
                    (4vec-<<= impl-val (4vec-bit?! impl-test
                                                   (4vec-bit?! spec-test spec-val ref-val)
                                                   impl-val)))
           :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
                                             4vec-bit?!
                                             4vec-bitmux
                                             4vec-<<=
                                             4vec-muxtest-subsetp))
                  (acl2::logbitp-reasoning))))

  
  (defret <fn>-svar-overridekeys-envs-agree
    (implies (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
             (svar-overridekeys-envs-agree x overridekeys (append intermed-env rest) spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree
                                      svar-overridekeys-envs-ok
                                      svex-env-lookup-of-cons-split
                                      equal-of-svar-change-override
                                      svar-override-p-when-other))))

  (defret <fn>-svex-env-<<=
    (implies (and (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                  (svex-env-<<= impl-env rest))
             (svex-env-<<= impl-env (append intermed-env rest)))
    :hints(("Goal" :in-theory (enable svex-env-<<=
                                      svar-overridekeys-envs-ok
                                      svex-env-lookup-of-cons-split))))


  (defret <fn>-preserves-svar-overridekeys-envs-agree
    (implies (and (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                  (svar-overridekeys-envs-agree var overridekeys rest spec-env spec-outs))
             (svar-overridekeys-envs-agree var overridekeys (append intermed-env rest) spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree
                                      svar-overridekeys-envs-ok
                                      svex-env-lookup-of-cons-split
                                      equal-of-svar-change-override
                                      svar-override-p-when-other
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys intermed-env)
           (svar-overridekeys-env-keys x overridekeys))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      alist-keys))))

  (defretd lookup-param-of-<fn>
    (implies (and (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys)))
                  (member-equal (svar-fix v) (svarlist-fix params)))
             (equal (svex-env-lookup v intermed-env)
                    (if (equal (svar-fix v) (svar-fix x))
                        (svex-env-lookup v impl-env)
                      (4vec-x))))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      equal-of-svar-change-override
                                      svar-override-p-when-other
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override
                                      svex-env-lookup-of-cons-split))))

  (defretd lookup-test-of-<fn>
    (implies (and (svar-override-p v :test)
                  (svarlist-member-nonoverride v overridekeys))
             (equal (svex-env-lookup v intermed-env)
                    (if (member-equal (svar-fix v) (svar-overridekeys-env-keys x overridekeys))
                        (svex-env-lookup v impl-env)
                      (4vec-x))))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      equal-of-svar-change-override
                                      svar-override-p-when-other
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override
                                      svex-env-lookup-of-cons-split)))))

                  




(define svarlist-overridekeys-envs-ok-badguy ((x svarlist-p)
                                              (params svarlist-p)
                                              (overridekeys svarlist-p)
                                              (impl-env svex-env-p)
                                              (spec-env svex-env-p)
                                              (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (if (atom x)
      nil
    (if (svar-overridekeys-envs-ok (car x) params overridekeys impl-env spec-env spec-outs)
        (svarlist-overridekeys-envs-ok-badguy (cdr x) params overridekeys impl-env spec-env spec-outs)
      (svar-fix (car x))))
  ///
  (defretd <fn>-when-witness
    (implies (and (not (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-fix))))

  (defretd not-svar-overridekeys-envs-ok-of-<fn>
    (implies badguy
             (not (svar-overridekeys-envs-ok badguy params overridekeys impl-env spec-env spec-outs))))

  (defretd member-of-<fn>
    (implies badguy
             (member-equal badguy (svarlist-fix x))))

  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs) 5)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs) 6)

  (defcong set-equiv equal (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs) 2)
  (defcong set-equiv equal (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs) 3)

  (defthm svarlist-overridekeys-envs-ok-badguy-of-append
    (equal (svarlist-overridekeys-envs-ok-badguy (append x y) params overridekeys impl-env spec-env spec-outs)
           (or (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)
               (svarlist-overridekeys-envs-ok-badguy y params overridekeys impl-env spec-env spec-outs)))))

(define svarlist-overridekeys-envs-ok ((x svarlist-p)
                                       (params svarlist-p)
                                       (overridekeys svarlist-p)
                                       (impl-env svex-env-p)
                                       (spec-env svex-env-p)
                                       (spec-outs svex-env-p))
  :returns (ok)
  :hooks ((:fix :hints nil))
  (not (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs))
  ///
  (defretd <fn>-implies
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok
                                      svarlist-overridekeys-envs-ok-badguy-when-witness))))

  (defretd badguy-not-ok-when-not-<fn>
    (implies (not ok)
             (not (svar-overridekeys-envs-ok
                   (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)
                   params overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok
                                      not-svar-overridekeys-envs-ok-of-svarlist-overridekeys-envs-ok-badguy))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not ok)
             (member-equal
              (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok
                                      member-of-svarlist-overridekeys-envs-ok-badguy))))

  (defretd badguy-member-when-not-<fn>
    (implies (and (not ok)
                  (svarlist-p x))
             (member-equal
              (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)
              x))
    :hints(("Goal" :use ((:instance badguy-member-fix-when-not-<fn>)))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not ok)
             (member-equal
              (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok
                                      member-of-svarlist-overridekeys-envs-ok-badguy))))

  (defretd <fn>-by-witness
    (implies (not ok)
             (b* ((badguy (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)))
               (and (svar-p badguy)
                    (member-equal badguy (svarlist-fix x))
                    (not (svar-overridekeys-envs-ok badguy params overridekeys impl-env spec-env spec-outs)))))
    :hints(("Goal" :in-theory (enable badguy-member-fix-when-not-<fn>
                                      badguy-not-ok-when-not-<fn>))))

  (local (in-theory (disable svarlist-overridekeys-envs-ok)))

  (defthm svarlist-overridekeys-envs-ok-of-subset
    (implies (and (svarlist-overridekeys-envs-ok y params overridekeys impl-env spec-env spec-outs)
                  (subsetp-equal (svarlist-fix x) (svarlist-fix y)))
             (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs))
    :hints (("goal" :use ((:instance svarlist-overridekeys-envs-ok-by-witness)
                          (:instance svarlist-overridekeys-envs-ok-implies
                           (x y)
                           (v (svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)))))))

  (local (in-theory (enable 4vec-muxtest-subsetp-when-svar-overridekeys-envs-ok-test
                            4vec-muxtest-subsetp-when-svar-overridekeys-envs-ok-val
                            4vec-override-mux-<<=-when-svar-overridekeys-envs-ok-test
                            4vec-override-mux-<<=-when-svar-overridekeys-envs-ok-val
                            4vec-bit?!-ok-when-svar-overridekeys-envs-ok-test
                            4vec-bit?!-ok-when-svar-overridekeys-envs-ok-val
                            nonoverride-params-ok-when-svar-overridekeys-envs-ok
                            nonoverride-vars-ok-when-svar-overridekeys-envs-ok)))
                            
  
  (defretd 4vec-muxtest-subsetp-when-<fn>-test
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup v spec-env)
                                   (svex-env-lookup v impl-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-muxtest-subsetp-when-<fn>-val
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override v :test) spec-env)
                                   (svex-env-lookup (svar-change-override v :test) impl-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-override-mux-<<=-when-<fn>-val
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (equal (svar-fix testvar) (svar-change-override v :test))
                  (equal (svar-fix refvar) (svar-change-override v nil))
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-override-mux-<<= (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup v impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup v spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-override-mux-<<=-when-<fn>-test
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (equal (svar-fix valvar) (svar-change-override v :val))
                  (equal (svar-fix refvar) (svar-change-override v nil))
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-override-mux-<<=  (svex-env-lookup v impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup v spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-bit?!-ok-when-<fn>-test
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (equal (svar-fix valvar) (svar-change-override v :val))
                  (equal refval (svex-env-lookup (svar-change-override v nil) spec-outs))
                  (svarlist-member-nonoverride v overridekeys))
             (equal (4vec-<<= (4vec-bit?! (svex-env-lookup v impl-env) (svex-env-lookup valvar impl-env) refval)
                              (4vec-bit?! (svex-env-lookup v spec-env) (svex-env-lookup valvar spec-env) refval))
                    t))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-bit?!-ok-when-<fn>-val
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (equal (svar-fix testvar) (svar-change-override v :test))
                  (equal refval (svex-env-lookup (svar-change-override v nil) spec-outs))
                  (svarlist-member-nonoverride v overridekeys))
             (equal (4vec-<<= (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup v impl-env) refval)
                              (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup v spec-env) refval))
                    t))
    :hints (("goal" :use <fn>-implies)))

  (defretd nonoverride-params-ok-when-<fn>
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (member-equal (svar-fix v) (svarlist-fix params))
                  (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys))))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd nonoverride-vars-ok-when-<fn>
    (implies (and ok
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys))))
             (4vec-<<= (svex-env-lookup v impl-env)
                       (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (local (in-theory (enable svarlist-overridekeys-envs-ok)))
  
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 5)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 6)
  (defcong set-equiv equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 1
    :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                      (acl2::element-list-final-cdr-p (lambda (x) t))
                                      (acl2::element-p (lambda (x) (svar-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)))
                                      (acl2::element-list-p (lambda (x) (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs))))
                           (x x) (y x-equiv)))
             :expand ((svarlist-overridekeys-envs-ok-badguy x params overridekeys impl-env spec-env spec-outs)))))
  (defcong set-equiv equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 2)
  (defcong set-equiv equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs) 3)

  (defthm svarlist-overridekeys-envs-ok-of-append
    (equal (svarlist-overridekeys-envs-ok (append x y) params overridekeys impl-env spec-env spec-outs)
           (and (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                (svarlist-overridekeys-envs-ok y params overridekeys impl-env spec-env spec-outs))))

  (defthmd svarlist-overridekeys-envs-ok-redef
    (equal (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
           (or (atom x)
               (and (svar-overridekeys-envs-ok (car x) params overridekeys impl-env spec-env spec-outs)
                    (svarlist-overridekeys-envs-ok (cdr x) params overridekeys impl-env spec-env spec-outs))))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok-badguy)))
    :rule-classes ((:definition :controller-alist ((svarlist-overridekeys-envs-ok t nil nil nil nil nil)))))

  (local (in-theory (enable svarlist-overridekeys-envs-ok))))

(local (defthm svarlist-p-of-alist-keys
         (implies (svex-env-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(define svarlist-overridekeys-env-keys ((x svarlist-p)
                                        (overridekeys svarlist-p))
  :returns (env-keys svarlist-p)
  (if (atom x)
      nil
    (append (svar-overridekeys-env-keys (car x) overridekeys)
            (svarlist-overridekeys-env-keys (cdr x) overridekeys)))
  ///
  (defretd svar-overridekeys-envs-ok-when-member-<fn>
    (implies (and (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                  (member-equal (svar-fix v) (svarlist-overridekeys-env-keys x overridekeys)))
             (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok-redef
                                      svar-overridekeys-envs-ok-when-member-svar-overridekeys-env-keys))))

  (defretd svar-overridekeys-envs-agree-when-member-<fn>
    (implies (and (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)
                  (member-equal (svar-fix v) (svarlist-overridekeys-env-keys x overridekeys)))
             (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree-redef
                                      svar-overridekeys-envs-agree-when-member-svar-overridekeys-env-keys))))


  (defretd svarlist-overridekeys-envs-ok-when-subsetp-<fn>
    (implies (and (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
                  (subsetp-equal (svarlist-fix v) (svarlist-overridekeys-env-keys x overridekeys)))
             (svarlist-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok-redef
                                      svarlist-fix
                                      svar-overridekeys-envs-ok-when-member-<fn>))))

  (defretd svarlist-overridekeys-envs-agree-when-subsetp-<fn>
    (implies (and (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)
                  (subsetp-equal (svarlist-fix v) (svarlist-overridekeys-env-keys x overridekeys)))
             (svarlist-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree-redef
                                      svarlist-fix
                                      svar-overridekeys-envs-agree-when-member-<fn>))))

  (defret subsetp-of-<fn>
    (subsetp-equal (svarlist-fix x) env-keys)
    :hints(("Goal" :in-theory (enable svarlist-fix))))

  (defthm svarlist-overridekeys-env-keys-of-append
    (equal (svarlist-overridekeys-env-keys (append x y) overridekeys)
           (append (svarlist-overridekeys-env-keys x overridekeys)
                   (svarlist-overridekeys-env-keys y overridekeys))))

  (defthm svarlist-overridekeys-env-keys-of-svar-overridekeys-env-keys
    (set-equiv (svarlist-overridekeys-env-keys (svar-overridekeys-env-keys v overridekeys) overridekeys)
               (svar-overridekeys-env-keys v overridekeys))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      acl2::set-unequal-witness-correct))))

  (defthm svarlist-overridekeys-env-keys-of-svarlist-overridekeys-env-keys
    (set-equiv (svarlist-overridekeys-env-keys (svarlist-overridekeys-env-keys v overridekeys) overridekeys)
               (svarlist-overridekeys-env-keys v overridekeys)))

  (defret member-<fn>-when-nonoverride
    (implies (or (svar-override-p v nil)
                 (and (not (svar-override-p v :test))
                      (not (svar-override-p v :val)))
                 (not (svarlist-member-nonoverride v overridekeys)))
             (iff (member-equal v env-keys)
                  (and (svar-p v)
                       (member-equal v (svarlist-fix x)))))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys))))

  (defret member-<fn>-when-test
    (implies (and (svar-override-p v :test)
                  (svarlist-member-nonoverride v overridekeys))
             (iff (member-equal v env-keys)
                  (and (svar-p v)
                       (or (member-equal v (svarlist-fix x))
                           (member-equal (svar-change-override v :val) (svarlist-fix x))))))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      equal-of-svar-change-override
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override))))

  (defret member-<fn>-when-val
    (implies (and (svar-override-p v :val)
                  (svarlist-member-nonoverride v overridekeys))
             (iff (member-equal v env-keys)
                  (and (svar-p v)
                       (or (member-equal v (svarlist-fix x))
                           (member-equal (svar-change-override v :test) (svarlist-fix x))))))
    :hints(("Goal" :in-theory (enable svar-overridekeys-env-keys
                                      equal-of-svar-change-override
                                      normalize-svar-change-override-when-equal-2
                                      normalize-svar-change-override-when-equal-1
                                      svar-equiv-when-equal-svar-change-override))))

  (defret member-of-<fn>-when-nonoverride
    (implies (or (svar-override-p v nil)
                 (and (not (svar-override-p v :test))
                      (not (svar-override-p v :val)))
                 (not (svarlist-member-nonoverride v overridekeys)))
             (iff (member-equal v env-keys) (member-equal v (svarlist-fix x))))
    :hints(("Goal" :in-theory (enable svarlist-fix)))))

(define svarlist-overridekeys-envs-ok-intermediate-env ((x svarlist-p)
                                                        (params svarlist-p)
                                                        (overridekeys svarlist-p)
                                                        (impl-env svex-env-p)
                                                        (spec-env svex-env-p)
                                                        (spec-outs svex-env-p))

  :returns (intermed-env svex-env-p)
  (if (atom x)
      (svex-env-fix impl-env)
    (append (svar-overridekeys-envs-ok-intermediate-env (car x) params overridekeys impl-env spec-env spec-outs)
            (svarlist-overridekeys-envs-ok-intermediate-env (cdr x) params overridekeys impl-env spec-env spec-outs)))
  ///
  
  (local (defthm svar-overridekeys-envs-ok-intermediate-env-preserves-svarlist-overridekeys-envs-agree
           (implies (and (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs)
                         (svarlist-overridekeys-envs-agree vars overridekeys rest spec-env spec-outs))
                    (svarlist-overridekeys-envs-agree vars overridekeys
                                                      (append (svar-overridekeys-envs-ok-intermediate-env v params overridekeys impl-env spec-env spec-outs)
                                                              rest)
                                                      spec-env spec-outs))
           :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree-redef)
                   :induct (len vars)))))
  
  (defret <fn>-svarlist-overridekeys-envs-agree
    (implies (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
             (svarlist-overridekeys-envs-agree x overridekeys intermed-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree-redef
                                      svarlist-overridekeys-envs-ok-redef))))

  (defret <fn>-svex-env-<<=
    (implies (svarlist-overridekeys-envs-ok x params overridekeys impl-env spec-env spec-outs)
             (svex-env-<<= impl-env intermed-env))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-ok-redef))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys intermed-env)
           (append (svarlist-overridekeys-env-keys x overridekeys)
                   (alist-keys (svex-env-fix impl-env))))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-env-keys))))

  

  (defretd lookup-param-of-<fn>
    (implies (and (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys)))
                  (member-equal (svar-fix v) (svarlist-fix params)))
             (equal (svex-env-lookup v intermed-env)
                    (svex-env-lookup v impl-env)))
    :hints(("Goal" :in-theory (enable lookup-param-of-svar-overridekeys-envs-ok-intermediate-env
                                      svex-env-boundp-iff-member-alist-keys
                                      svarlist-fix))))

  (defretd lookup-test-of-<fn>
    (implies (and (svar-override-p v :test)
                  (svarlist-member-nonoverride v overridekeys))
             (equal (svex-env-lookup v intermed-env)
                    (svex-env-lookup v impl-env)))
    :hints(("Goal" :in-theory (enable lookup-test-of-svar-overridekeys-envs-ok-intermediate-env
                                      svex-env-boundp-iff-member-alist-keys
                                      svarlist-fix))))

  (local (defthm member-change-override-change-override-when-val
           (implies (svar-override-p v :val)
                    (iff (member-equal (svar-change-override v nil)
                                       (svarlist-change-override x nil))
                         (member-equal (svar-fix v) (svarlist-change-override x :val))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override
                                             normalize-svar-change-override-when-equal-1
                                             normalize-svar-change-override-when-equal-2
                                             svar-equiv-when-equal-svar-change-override)))))
  
  (defret extract-params-of-<fn>
    (implies (and (not (intersectp-equal (svarlist-fix params)
                                         (svarlist-change-override overridekeys :val)))
                  (subsetp-equal (svarlist-fix pars) (svarlist-fix params)))
             (equal (svex-env-extract pars intermed-env)
                    (svex-env-extract pars impl-env)))
    :hints(("Goal" :in-theory (e/d (svarlist-fix
                                    svex-env-extract) (<fn>))
            :induct (len pars))
           (and stable-under-simplificationp
                '(:use ((:instance lookup-param-of-<fn>
                         (v (car pars)))
                        (:instance lookup-test-of-<fn>
                         (v (car pars))))
                  :do-not-induct t)))))



(define overridekeys-envs-ok ((params svarlist-p)
                              (overridekeys svarlist-p)
                              (impl-env svex-env-p)
                              (spec-env svex-env-p)
                              (spec-outs svex-env-p))
  :returns (agree)
  (svarlist-overridekeys-envs-ok
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   params overridekeys impl-env spec-env spec-outs)
  ///
  (defret <fn>-implies
    (implies agree
             (svar-overridekeys-envs-ok v params overridekeys impl-env spec-env spec-outs))
    :hints (("goal" :use ((:instance svarlist-overridekeys-envs-ok-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env)))))
                          (:instance svarlist-overridekeys-envs-ok-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :test)))
                          (:instance svarlist-overridekeys-envs-ok-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :val))))
             :in-theory (enable svar-overridekeys-envs-ok
                                svex-env-lookup-when-not-boundp
                                svex-env-boundp-iff-member-alist-keys))))

  (defret <fn>-implies-svarlist-overridekeys-envs-ok
    (implies agree
             (svarlist-overridekeys-envs-ok vars params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (e/d (svarlist-overridekeys-envs-ok
                                    svarlist-overridekeys-envs-ok-badguy)
                                   (<fn>)))))


  (local (in-theory (enable 4vec-muxtest-subsetp-when-svar-overridekeys-envs-ok-test
                            4vec-override-mux-<<=-when-svar-overridekeys-envs-ok-test
                            4vec-override-mux-<<=-when-svar-overridekeys-envs-ok-val
                            4vec-bit?!-ok-when-svar-overridekeys-envs-ok-test
                            4vec-bit?!-ok-when-svar-overridekeys-envs-ok-val
                            nonoverride-params-ok-when-svar-overridekeys-envs-ok
                            nonoverride-vars-ok-when-svar-overridekeys-envs-ok)))
                            
  (local (in-theory (disable overridekeys-envs-ok overridekeys-envs-ok-implies)))
  (defretd 4vec-muxtest-subsetp-when-<fn>
    (implies (and agree
                  (svar-override-p x :test)
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup x spec-env)
                                   (svex-env-lookup x impl-env)))
    :hints (("goal" :use ((:instance <fn>-implies
                           (v x))))))

  (defretd 4vec-override-mux-<<=-when-<fn>
    (implies (and agree
                  (svar-override-p testvar :test)
                  (svar-override-p valvar :val)
                  (svar-override-p refvar nil)
                  (equal (svar-change-override testvar nil) (svar-fix refvar))
                  (equal (svar-change-override valvar nil) (svar-fix refvar))
                  (svarlist-member-nonoverride refvar overridekeys))
             (4vec-override-mux-<<= (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use ((:instance <fn>-implies (v testvar)))
             :in-theory (enable equal-of-svar-change-override))))

  (defretd 4vec-bit?!-ok-when-<fn>
    (implies (and agree
                  (svar-override-p testvar :test)
                  (equal (svar-fix valvar) (svar-change-override testvar :val))
                  (equal refval (svex-env-lookup (svar-change-override testvar nil) spec-outs))
                  (svarlist-member-nonoverride testvar overridekeys))
             (equal (4vec-<<= (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup valvar impl-env) refval)
                           (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup valvar spec-env) refval))
                    t))
    :hints (("goal" :use ((:instance <fn>-implies (v testvar))))))

  (defretd nonoverride-params-ok-when-<fn>
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix params))
                  (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys))))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd nonoverride-vars-ok-when-<fn>
    (implies (and agree
                  (or (svar-override-p v nil)
                      (and (not (svar-override-p v :test))
                           (not (svar-override-p v :val)))
                      (not (svarlist-member-nonoverride v overridekeys))))
             (4vec-<<= (svex-env-lookup v impl-env)
                       (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies))))


(define overridekeys-envs-ok-badguy ((params svarlist-p)
                                     (overridekeys svarlist-p)
                                        (impl-env svex-env-p)
                                        (spec-env svex-env-p)
                                        (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (svarlist-overridekeys-envs-ok-badguy
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   params overridekeys impl-env spec-env spec-outs)
  ///
  

  (defretd badguy-not-ok-when-not-overridekeys-envs-ok
    (implies (not (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs))
             (not (svar-overridekeys-envs-ok
                   badguy
                   params overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (e/d (badguy-not-ok-when-not-svarlist-overridekeys-envs-ok
                                    overridekeys-envs-ok)
                                   (SVARLIST-OVERRIDEKEYS-ENVS-OK-BADGUY-OF-APPEND
                                    SVARLIST-OVERRIDEKEYS-ENVS-OK-OF-APPEND))))))

(defsection overridekeys-envs-ok-more
  ;; :extension overridekeys-envs-ok
  (local (std::set-define-current-function overridekeys-envs-ok))

  (defthmd overridekeys-envs-ok-by-witness
    (equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)
           (svar-overridekeys-envs-ok
            (overridekeys-envs-ok-badguy params overridekeys impl-env spec-env spec-outs) params overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (e/d (badguy-not-ok-when-not-overridekeys-envs-ok
                                    overridekeys-envs-ok-implies)
                                   (overridekeys-envs-ok-badguy))
            :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs))))
    :rule-classes :definition)

  (local (in-theory (disable overridekeys-envs-ok-implies)))
  
  (defcong svex-envs-similar equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs) 3
    :hints (("goal" :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-ok clause))
                      (other-arg (if (eq (nth 3 lit) 'impl-env) 'impl-env-equiv 'impl-env)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-ok-implies
                            (impl-env ,other-arg)
                            (v (overridekeys-envs-ok-badguy . ,(cdr lit))))))))))
  (defcong svex-envs-similar equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs) 4
    :hints (("goal" :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-ok clause))
                      (other-arg (if (eq (nth 4 lit) 'spec-env) 'spec-env-equiv 'spec-env)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-ok-implies
                            (spec-env ,other-arg)
                            (v (overridekeys-envs-ok-badguy . ,(cdr lit))))))))))
  (defcong svex-envs-similar equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs) 5
    :hints (("goal" :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-ok clause))
                      (other-arg (if (eq (nth 5 lit) 'spec-outs) 'spec-outs-equiv 'spec-outs)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-ok-implies
                            (spec-outs ,other-arg)
                            (v (overridekeys-envs-ok-badguy . ,(cdr lit))))))))))
  (defcong set-equiv equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs) 1
    :hints (("goal" :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-ok clause))
                      (other-arg (if (eq (nth 1 lit) 'params) 'params-equiv 'params)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-ok-implies
                            (params ,other-arg)
                            (v (overridekeys-envs-ok-badguy . ,(cdr lit))))))))))
  (defcong set-equiv equal (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs) 2
    :hints (("goal" :cases ((overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-ok clause))
                      (other-arg (if (eq (nth 2 lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-ok-implies
                            (overridekeys ,other-arg)
                            (v (overridekeys-envs-ok-badguy . ,(cdr lit)))))))))))

(define overridekeys-envs-ok-intermediate-env ((params svarlist-p)
                                               (overridekeys svarlist-p)
                                               (impl-env svex-env-p)
                                               (spec-env svex-env-p)
                                               (spec-outs svex-env-p))
  :returns (intermed-env svex-env-p)
  (svarlist-overridekeys-envs-ok-intermediate-env
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   params overridekeys impl-env spec-env spec-outs)
  ///

                    
  (local (in-theory (disable acl2::alist-keys-member-hons-assoc-equal)))

  (local (defthm svar-overridekeys-envs-agree-when-not-member-env-keys
           (implies (not (member-equal (svar-fix v)
                                       (svarlist-overridekeys-env-keys
                                        (append (alist-keys (svex-env-fix impl-env))
                                                (alist-keys (svex-env-fix spec-env)))
                                        overridekeys)))
                    (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
           :hints (("goal" :cases ((svar-override-p x :test)
                                   (svar-override-p x :val))
                    :in-theory (enable svar-overridekeys-envs-agree
                                       svar-override-p-when-other
                                       svex-env-lookup-when-not-boundp
                                       svex-env-boundp-iff-member-alist-keys))
                   (and stable-under-simplificationp
                        '(:cases ((svarlist-member-nonoverride v overridekeys)))))))
                           
  (local (defthm svarlist-overridekeys-env-keys-lemma
           (set-equiv (SVARLIST-OVERRIDEKEYS-ENV-KEYS
                       (APPEND (SVARLIST-OVERRIDEKEYS-ENV-KEYS
                                (APPEND (ALIST-KEYS (SVEX-ENV-FIX IMPL-ENV))
                                        (ALIST-KEYS (SVEX-ENV-FIX SPEC-ENV)))
                                OVERRIDEKEYS)
                               (ALIST-KEYS (SVEX-ENV-FIX IMPL-ENV))
                               (ALIST-KEYS (SVEX-ENV-FIX SPEC-ENV)))
                       OVERRIDEKEYS)
                      (SVARLIST-OVERRIDEKEYS-ENV-KEYS
                       (APPEND (ALIST-KEYS (SVEX-ENV-FIX IMPL-ENV))
                               (ALIST-KEYS (SVEX-ENV-FIX SPEC-ENV)))
                       OVERRIDEKEYS))))
  
  (defret <fn>-overridekeys-envs-agree
    (implies (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)
             (overridekeys-envs-agree overridekeys intermed-env spec-env spec-outs))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause))))
                   `(:expand (,lit)
                     :use ((:instance svar-overridekeys-envs-agree-when-member-svarlist-overridekeys-env-keys
                            (x (append (alist-keys (svex-env-fix impl-env))
                                       (alist-keys (Svex-env-fix spec-env))))
                            (v (overridekeys-envs-agree-badguy . ,(cdr lit)))
                            (impl-env ,(nth 2 lit))))
                     :in-theory (e/d (svex-env-lookup-when-not-boundp
                                      svex-env-boundp-iff-member-alist-keys)
                                     (svarlist-overridekeys-envs-agree-implies
                                      svarlist-overridekeys-env-keys-of-append))
                     :do-not-induct t)))))

  (defret <fn>-svex-env-<<=
    (implies (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)
             (svex-env-<<= impl-env intermed-env))
    :hints(("Goal" :in-theory (e/d (overridekeys-envs-ok)
                                   (svarlist-overridekeys-envs-ok-of-append)))))

  (defret extract-params-of-<fn>
    (implies (and (not (intersectp-equal (svarlist-fix params)
                                         (svarlist-change-override overridekeys :val)))
                  (subsetp-equal (svarlist-fix pars) (svarlist-fix params)))
             (equal (svex-env-extract pars intermed-env)
                    (svex-env-extract pars impl-env)))))


(defthm svex-eval-when-overridekeys-envs-ok/transparent/partial-monotonic
  (implies (and (overridekeys-envs-ok params overridekeys impl-env spec-env
                                      (svex-alist-eval subst spec-env))
                (svex-overridekey-transparent-p x overridekeys subst)
                (svex-partial-monotonic params x)
                (not (intersectp-equal (svarlist-fix params)
                                       (svarlist-change-override overridekeys :val))))
           (4vec-<<= (svex-eval x impl-env)
                     (svex-eval x spec-env)))
  :hints (("goal" :use ((:instance svex-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-ok-intermediate-env
                                    params overridekeys impl-env spec-env
                                    (svex-alist-eval subst spec-env)))
                         (spec-env spec-env))
                        (:instance overridekeys-envs-ok-intermediate-env-svex-env-<<=
                         (spec-outs (svex-alist-eval subst spec-env)))
                        (:instance eval-when-svex-partial-monotonic
                         (param-keys params)
                         (env1 impl-env)
                         (env2 (overridekeys-envs-ok-intermediate-env
                                params overridekeys impl-env spec-env
                                (svex-alist-eval subst spec-env)))))
           :in-theory (disable overridekeys-envs-ok-intermediate-env-svex-env-<<=
                               eval-when-svex-partial-monotonic))))



(defthm svexlist-eval-when-overridekeys-envs-ok/transparent/partial-monotonic
  (implies (and (overridekeys-envs-ok params overridekeys impl-env spec-env
                                      (svex-alist-eval subst spec-env))
                (svexlist-overridekey-transparent-p x overridekeys subst)
                (svexlist-partial-monotonic params x)
                (not (intersectp-equal (svarlist-fix params)
                                       (svarlist-change-override overridekeys :val))))
           (4veclist-<<= (svexlist-eval x impl-env)
                         (svexlist-eval x spec-env)))
  :hints (("goal" :use ((:instance svexlist-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-ok-intermediate-env
                                    params overridekeys impl-env spec-env
                                    (svex-alist-eval subst spec-env)))
                         (spec-env spec-env))
                        (:instance overridekeys-envs-ok-intermediate-env-svex-env-<<=
                         (spec-outs (svex-alist-eval subst spec-env)))
                        (:instance eval-when-svexlist-partial-monotonic
                         (param-keys params)
                         (env1 impl-env)
                         (env2 (overridekeys-envs-ok-intermediate-env
                                    params overridekeys impl-env spec-env
                                    (svex-alist-eval subst spec-env)))))
           :in-theory (disable overridekeys-envs-ok-intermediate-env-svex-env-<<=
                               eval-when-svexlist-partial-monotonic))))


(defthm svex-alist-eval-when-overridekeys-envs-ok/transparent/partial-monotonic
  (implies (and (overridekeys-envs-ok params overridekeys impl-env spec-env
                                      (svex-alist-eval subst spec-env))
                (svex-alist-overridekey-transparent-p x overridekeys subst)
                (svex-alist-partial-monotonic params x)
                (not (intersectp-equal (svarlist-fix params)
                                       (svarlist-change-override overridekeys :val))))
           (svex-env-<<= (svex-alist-eval x impl-env)
                         (svex-alist-eval x spec-env)))
  :hints (("goal" :use ((:instance svex-alist-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-ok-intermediate-env
                                    params overridekeys impl-env spec-env
                                    (svex-alist-eval subst spec-env)))
                         (spec-env spec-env))
                        (:instance overridekeys-envs-ok-intermediate-env-svex-env-<<=
                         (spec-outs (svex-alist-eval subst spec-env)))
                        (:instance eval-when-svex-alist-partial-monotonic
                         (param-keys params)
                         (env1 impl-env)
                         (env2 (overridekeys-envs-ok-intermediate-env
                                    params overridekeys impl-env spec-env
                                    (svex-alist-eval subst spec-env)))))
           :in-theory (disable overridekeys-envs-ok-intermediate-env-svex-env-<<=
                               eval-when-svex-alist-partial-monotonic))))
