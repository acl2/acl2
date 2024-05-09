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
(include-book "ovmonotonicity")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "alist-thms"))

(local (std::add-default-post-define-hook :fix))



(define svar-overridekeys-envs-agree* ((x svar-p)
                                       (overridekeys svarlist-p)
                                       (impl-env svex-env-p)
                                       (spec-env svex-env-p)
                                       (spec-outs svex-env-p))
  :returns (agree)
  (cond ((or (svar-override-p x :test)
             (svar-override-p x :val))
         (if (svarlist-member-nonoverride x overridekeys)
             (and (4vec-override-mux-agrees (svex-env-lookup (svar-change-override x :test) impl-env)
                                            (svex-env-lookup (svar-change-override x :val) impl-env)
                                            (svex-env-lookup (svar-change-override x :test) spec-env)
                                            (svex-env-lookup (svar-change-override x :val) spec-env)
                                            (svex-env-lookup (svar-change-override x nil) spec-outs))
                  (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override x :test) spec-env)
                                        (svex-env-lookup (svar-change-override x :test) impl-env)))
           (and (4vec-1mask-equiv (svex-env-lookup (svar-change-override x :test) impl-env)
                                  (svex-env-lookup (svar-change-override x :test) spec-env))
                (equal (4vec-bit?! (svex-env-lookup (svar-change-override x :test) impl-env)
                                   (svex-env-lookup (svar-change-override x :val) impl-env)
                                   0)
                       (4vec-bit?! (svex-env-lookup (svar-change-override x :test) spec-env)
                                   (svex-env-lookup (svar-change-override x :val) spec-env)
                                   0)))))
        (t (equal (svex-env-lookup x impl-env)
                  (svex-env-lookup x spec-env))))
  ///
  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree* x overridekeys impl-env spec-env spec-outs) 3)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree* x overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree* x overridekeys impl-env spec-env spec-outs) 5)
  
  (defcong set-equiv equal (svar-overridekeys-envs-agree* x overridekeys impl-env spec-env spec-outs) 2))

(define svarlist-overridekeys-envs-agree*-badguy ((x svarlist-p)
                                                 (overridekeys svarlist-p)
                                                 (impl-env svex-env-p)
                                                 (spec-env svex-env-p)
                                                 (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (if (atom x)
      nil
    (if (svar-overridekeys-envs-agree* (car x) overridekeys impl-env spec-env spec-outs)
        (svarlist-overridekeys-envs-agree*-badguy (cdr x) overridekeys impl-env spec-env spec-outs)
      (svar-fix (car x))))
  ///
  (defretd <fn>-when-witness
    (implies (and (not (svar-overridekeys-envs-agree* v overridekeys impl-env spec-env spec-outs))
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-fix))))

  (defretd not-svar-overridekeys-envs-agree*-of-<fn>
    (implies badguy
             (not (svar-overridekeys-envs-agree* badguy overridekeys impl-env spec-env spec-outs))))

  (defretd member-of-<fn>
    (implies badguy
             (member-equal badguy (svarlist-fix x)))))  

(define svarlist-overridekeys-envs-agree* ((x svarlist-p)
                                          (overridekeys svarlist-p)
                                          (impl-env svex-env-p)
                                          (spec-env svex-env-p)
                                          (spec-outs svex-env-p))
  :returns (agree*)
  :hooks ((:fix :hints nil))
  (not (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs))
  ///
  (defretd <fn>-implies
    (implies (and agree*
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svar-overridekeys-envs-agree* v overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree*
                                      svarlist-overridekeys-envs-agree*-badguy-when-witness))))

  (defretd badguy-not-agree*-when-not-<fn>
    (implies (not agree*)
             (not (svar-overridekeys-envs-agree*
                   (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs)
                   overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree*
                                      not-svar-overridekeys-envs-agree*-of-svarlist-overridekeys-envs-agree*-badguy))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not agree*)
             (member-equal
              (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree*
                                      member-of-svarlist-overridekeys-envs-agree*-badguy))))

  (defretd badguy-member-when-not-<fn>
    (implies (and (not agree*)
                  (svarlist-p x))
             (member-equal
              (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs)
              x))
    :hints(("Goal" :use ((:instance badguy-member-fix-when-not-<fn>)))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not agree*)
             (member-equal
              (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree*
                                      member-of-svarlist-overridekeys-envs-agree*-badguy))))

  (defretd <fn>-by-witness
    (implies (not agree*)
             (b* ((badguy (svarlist-overridekeys-envs-agree*-badguy x overridekeys impl-env spec-env spec-outs)))
               (and (svar-p badguy)
                    (member-equal badguy (svarlist-fix x))
                    (not (svar-overridekeys-envs-agree* badguy overridekeys impl-env spec-env spec-outs)))))
    :hints(("Goal" :in-theory (enable badguy-member-fix-when-not-<fn>
                                      badguy-not-agree*-when-not-<fn>)))))


(define overridekeys-envs-agree* ((overridekeys svarlist-p)
                                 (impl-env svex-env-p)
                                 (spec-env svex-env-p)
                                 (spec-outs svex-env-p))
  :returns (agree*)
  (svarlist-overridekeys-envs-agree*
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   overridekeys impl-env spec-env spec-outs)
  ///
  
  (defret <fn>-implies
    (implies agree*
             (svar-overridekeys-envs-agree* v overridekeys impl-env spec-env spec-outs))
    :hints (("goal" :use ((:instance svarlist-overridekeys-envs-agree*-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env)))))
                          (:instance svarlist-overridekeys-envs-agree*-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :test)))
                          (:instance svarlist-overridekeys-envs-agree*-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :val))))
             :in-theory (enable svar-overridekeys-envs-agree*
                                svex-env-lookup-when-not-boundp
                                svex-env-boundp-iff-member-alist-keys)))))

(define overridekeys-envs-agree*-badguy ((overridekeys svarlist-p)
                                        (impl-env svex-env-p)
                                        (spec-env svex-env-p)
                                        (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (svarlist-overridekeys-envs-agree*-badguy
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   overridekeys impl-env spec-env spec-outs)
  ///
  

  (defretd badguy-not-agree*-when-not-overridekeys-envs-agree*
    (implies (not (overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs))
             (not (svar-overridekeys-envs-agree*
                   badguy
                   overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (e/d (badguy-not-agree*-when-not-svarlist-overridekeys-envs-agree*
                                    overridekeys-envs-agree*)))))

  (defthmd overridekeys-envs-agree*-by-witness
    (equal (overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs)
           (svar-overridekeys-envs-agree*
            (overridekeys-envs-agree*-badguy overridekeys impl-env spec-env spec-outs) overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (e/d (badguy-not-agree*-when-not-overridekeys-envs-agree*
                                    overridekeys-envs-agree*-implies)
                                   (overridekeys-envs-agree*-badguy))
            :cases ((overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs))))
    :rule-classes :definition))


;; Want to show that if an svex(/list/-alist) satisfies *-overridekey-transparent-p and *-ovcongruent,
;; then its evaluation is equal under overridekeys-envs-agree*.

;; To do this, given envs satisfying overridekeys-envs-agree*, we need an
;; intermediate env that is overridekeys-envs-agree with the spec and ovsimilar
;; with the impl, or vice versa.

(local
 (define overridekeys-envs-agree*-intermed-env ((overridekeys svarlist-p)
                                                (impl-env svex-env-p)
                                                (spec-env svex-env-p))
   :returns (intermed svex-env-p)
   (append (svex-env-extract (append
                              (hons-set-diff (svarlist-filter-override (append (alist-keys (svex-env-fix impl-env))
                                                                              (alist-keys (svex-env-fix spec-env)))
                                                                      :test)
                                             (svarlist-change-override overridekeys :test))
                              (hons-set-diff (svarlist-filter-override (append (alist-keys (svex-env-fix impl-env))
                                                                              (alist-keys (svex-env-fix spec-env)))
                                                                      :val)
                                            (svarlist-change-override overridekeys :val)))
                             
                             spec-env)
           (svex-env-fix impl-env))
   ///
  
   (local (Defthm member-of-svarlist-change-override-rw
            (implies (syntaxp (not (equal type ''nil)))
                     (iff (member-equal v (svarlist-change-override x type))
                          (and (svar-p v)
                               (svar-override-p v type)
                               (svarlist-member-nonoverride v x))))
            :hints(("Goal" :in-theory (enable svarlist-change-override
                                              equal-of-svar-change-override)))))
  
   (defret <fn>-ovsimilar-to-impl-env
     (implies (overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs)
              (svex-envs-ovsimilar intermed impl-env))
     :hints ((and stable-under-simplificationp
                  (let* ((lit (car (last clause)))
                         (witness `(svex-envs-ovsimilar-witness . ,(cdr lit))))
                    `(:computed-hint-replacement
                      ((and stable-under-simplificationp
                            '(:computed-hint-replacement
                              ('(:use ((:instance overridekeys-envs-agree*-implies
                                        (v key)))
                                 :in-theory (e/d (svar-overridekeys-envs-agree*)
                                                 (overridekeys-envs-agree*-implies))))
                              :clause-processor (acl2::generalize-with-alist-cp clause '((,witness . key))))))
                      :expand (,lit))))))

   (defret <fn>-overridekeys-envs-agree
     (implies (overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs)
              (overridekeys-envs-agree overridekeys intermed spec-env spec-outs))
     :hints ((and stable-under-simplificationp
                  (let* ((lit (car (last clause)))
                         (witness `(overridekeys-envs-agree-badguy . ,(cdr lit))))
                    `(:computed-hint-replacement
                      ((and stable-under-simplificationp
                            '(:computed-hint-replacement
                              ('(
                                 :use ((:instance overridekeys-envs-agree*-implies
                                        (v key)))
                                 :in-theory (e/d (svar-overridekeys-envs-agree*
                                                  svar-overridekeys-envs-agree
                                                  svex-env-lookup-when-not-boundp
                                                  svex-env-boundp-iff-member-alist-keys)
                                                 (overridekeys-envs-agree*-implies))))
                              :clause-processor (acl2::generalize-with-alist-cp clause '((,witness . key))))))
                      :expand (,lit)))))
     :otf-flg t)))


(defthmd svex-eval-when-overridekeys-envs-agree*
  (implies (and (overridekeys-envs-agree* overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                (svex-ovcongruent x)
                (svex-overridekey-transparent-p x overridekeys subst))
           (equal (svex-eval x impl-env)
                  (svex-eval x spec-env)))
  :hints (("goal" :use ((:instance svex-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))
                        (:instance svex-ovcongruent-necc
                         (env1 impl-env)
                         (env2 (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))))))


(defthmd svexlist-eval-when-overridekeys-envs-agree*
  (implies (and (overridekeys-envs-agree* overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                (svexlist-ovcongruent x)
                (svexlist-overridekey-transparent-p x overridekeys subst))
           (equal (svexlist-eval x impl-env)
                  (svexlist-eval x spec-env)))
  :hints (("goal" :use ((:instance svexlist-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))
                        (:instance svexlist-ovcongruent-necc
                         (env1 impl-env)
                         (env2 (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))))))


(defthmd svex-alist-eval-when-overridekeys-envs-agree*
  (implies (and (overridekeys-envs-agree* overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                (svex-alist-ovcongruent x)
                (svex-alist-overridekey-transparent-p x overridekeys subst))
           (svex-envs-equivalent (svex-alist-eval x impl-env)
                                 (svex-alist-eval x spec-env)))
  :hints (("goal" :use ((:instance svex-alist-overridekey-transparent-p-necc
                         (impl-env (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))
                        (:instance svex-alist-ovcongruent-necc
                         (env1 impl-env)
                         (env2 (overridekeys-envs-agree*-intermed-env overridekeys impl-env spec-env)))))))

