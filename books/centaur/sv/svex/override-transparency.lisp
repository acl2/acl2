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


(include-book "override-mux")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (defthm equal-of-ash-same
         (implies (natp n)
                  (equal (equal (ash x n) (ash y n))
                         (equal (ifix x) (ifix y))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                           bitops::ihsext-recursive-redefs)))))

(define svar-equiv-nonoverride ((x svar-p) (y svar-p))
  :guard-hints (("goal" :in-theory (enable svar-change-override)))
  (mbe :logic
       (equal (svar-change-override x nil) (svar-change-override y nil))
       :exec
       (b* (((svar x)) ((svar y)))
         (and (equal x.name y.name)
              (eql x.delay y.delay)
              (equal x.props y.props)
              (eql (logtail 3 x.bits)
                   (logtail 3 y.bits))))))



(define overridekeys->override-vars ((x svarlist-p))
  :returns (override-vars svarlist-p)
  (if (atom x)
      nil
    (cons (svar-change-override (car x) :test)
          (cons (svar-change-override (car x) :val)
                (overridekeys->override-vars (cdr x)))))
  ///
  (defthmd overridekeys->override-vars-under-set-equiv
    (set-equiv (overridekeys->override-vars x)
               (append (svarlist-change-override x :test)
                       (svarlist-change-override x :val)))
    :hints(("Goal" :in-theory (enable svarlist-change-override))))

  (defret svarlist-override-okp-of-<fn>
    (svarlist-override-okp override-vars)
    :hints(("Goal" :in-theory (enable svarlist-override-okp)))))


(define svarlist-member-nonoverride ((x svar-p)
                                     (lst svarlist-p))
  :guard-hints (("goal" :in-theory (enable svar-equiv-nonoverride
                                           svarlist-change-override)
                 :expand ((svarlist-member-nonoverride x (cdr lst)))))
  :enabled t
  (mbe :logic (and (member-equal (svar-change-override x nil)
                                 (svarlist-change-override lst nil))
                   t)
       :exec (if (atom lst)
                 nil
               (or (svar-equiv-nonoverride x (car lst))
                   (svarlist-member-nonoverride x (cdr lst)))))
  ///
  (defcong set-equiv set-equiv (svarlist-change-override x type) 1
    :hints (("goal" :use ((:instance (:functional-instance acl2::set-equiv-congruence-over-elementlist-projection
                                      (acl2::elementlist-projection (lambda (x) (svarlist-change-override x type)))
                                      (acl2::element-xformer (lambda (x) (svar-change-override x type)))
                                      (acl2::element-p (lambda (x) t))
                                      (acl2::outelement-p (lambda (x) t)))
                           (x x) (y x-equiv)))
             :expand ((svarlist-change-override x type)))))
  (defcong set-equiv equal (svarlist-member-nonoverride x lst) 2))



(define svar-overridekeys-envs-agree ((x svar-p)
                                      (overridekeys svarlist-p)
                                      (impl-env svex-env-p)
                                      (spec-env svex-env-p)
                                      (spec-outs svex-env-p))
  :returns (agree)
  (cond ((and (or (svar-override-p x :test)
                  (svar-override-p x :val))
              (svarlist-member-nonoverride x overridekeys))
         (and (4vec-override-mux-agrees (svex-env-lookup (svar-change-override x :test) impl-env)
                                        (svex-env-lookup (svar-change-override x :val) impl-env)
                                        (svex-env-lookup (svar-change-override x :test) spec-env)
                                        (svex-env-lookup (svar-change-override x :val) spec-env)
                                        (svex-env-lookup (svar-change-override x nil) spec-outs))
              (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override x :test) spec-env)
                                    (svex-env-lookup (svar-change-override x :test) impl-env))))
        ;; ((and (svar-override-p x :val)
        ;;       (svarlist-member-nonoverride x overridekeys))
        ;;  )
        (t (equal (svex-env-lookup x impl-env)
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

  (defretd 4vec-override-mux-agrees-when-<fn>-val
    (implies (and agree
                  (svar-override-p x :val)
                  (equal (svar-fix testvar) (svar-change-override x :test))
                  (equal (svar-fix refvar) (svar-change-override x nil))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-override-mux-agrees (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup x impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup x spec-env)
                                   (svex-env-lookup refvar spec-outs))))

  (defretd 4vec-override-mux-agrees-when-<fn>-test
    (implies (and agree
                  (svar-override-p x :test)
                  (equal (svar-fix valvar) (svar-change-override x :val))
                  (equal (svar-fix refvar) (svar-change-override x nil))
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-override-mux-agrees (svex-env-lookup x impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup x spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs))))

  (defretd 4vec-bit?!-agree-when-<fn>-test
    (implies (and agree
                  (svar-override-p x :test)
                  (equal (svar-fix valvar) (svar-change-override x :val))
                  (equal refval (svex-env-lookup (svar-change-override x nil) spec-outs))
                  (svarlist-member-nonoverride x overridekeys))
             (equal (equal (4vec-bit?! (svex-env-lookup x impl-env) (svex-env-lookup valvar impl-env) refval)
                           (4vec-bit?! (svex-env-lookup x spec-env) (svex-env-lookup valvar spec-env) refval))
                    t)))

  (defretd 4vec-bit?!-agree-when-<fn>-val
    (implies (and agree
                  (svar-override-p x :val)
                  (equal (svar-fix testvar) (svar-change-override x :test))
                  (equal refval (svex-env-lookup (svar-change-override x nil) spec-outs))
                  (svarlist-member-nonoverride x overridekeys))
             (equal (equal (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup x impl-env) refval)
                           (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup x spec-env) refval))
                    t)))

  (defretd nonoverride-vars-agree-when-<fn>
    (implies (and agree
                  (svar-override-p x nil))
             (equal (svex-env-lookup x impl-env)
                    (svex-env-lookup x spec-env))))

  (defretd non-overridekeys-agree-when-<fn>
    (implies (and agree
                  (not (svarlist-member-nonoverride x overridekeys)))
             (equal (svex-env-lookup x impl-env)
                    (svex-env-lookup x spec-env))))

  (defretd neither-override-vars-agree-when-<fn>
    (implies (and agree
                  (not (svar-override-p x :test))
                  (not (svar-override-p x :val)))
             (equal (svex-env-lookup x impl-env)
                    (svex-env-lookup x spec-env))))

  (defret <fn>-of-svarlist-change-override
    (equal (let ((overridekeys (svarlist-change-override overridekeys type))) <call>)
           agree))
  

  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 3)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 5)

  (defcong set-equiv equal (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 2))



(define svarlist-overridekeys-envs-agree-badguy ((x svarlist-p)
                                                 (overridekeys svarlist-p)
                                                 (impl-env svex-env-p)
                                                 (spec-env svex-env-p)
                                                 (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (if (atom x)
      nil
    (if (svar-overridekeys-envs-agree (car x) overridekeys impl-env spec-env spec-outs)
        (svarlist-overridekeys-envs-agree-badguy (cdr x) overridekeys impl-env spec-env spec-outs)
      (svar-fix (car x))))
  ///
  (defretd <fn>-when-witness
    (implies (and (not (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-fix))))

  (defretd not-svar-overridekeys-envs-agree-of-<fn>
    (implies badguy
             (not (svar-overridekeys-envs-agree badguy overridekeys impl-env spec-env spec-outs))))

  (defretd member-of-<fn>
    (implies badguy
             (member-equal badguy (svarlist-fix x))))

  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs) 3)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs) 5)

  (defcong set-equiv equal (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs) 2)

  (defthm svarlist-overridekeys-envs-agree-badguy-of-append
    (equal (svarlist-overridekeys-envs-agree-badguy (append x y) overridekeys impl-env spec-env spec-outs)
           (or (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)
               (svarlist-overridekeys-envs-agree-badguy y overridekeys impl-env spec-env spec-outs))))

  (defret <fn>-of-svarlist-change-override
    (iff (let ((overridekeys (svarlist-change-override overridekeys type))) <call>)
         badguy)))

(define svarlist-overridekeys-envs-agree ((x svarlist-p)
                                          (overridekeys svarlist-p)
                                          (impl-env svex-env-p)
                                          (spec-env svex-env-p)
                                          (spec-outs svex-env-p))
  :returns (agree)
  :hooks ((:fix :hints nil))
  (not (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs))
  ///
  (defretd <fn>-implies
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x)))
             (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree
                                      svarlist-overridekeys-envs-agree-badguy-when-witness))))

  (defretd badguy-not-agree-when-not-<fn>
    (implies (not agree)
             (not (svar-overridekeys-envs-agree
                   (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)
                   overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree
                                      not-svar-overridekeys-envs-agree-of-svarlist-overridekeys-envs-agree-badguy))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not agree)
             (member-equal
              (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree
                                      member-of-svarlist-overridekeys-envs-agree-badguy))))

  (defretd badguy-member-when-not-<fn>
    (implies (and (not agree)
                  (svarlist-p x))
             (member-equal
              (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)
              x))
    :hints(("Goal" :use ((:instance badguy-member-fix-when-not-<fn>)))))

  (defretd badguy-member-fix-when-not-<fn>
    (implies (not agree)
             (member-equal
              (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)
              (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree
                                      member-of-svarlist-overridekeys-envs-agree-badguy))))

  (defretd <fn>-by-witness
    (implies (not agree)
             (b* ((badguy (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)))
               (and (svar-p badguy)
                    (member-equal badguy (svarlist-fix x))
                    (not (svar-overridekeys-envs-agree badguy overridekeys impl-env spec-env spec-outs)))))
    :hints(("Goal" :in-theory (enable badguy-member-fix-when-not-<fn>
                                      badguy-not-agree-when-not-<fn>))))

  (local (in-theory (disable svarlist-overridekeys-envs-agree)))

  (defthm svarlist-overridekeys-envs-agree-of-subset
    (implies (and (svarlist-overridekeys-envs-agree y overridekeys impl-env spec-env spec-outs)
                  (subsetp-equal (svarlist-fix x) (svarlist-fix y)))
             (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs))
    :hints (("goal" :use ((:instance svarlist-overridekeys-envs-agree-by-witness)
                          (:instance svarlist-overridekeys-envs-agree-implies
                           (x y)
                           (v (svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)))))))

  (local (in-theory (enable 4vec-muxtest-subsetp-when-svar-overridekeys-envs-agree-test
                            4vec-muxtest-subsetp-when-svar-overridekeys-envs-agree-val
                            4vec-override-mux-agrees-when-svar-overridekeys-envs-agree-test
                            4vec-override-mux-agrees-when-svar-overridekeys-envs-agree-val
                            4vec-bit?!-agree-when-svar-overridekeys-envs-agree-test
                            4vec-bit?!-agree-when-svar-overridekeys-envs-agree-val
                            nonoverride-vars-agree-when-svar-overridekeys-envs-agree
                            non-overridekeys-agree-when-svar-overridekeys-envs-agree
                            neither-override-vars-agree-when-svar-overridekeys-envs-agree)))
                            
  
  (defretd 4vec-muxtest-subsetp-when-<fn>-test
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup v spec-env)
                                   (svex-env-lookup v impl-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-muxtest-subsetp-when-<fn>-val
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup (svar-change-override v :test) spec-env)
                                   (svex-env-lookup (svar-change-override v :test) impl-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-override-mux-agrees-when-<fn>-val
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (equal (svar-fix testvar) (svar-change-override v :test))
                  (equal (svar-fix refvar) (svar-change-override v nil))
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-override-mux-agrees (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup v impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup v spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-override-mux-agrees-when-<fn>-test
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (equal (svar-fix valvar) (svar-change-override v :val))
                  (equal (svar-fix refvar) (svar-change-override v nil))
                  (svarlist-member-nonoverride v overridekeys))
             (4vec-override-mux-agrees (svex-env-lookup v impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup v spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-bit?!-agree-when-<fn>-test
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :test)
                  (equal (svar-fix valvar) (svar-change-override v :val))
                  (equal refval (svex-env-lookup (svar-change-override v nil) spec-outs))
                  (svarlist-member-nonoverride v overridekeys))
             (equal (equal (4vec-bit?! (svex-env-lookup v impl-env) (svex-env-lookup valvar impl-env) refval)
                           (4vec-bit?! (svex-env-lookup v spec-env) (svex-env-lookup valvar spec-env) refval))
                    t))
    :hints (("goal" :use <fn>-implies)))

  (defretd 4vec-bit?!-agree-when-<fn>-val
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v :val)
                  (equal (svar-fix testvar) (svar-change-override v :test))
                  (equal refval (svex-env-lookup (svar-change-override v nil) spec-outs))
                  (svarlist-member-nonoverride v overridekeys))
             (equal (equal (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup v impl-env) refval)
                           (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup v spec-env) refval))
                    t))
    :hints (("goal" :use <fn>-implies)))

  (defretd nonoverride-vars-agree-when-<fn>
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (svar-override-p v nil))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd non-overridekeys-agree-when-<fn>
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (not (svarlist-member-nonoverride v overridekeys)))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd neither-override-vars-agree-when-<fn>
    (implies (and agree
                  (member-equal (svar-fix v) (svarlist-fix x))
                  (not (svar-override-p v :test))
                  (not (svar-override-p v :val)))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (local (in-theory (enable svarlist-overridekeys-envs-agree)))
  
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 3)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 4)
  (defcong svex-envs-similar equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 5)
  (defcong set-equiv equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 1
    :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                      (acl2::element-list-final-cdr-p (lambda (x) t))
                                      (acl2::element-p (lambda (x) (svar-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)))
                                      (acl2::element-list-p (lambda (x) (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs))))
                           (x x) (y x-equiv)))
             :expand ((svarlist-overridekeys-envs-agree-badguy x overridekeys impl-env spec-env spec-outs)))))
  (defcong set-equiv equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs) 2)

  (defthm svarlist-overridekeys-envs-agree-of-append
    (equal (svarlist-overridekeys-envs-agree (append x y) overridekeys impl-env spec-env spec-outs)
           (and (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)
                (svarlist-overridekeys-envs-agree y overridekeys impl-env spec-env spec-outs))))

  (defthmd svarlist-overridekeys-envs-agree-redef
    (equal (svarlist-overridekeys-envs-agree x overridekeys impl-env spec-env spec-outs)
           (or (atom x)
               (and (svar-overridekeys-envs-agree (car x) overridekeys impl-env spec-env spec-outs)
                    (svarlist-overridekeys-envs-agree (cdr x) overridekeys impl-env spec-env spec-outs))))
    :hints(("Goal" :in-theory (enable svarlist-overridekeys-envs-agree-badguy)))
    :rule-classes ((:definition :controller-alist ((svarlist-overridekeys-envs-agree t nil nil nil nil)))))

  (defret <fn>-of-svarlist-change-override
    (equal (let ((overridekeys (svarlist-change-override overridekeys type))) <call>)
           agree)))



(defthm 4vec-muxtest-subsetp-of-same
  (4vec-muxtest-subsetp x x)
  :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp))))

(defthm 4vec-override-mux-agrees-of-same
  (4vec-override-mux-agrees test val test val spec-ref)
  :hints(("Goal" :in-theory (enable 4vec-override-mux-agrees
                                    4vec-bit?!
                                    4vec-bitmux))
         (acl2::logbitp-reasoning)))


(define svarlist-overridekeys-envs-agree-extend-env ((vars svarlist-p)
                                                 (overridekeys svarlist-p)
                                                 (impl-env svex-env-p)
                                                 (spec-env svex-env-p))
  :returns (new-env svex-env-p)
  (append (svex-env-extract vars impl-env)
          (svex-env-extract (svarlist-change-override (intersection-equal
                                                       (svarlist-fix vars)
                                                       (svarlist-change-override overridekeys :val))
                                                      :test)
                            impl-env)
          (svex-env-extract (svarlist-change-override (intersection-equal
                                                       (svarlist-fix vars)
                                                       (svarlist-change-override overridekeys :test))
                                                      :val)
                            impl-env)
          (svex-env-fix spec-env))
  ///

  ;; Showing svexlist-overridekey-transparent-p implies transparent-p of its components is tricker -- we need to show that
  ;; if an impl-env satisfies envs-agree on some vars, we can construct a new impl-env that satisfies it on a superset.

  (local (defthm member-change-override-when-subsetp
           (implies (and (member-equal (svar-change-override v1 :test) (svarlist-fix vars1))
                         (equal (svar-change-override v0 nil) (svar-change-override v1 nil)))
                    (member-equal (svar-change-override v0 :test) (svarlist-fix vars1)))
           :hints(("Goal" :in-theory (enable svarlist-fix
                                             equal-of-svar-change-override)))))
  
  (local (defthm member-override-test-lemma
           (implies (and (subsetp-equal (svarlist-change-override overridekeys :test) (svarlist-fix vars1))
                         (member-equal (svar-change-override var nil) (svarlist-change-override overridekeys nil)))
                    (member-equal (svar-change-override var :test) (svarlist-fix vars1)))
           :hints(("Goal" :in-theory (enable svarlist-change-override)))))


  (local (defthm member-svar-change-override-both-norm
           (implies (syntaxp (not (equal type ''nil)))
                    (iff (member-equal (svar-change-override v type) (svarlist-change-override x type))
                         (member-equal (svar-change-override v nil) (svarlist-change-override x nil))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override)))))

  (local (defthm member-svar-change-override-both-norm-free
           (implies (and (syntaxp (not (equal type ''nil)))
                         )
                    (iff (member-equal v (svarlist-change-override x type))
                         (and (svar-override-p v type)
                              (svar-p v)
                              (member-equal (svar-change-override v nil) (svarlist-change-override x nil)))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override)))))
  
  (local (defthm member-of-svarlist-change-val/test-override-lemma
           (iff (member-equal v (svarlist-change-override
                                 (intersection-equal (svarlist-fix vars1)
                                                     (svarlist-change-override overridekeys :val))
                                 :test))
                (and (svar-p v)
                     (svar-override-p v :test)
                     (member-equal (svar-change-override v :val) (svarlist-fix vars1))
                     (member-equal (svar-change-override v nil) (svarlist-change-override overridekeys nil))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             intersection-equal
                                             svarlist-fix
                                             equal-of-svar-change-override)))))

  (local (defthm member-of-svarlist-change-test/val-override-lemma
           (iff (member-equal v (svarlist-change-override
                                 (intersection-equal (svarlist-fix vars1)
                                                     (svarlist-change-override overridekeys :test))
                                 :val))
                (and (svar-p v)
                     (svar-override-p v :val)
                     (member-equal (svar-change-override v :test) (svarlist-fix vars1))
                     (member-equal (svar-change-override v nil) (svarlist-change-override overridekeys nil))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             intersection-equal
                                             svarlist-fix
                                             equal-of-svar-change-override)))))
  
  (defret svar-overridekeys-envs-agree-of-<fn>
    (implies ;(and (member-equal (svar-fix var) (svarlist-fix vars1))
     (svar-overridekeys-envs-agree var overridekeys impl-env spec-env spec-outs)
     (svar-overridekeys-envs-agree var overridekeys
                                   new-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree))))

  (defret svar-overridekeys-envs-agree-of-<fn>-when-not-member-vars
    (implies (and (not (member-equal (svar-fix var) (svarlist-fix vars)))
                  (or (not (and (member-equal (svar-change-override var nil)
                                              (svarlist-change-override overridekeys nil))
                                (or (svar-override-p var :test)
                                    (svar-override-p var :val))))
                      (and (not (member-equal (svar-change-override var :test) (svarlist-fix vars)))
                           (not (member-equal (svar-change-override var :val) (svarlist-fix vars))))))
             (svar-overridekeys-envs-agree var overridekeys
                                           new-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree)))
    :otf-flg t)

  (defret svar-overridekeys-envs-agree-of-<fn>-not-member-vars-when-val
    (implies (and (not (member-equal (svar-fix var) (svarlist-fix vars)))
                  (svar-override-p var :val)
                  (member-equal (svar-change-override var nil)
                                (svarlist-change-override overridekeys nil))
                  (svar-overridekeys-envs-agree (svar-change-override var :test) overridekeys
                                                impl-env spec-env spec-outs))
             (svar-overridekeys-envs-agree var overridekeys
                                           new-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree)))
    :otf-flg t)

  (defret svar-overridekeys-envs-agree-of-<fn>-not-member-vars-when-test
    (implies (and (not (member-equal (svar-fix var) (svarlist-fix vars)))
                  (svar-override-p var :test)
                  (member-equal (svar-change-override var nil)
                                (svarlist-change-override overridekeys nil))
                  (svar-overridekeys-envs-agree (svar-change-override var :val) overridekeys
                                                impl-env spec-env spec-outs))
             (svar-overridekeys-envs-agree var overridekeys
                                           new-env spec-env spec-outs))
    :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree)))
    :otf-flg t)

  ;; (defret svar-overridekeys-envs-agree-of-<fn>-of-val-when-test-member-vars
  ;;   (implies (and (member-equal (svar-change-override var :test) (svarlist-fix vars))
  ;;                 (svar-override-p var :val)
  ;;                 (svar-overridekeys-envs-agree (svar-change-override var :test) overridekeys new-env spec-env spec-outs)
  ;;                 (svar-overridekeys-envs-agree (svar-change-override var :test) overridekeys new-env spec-env spec-outs))
  ;;            (svar-overridekeys-envs-agree var overridekeys
  ;;                                          new-env spec-env spec-outs))
  ;;   :hints(("Goal" :in-theory (enable svar-overridekeys-envs-agree)))
  ;;   :otf-flg t)

  (defret svar-overridekeys-envs-agree-of-<fn>-when-svarlist-overridekeys-envs-agree
    (implies
     (svarlist-overridekeys-envs-agree vars overridekeys impl-env spec-env spec-outs)
     (svar-overridekeys-envs-agree var overridekeys new-env spec-env spec-outs))
    :hints (("goal" :cases ((member-equal (svar-fix var) (svarlist-fix vars)))
             :in-theory (disable <fn>))
            (and stable-under-simplificationp
                 '(:cases ((and (svarlist-member-nonoverride var overridekeys)
                                (or (svar-override-p var :test)
                                    (svar-override-p var :val))))))
            (and stable-under-simplificationp
                 '(:cases ((member-equal (svar-change-override var :test) (svarlist-fix vars)))))
            (and stable-under-simplificationp
                 '(:cases ((member-equal (svar-change-override var :val) (svarlist-fix vars)))
                   :in-theory (e/d (svarlist-overridekeys-envs-agree-implies)
                                   (<fn>))))))

  
  (defret svarlist-overridekeys-envs-agree-of-<fn>
    (implies
     (svarlist-overridekeys-envs-agree vars overridekeys impl-env spec-env spec-outs)
     (svarlist-overridekeys-envs-agree vars2 overridekeys
                                       new-env spec-env spec-outs))
    :hints (("goal" :induct (len vars2)
             
             :expand ((:free (new-env) (svarlist-overridekeys-envs-agree-badguy vars2 overridekeys
                                       new-env spec-env spec-outs)))
             :in-theory (e/d (svarlist-overridekeys-envs-agree)
                             (<fn>)))))

  (defret svarlist-overridekeys-envs-agree-of-<fn>-subset
    (implies
     (svarlist-overridekeys-envs-agree vars overridekeys impl-env spec-env spec-outs)
     (svarlist-overridekeys-envs-agree vars2 overridekeys
                                       new-env spec-env spec-outs))
    :hints (("goal" :induct (len vars2)
             
             :expand ((:free (new-env) (svarlist-overridekeys-envs-agree-badguy vars2 overridekeys
                                       new-env spec-env spec-outs)))
             :in-theory (e/d (svarlist-overridekeys-envs-agree)
                             (<fn>)))))

  (defret svex-envs-agree-of-<fn>
    (svex-envs-agree vars new-env impl-env)
    :hints(("Goal" :in-theory (enable svex-envs-agree-by-witness))))

  (defret svex-eval-of-<fn>
    :pre-bind ((vars (svex-vars x)))
    (equal (svex-eval x new-env)
           (svex-eval x impl-env))
    :hints(("Goal" :in-theory (e/d (svex-eval-when-envs-agree)
                                   (svex-envs-agree-of-<fn>))
            :use ((:instance svex-envs-agree-of-<fn> (vars (svex-vars x)))))))

  (defret svexlist-eval-of-<fn>
    :pre-bind ((vars (svexlist-vars x)))
    (equal (svexlist-eval x new-env)
           (svexlist-eval x impl-env))
    :hints(("Goal" :in-theory (e/d (svexlist-eval-when-envs-agree)
                                   (svex-envs-agree-of-<fn>))
            :use ((:instance svex-envs-agree-of-<fn> (vars (svexlist-vars x)))))))

  (defret svex-alist-eval-of-<fn>
    :pre-bind ((vars (svex-alist-vars x)))
    (equal (svex-alist-eval x new-env)
           (svex-alist-eval x impl-env))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-when-envs-agree)
                                   (svex-envs-agree-of-<fn>))
            :use ((:instance svex-envs-agree-of-<fn> (vars (svex-alist-vars x))))))))


(local (defthm svarlist-p-of-alist-keys
         (implies (svex-env-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (include-book "alist-thms"))

(define overridekeys-envs-agree ((overridekeys svarlist-p)
                                 (impl-env svex-env-p)
                                 (spec-env svex-env-p)
                                 (spec-outs svex-env-p))
  :returns (agree)
  (svarlist-overridekeys-envs-agree
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   overridekeys impl-env spec-env spec-outs)
  ///
  
  (defret <fn>-implies
    (implies agree
             (svar-overridekeys-envs-agree v overridekeys impl-env spec-env spec-outs))
    :hints (("goal" :use ((:instance svarlist-overridekeys-envs-agree-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env)))))
                          (:instance svarlist-overridekeys-envs-agree-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :test)))
                          (:instance svarlist-overridekeys-envs-agree-implies
                           (x (append (alist-keys (svex-env-fix impl-env))
                                      (alist-keys (svex-env-fix spec-env))))
                           (v (svar-change-override v :val))))
             :in-theory (enable svar-overridekeys-envs-agree
                                svex-env-lookup-when-not-boundp
                                svex-env-boundp-iff-member-alist-keys))))

  (defret <fn>-implies-svarlist-overridekeys-envs-agree
    (implies agree
             (svarlist-overridekeys-envs-agree vars overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (e/d (svarlist-overridekeys-envs-agree
                                    svarlist-overridekeys-envs-agree-badguy)
                                   (<fn>)))))

  (defret <fn>-of-svarlist-change-override
    (equal (let ((overridekeys (svarlist-change-override overridekeys type))) <call>)
           agree))
  
  (local (in-theory (enable 4vec-muxtest-subsetp-when-svar-overridekeys-envs-agree-test
                            4vec-override-mux-agrees-when-svar-overridekeys-envs-agree-test
                            4vec-override-mux-agrees-when-svar-overridekeys-envs-agree-val
                            4vec-bit?!-agree-when-svar-overridekeys-envs-agree-test
                            4vec-bit?!-agree-when-svar-overridekeys-envs-agree-val
                            nonoverride-vars-agree-when-svar-overridekeys-envs-agree
                            non-overridekeys-agree-when-svar-overridekeys-envs-agree
                            neither-override-vars-agree-when-svar-overridekeys-envs-agree)))
                            
  (local (in-theory (disable overridekeys-envs-agree overridekeys-envs-agree-implies)))
  (defretd 4vec-muxtest-subsetp-when-<fn>
    (implies (and agree
                  (svar-override-p x :test)
                  (svarlist-member-nonoverride x overridekeys))
             (4vec-muxtest-subsetp (svex-env-lookup x spec-env)
                                   (svex-env-lookup x impl-env)))
    :hints (("goal" :use ((:instance <fn>-implies
                           (v x))))))

  (defretd 4vec-override-mux-agrees-when-<fn>
    (implies (and agree
                  (svar-override-p testvar :test)
                  (svar-override-p valvar :val)
                  (svar-override-p refvar nil)
                  (equal (svar-change-override testvar nil) (svar-fix refvar))
                  (equal (svar-change-override valvar nil) (svar-fix refvar))
                  (svarlist-member-nonoverride refvar overridekeys))
             (4vec-override-mux-agrees (svex-env-lookup testvar impl-env)
                                   (svex-env-lookup valvar impl-env)
                                   (svex-env-lookup testvar spec-env)
                                   (svex-env-lookup valvar spec-env)
                                   (svex-env-lookup refvar spec-outs)))
    :hints (("goal" :use ((:instance <fn>-implies (v testvar)))
             :in-theory (enable equal-of-svar-change-override))))

  (defretd 4vec-bit?!-agree-when-<fn>
    (implies (and agree
                  (svar-override-p testvar :test)
                  (equal (svar-fix valvar) (svar-change-override testvar :val))
                  (equal refval (svex-env-lookup (svar-change-override testvar nil) spec-outs))
                  (svarlist-member-nonoverride testvar overridekeys))
             (equal (equal (4vec-bit?! (svex-env-lookup testvar impl-env) (svex-env-lookup valvar impl-env) refval)
                           (4vec-bit?! (svex-env-lookup testvar spec-env) (svex-env-lookup valvar spec-env) refval))
                    t))
    :hints (("goal" :use ((:instance <fn>-implies (v testvar))))))

  (defretd nonoverride-vars-agree-when-<fn>
    (implies (and agree
                  (svar-override-p v nil))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd non-overridekeys-agree-when-<fn>
    (implies (and agree
                  (not (svarlist-member-nonoverride v overridekeys)))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies)))

  (defretd neither-override-vars-agree-when-<fn>
    (implies (and agree
                  (not (svar-override-p v :test))
                  (not (svar-override-p v :val)))
             (equal (svex-env-lookup v impl-env)
                    (svex-env-lookup v spec-env)))
    :hints (("goal" :use <fn>-implies))))

(define overridekeys-envs-agree-badguy ((overridekeys svarlist-p)
                                        (impl-env svex-env-p)
                                        (spec-env svex-env-p)
                                        (spec-outs svex-env-p))
  :returns (badguy (iff (svar-p badguy) badguy))
  (svarlist-overridekeys-envs-agree-badguy
   (append (alist-keys (svex-env-fix impl-env))
           (alist-keys (svex-env-fix spec-env)))
   overridekeys impl-env spec-env spec-outs)
  ///
  

  (defretd badguy-not-agree-when-not-overridekeys-envs-agree
    (implies (not (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs))
             (not (svar-overridekeys-envs-agree
                   badguy
                   overridekeys impl-env spec-env spec-outs)))
    :hints(("Goal" :in-theory (e/d (badguy-not-agree-when-not-svarlist-overridekeys-envs-agree
                                    overridekeys-envs-agree)
                                   (SVARLIST-OVERRIDEKEYS-ENVS-AGREE-BADGUY-OF-APPEND
                                    SVARLIST-OVERRIDEKEYS-ENVS-AGREE-OF-APPEND))))))

(defsection overridekeys-envs-agree-more
  ;; :extension overridekeys-envs-agree
  (local (std::set-define-current-function overridekeys-envs-agree))

  (defthmd overridekeys-envs-agree-by-witness
    (equal (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
           (svar-overridekeys-envs-agree
            (overridekeys-envs-agree-badguy overridekeys impl-env spec-env spec-outs) overridekeys impl-env spec-env spec-outs))
    :hints(("Goal" :in-theory (e/d (badguy-not-agree-when-not-overridekeys-envs-agree
                                    overridekeys-envs-agree-implies)
                                   (overridekeys-envs-agree-badguy))
            :cases ((overridekeys-envs-agree overridekeys impl-env spec-env spec-outs))))
    :rule-classes :definition)
  
  (defcong svex-envs-similar equal (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs) 2
    :hints (("goal" :cases ((overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-agree clause))
                      (other-arg (if (eq (nth 2 lit) 'impl-env) 'impl-env-equiv 'impl-env)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-agree-implies
                            (impl-env ,other-arg)
                            (v (overridekeys-envs-agree-badguy . ,(cdr lit))))))))))
  (defcong svex-envs-similar equal (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs) 3
    :hints (("goal" :cases ((overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-agree clause))
                      (other-arg (if (eq (nth 3 lit) 'spec-env) 'spec-env-equiv 'spec-env)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-agree-implies
                            (spec-env ,other-arg)
                            (v (overridekeys-envs-agree-badguy . ,(cdr lit))))))))))
  (defcong svex-envs-similar equal (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs) 4
    :hints (("goal" :cases ((overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-agree clause))
                      (other-arg (if (eq (nth 4 lit) 'spec-outs) 'spec-outs-equiv 'spec-outs)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-agree-implies
                            (spec-outs ,other-arg)
                            (v (overridekeys-envs-agree-badguy . ,(cdr lit))))))))))
  (defcong set-equiv equal (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs) 1
    :hints (("goal" :cases ((overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'overridekeys-envs-agree clause))
                      (other-arg (if (eq (nth 1 lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance overridekeys-envs-agree-implies
                            (overridekeys ,other-arg)
                            (v (overridekeys-envs-agree-badguy . ,(cdr lit)))))))))))

  

                                           

(defsection svex-overridekey-transparent-p
  (defun-sk svex-overridekey-transparent-p (x overridekeys subst)
    (forall (impl-env spec-env)
            (implies (overridekeys-envs-agree overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                     (equal (svex-eval x impl-env)
                            (svex-eval x spec-env)))))

  (in-theory (disable svex-overridekey-transparent-p
                      svex-overridekey-transparent-p-necc))

  (defthmd svex-overridekey-transparent-p-implies
    (implies (and (svex-overridekey-transparent-p x overridekeys subst)
                  (svarlist-overridekeys-envs-agree (svex-vars x) overridekeys impl-env spec-env (svex-alist-eval subst spec-env)))
             (equal (svex-eval x impl-env)
                    (svex-eval x spec-env)))
    :hints (("goal" :use ((:instance svex-overridekey-transparent-p-necc
                           (impl-env (svarlist-overridekeys-envs-agree-extend-env
                                      (svex-vars x)
                                      overridekeys impl-env spec-env))))
             :in-theory (e/d (overridekeys-envs-agree)
                             (svarlist-overridekeys-envs-agree-of-append)))))

  (defcong svex-eval-equiv equal (svex-overridekey-transparent-p x overridekeys subst) 1
    :hints (("goal" :cases ((svex-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-overridekey-transparent-p clause))
                      (other (if (eq (nth 1 lit) 'x) 'x-equiv 'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-overridekey-transparent-p-necc
                            (x ,other)
                            (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defcong set-equiv equal (svex-overridekey-transparent-p x overridekeys subst) 2
    :hints (("goal" :cases ((svex-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defcong svex-alist-eval-equiv equal (svex-overridekey-transparent-p x overridekeys subst) 3
    :hints (("goal" :cases ((svex-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-overridekey-transparent-p clause))
                      (other (if (eq (nth 3 lit) 'subst) 'subst-equiv 'subst)))
                   `(:expand (,lit)
                     :use ((:instance svex-overridekey-transparent-p-necc
                            (subst ,other)
                            (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (fty::deffixcong svarlist-equiv equal (svex-overridekey-transparent-p x overridekeys subst) overridekeys
    :hints (("goal" :cases ((svex-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-fix overridekeys) 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defthm svex-overridekey-transparent-p-of-svarlist-change-override
    (equal (svex-overridekey-transparent-p x (svarlist-change-override overridekeys type) subst)
           (svex-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :cases ((svex-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-change-override overridekeys type) 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness . ,(cdr lit))))))))))))

(defsection svexlist-overridekey-transparent-p
  (defun-sk svexlist-overridekey-transparent-p (x overridekeys subst)
    (forall (impl-env spec-env)
            (implies (overridekeys-envs-agree overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                     (equal (svexlist-eval x impl-env)
                            (svexlist-eval x spec-env)))))

  (in-theory (disable svexlist-overridekey-transparent-p
                      svexlist-overridekey-transparent-p-necc))

  (defthmd svexlist-overridekey-transparent-p-implies
    (implies (and (svexlist-overridekey-transparent-p x overridekeys subst)
                  (svarlist-overridekeys-envs-agree (svexlist-vars x) overridekeys impl-env spec-env (svex-alist-eval subst spec-env)))
             (equal (svexlist-eval x impl-env)
                    (svexlist-eval x spec-env)))
    :hints (("goal" :use ((:instance svexlist-overridekey-transparent-p-necc
                           (impl-env (svarlist-overridekeys-envs-agree-extend-env
                                      (svexlist-vars x)
                                      overridekeys impl-env spec-env))))
             :in-theory (e/d (overridekeys-envs-agree)
                             (svarlist-overridekeys-envs-agree-of-append)))))

  (defcong svexlist-eval-equiv equal (svexlist-overridekey-transparent-p x overridekeys subst) 1
    :hints (("goal" :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svexlist-overridekey-transparent-p clause))
                      (other (if (eq (nth 1 lit) 'x) 'x-equiv 'x)))
                   `(:expand (,lit)
                     :use ((:instance svexlist-overridekey-transparent-p-necc
                            (x ,other)
                            (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defcong set-equiv equal (svexlist-overridekey-transparent-p x overridekeys subst) 2
    :hints (("goal" :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svexlist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand ((:with svexlist-overridekey-transparent-p ,lit))
                     :use ((:instance svexlist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defcong svex-alist-eval-equiv equal (svexlist-overridekey-transparent-p x overridekeys subst) 3
    :hints (("goal" :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svexlist-overridekey-transparent-p clause))
                      (other (if (eq (nth 3 lit) 'subst) 'subst-equiv 'subst)))
                   `(:expand (,lit)
                     :use ((:instance svexlist-overridekey-transparent-p-necc
                            (subst ,other)
                            (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (fty::deffixcong svarlist-equiv equal (svexlist-overridekey-transparent-p x overridekeys subst) overridekeys
    :hints (("goal" :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svexlist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-fix overridekeys) 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svexlist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defthm svexlist-overridekey-transparent-p-of-svarlist-change-override
    (equal (svexlist-overridekey-transparent-p x (svarlist-change-override overridekeys type) subst)
           (svexlist-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svexlist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-change-override overridekeys type) 'overridekeys)))
                   `(:expand ((:with svexlist-overridekey-transparent-p ,lit))
                     :use ((:instance svexlist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness . ,(cdr lit))))))))))))




(defsection svex-alist-overridekey-transparent-p
  (defun-sk svex-alist-overridekey-transparent-p (x overridekeys subst)
    (forall (impl-env spec-env)
            (implies (overridekeys-envs-agree overridekeys impl-env spec-env (svex-alist-eval subst spec-env))
                     (equal (svex-alist-eval x impl-env)
                            (svex-alist-eval x spec-env)))))

  (in-theory (disable svex-alist-overridekey-transparent-p
                      svex-alist-overridekey-transparent-p-necc))

  (defthmd svex-alist-overridekey-transparent-p-implies
    (implies (and (svex-alist-overridekey-transparent-p x overridekeys subst)
                  (svarlist-overridekeys-envs-agree (svex-alist-vars x) overridekeys impl-env spec-env (svex-alist-eval subst spec-env)))
             (equal (svex-alist-eval x impl-env)
                    (svex-alist-eval x spec-env)))
    :hints (("goal" :use ((:instance svex-alist-overridekey-transparent-p-necc
                           (impl-env (svarlist-overridekeys-envs-agree-extend-env
                                      (svex-alist-vars x)
                                      overridekeys impl-env spec-env))))
             :in-theory (e/d (overridekeys-envs-agree)
                             (svarlist-overridekeys-envs-agree-of-append)))))
  
  (defcong svex-alist-eval-equiv!! equal (svex-alist-overridekey-transparent-p x overridekeys subst) 1
    :hints (("goal" :cases ((svex-alist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-alist-overridekey-transparent-p clause))
                      (other (if (eq (nth 1 lit) 'x) 'x-equiv 'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-alist-overridekey-transparent-p-necc
                            (x ,other)
                            (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defcong set-equiv equal (svex-alist-overridekey-transparent-p x overridekeys subst) 2
    :hints (("goal" :cases ((svex-alist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-alist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand ((:with svex-alist-overridekey-transparent-p ,lit))
                     :use ((:instance svex-alist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))
  
  (defcong svex-alist-eval-equiv equal (svex-alist-overridekey-transparent-p x overridekeys subst) 3
    :hints (("goal" :cases ((svex-alist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-alist-overridekey-transparent-p clause))
                      (other (if (eq (nth 3 lit) 'subst) 'subst-equiv 'subst)))
                   `(:expand (,lit)
                     :use ((:instance svex-alist-overridekey-transparent-p-necc
                            (subst ,other)
                            (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (fty::deffixcong svarlist-equiv equal (svex-alist-overridekey-transparent-p x overridekeys subst) overridekeys
    :hints (("goal" :cases ((svex-alist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-alist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-fix overridekeys) 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-alist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit)))))))))))

  (defthm svex-alist-overridekey-transparent-p-of-svarlist-change-override
    (equal (svex-alist-overridekey-transparent-p x (svarlist-change-override overridekeys type) subst)
           (svex-alist-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :cases ((svex-alist-overridekey-transparent-p x overridekeys subst)))
            (And stable-under-simplificationp
                 (b* ((lit (assoc 'svex-alist-overridekey-transparent-p clause))
                      (other (if (eq (nth 2 lit) 'overridekeys) '(svarlist-change-override overridekeys type) 'overridekeys)))
                   `(:expand ((:with svex-alist-overridekey-transparent-p ,lit))
                     :use ((:instance svex-alist-overridekey-transparent-p-necc
                            (overridekeys ,other)
                            (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))
                            (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness . ,(cdr lit))))))))))))



(defsection svex-overridekey-transparent-p-recurrence
  (defthmd svex-overridekey-transparent-p-when-args-transparent
    (implies (and (svex-case x :call)
                  (svexlist-overridekey-transparent-p (svex-call->args x) overridekeys subst))
             (svex-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :expand ((svex-overridekey-transparent-p x overridekeys subst))
             :use ((:instance svexlist-overridekey-transparent-p-necc
                    (x (svex-call->args x))
                    (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness x overridekeys subst))))))))

  (defthmd svex-overridekey-transparent-p-when-const
    (implies (svex-case x :quote)
             (svex-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :in-theory (enable svex-overridekey-transparent-p))))

  (defthmd svex-overridekey-transparent-p-when-non-override-var
    (implies (and (svex-case x :var)
                  (or (and (not (svar-override-p (svex-var->name x) :test))
                           (not (svar-override-p (svex-var->name x) :val)))
                      (not (svarlist-member-nonoverride (svex-var->name x) overridekeys))))
             (svex-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :in-theory (enable svex-overridekey-transparent-p
                                       non-overridekeys-agree-when-overridekeys-envs-agree
                                       neither-override-vars-agree-when-overridekeys-envs-agree)
             :expand ((:Free (env) (svex-eval x env))))))
  
  (defthm svexlist-overridekey-transparent-p-of-nil
    (svexlist-overridekey-transparent-p nil overridekeys subst)
    :hints(("Goal" :in-theory (enable svexlist-overridekey-transparent-p))))
  
  (defthmd svexlist-overridekey-transparent-p-when-car-cdr
    (implies (and (svex-overridekey-transparent-p (car x) overridekeys subst)
                  (svexlist-overridekey-transparent-p (cdr x) overridekeys subst))
             (svexlist-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :expand ((svexlist-overridekey-transparent-p x overridekeys subst))
             :use ((:instance svexlist-overridekey-transparent-p-necc
                    (x (cdr x))
                    (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness x overridekeys subst))))
                   (:instance svex-overridekey-transparent-p-necc
                    (x (car x))
                    (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness x overridekeys subst))))))))

  (defthm svex-alist-overridekey-transparent-p-of-nil
    (svex-alist-overridekey-transparent-p nil overridekeys subst)
    :hints(("Goal" :in-theory (enable svex-alist-overridekey-transparent-p
                                      svex-alist-eval))))


  (defthmd svex-alist-overridekey-transparent-p-when-cdar-cdr
    (implies (and (svex-overridekey-transparent-p (cdar x) overridekeys subst)
                  (svex-alist-overridekey-transparent-p (cdr x) overridekeys subst))
             (svex-alist-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :expand ((svex-alist-overridekey-transparent-p x overridekeys subst))
             :in-theory (enable svex-alist-eval svex-alist-vars)
             :use ((:instance svex-alist-overridekey-transparent-p-necc
                    (x (cdr x))
                    (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x overridekeys subst))))
                   (:instance svex-overridekey-transparent-p-necc
                    (x (cdar x))
                    (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x overridekeys subst))))))))

  (defthmd svex-alist-overridekey-transparent-p-when-bad-car
    (implies (and (not (and (consp (car x)) (svar-p (caar x))))
                  (svex-alist-overridekey-transparent-p (cdr x) overridekeys subst))
             (svex-alist-overridekey-transparent-p x overridekeys subst))
    :hints (("goal" :expand ((svex-alist-overridekey-transparent-p x overridekeys subst))
             :in-theory (enable svex-alist-eval svex-alist-vars)
             :use ((:instance svex-alist-overridekey-transparent-p-necc
                    (x (cdr x))
                    (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x overridekeys subst))))
                   (:instance svex-overridekey-transparent-p-necc
                    (x (cdar x))
                    (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x overridekeys subst))))))))

  (defthmd svexlist-overridekey-transparent-p-implies-car
    (implies (svexlist-overridekey-transparent-p x overridekeys subst)
             (svex-overridekey-transparent-p (car x) overridekeys subst))
    :hints (("goal" :expand ((svex-overridekey-transparent-p (car x) overridekeys subst)
                             (svex-overridekey-transparent-p nil overridekeys subst)
                             (:free (env) (svexlist-eval x env))
                             (svexlist-vars x))
             :in-theory (enable svex-overridekey-transparent-p-when-const)
             :use ((:instance svexlist-overridekey-transparent-p-necc
                    (x x)
                    (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness (car x) overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness (car x) overridekeys subst)))))))
    :otf-flg t)

  (defthmd svexlist-overridekey-transparent-p-implies-cdr
    (implies (svexlist-overridekey-transparent-p x overridekeys subst)
             (svexlist-overridekey-transparent-p (cdr x) overridekeys subst))
    :hints (("goal" :expand ((svexlist-overridekey-transparent-p (cdr x) overridekeys subst)
                             (:free (env) (svexlist-eval x env))
                             (svexlist-vars x))
             :use ((:instance svexlist-overridekey-transparent-p-necc
                    (x x)
                    (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness (cdr x) overridekeys subst)))
                    (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness (cdr x) overridekeys subst)))))))
    :otf-flg t)


  (defthmd svexlist-overridekey-transparent-p-rec
    (equal (svexlist-overridekey-transparent-p x overridekeys subst)
           (if (atom x)
               t
             (and (svex-overridekey-transparent-p (car x) overridekeys subst)
                  (svexlist-overridekey-transparent-p (cdr x) overridekeys subst))))
    :hints(("Goal" :in-theory (enable svexlist-overridekey-transparent-p-implies-cdr
                                      svexlist-overridekey-transparent-p-implies-car
                                      svexlist-overridekey-transparent-p-when-car-cdr)
            :cases ((svexlist-overridekey-transparent-p x overridekeys subst)))
           (and stable-under-simplificationp
                '(:in-theory (enable svexlist-overridekey-transparent-p))))
    :rule-classes ((:definition :controller-alist ((svexlist-overridekey-transparent-p t nil nil)))))



  (defthmd svex-alist-overridekey-transparent-p-implies-cdar
    (implies (and (svex-alist-overridekey-transparent-p x overridekeys subst)
                  (svar-p (caar x)))
             (svex-overridekey-transparent-p (cdar x) overridekeys subst))
    :hints (("goal" :expand ((svex-overridekey-transparent-p (cdar x) overridekeys subst)
                             (svex-overridekey-transparent-p nil overridekeys subst)
                             (:free (env) (svex-alist-eval x env))
                             (svex-alist-vars x))
             :use ((:instance svex-alist-overridekey-transparent-p-necc
                    (x x)
                    (impl-env (mv-nth 0 (svex-overridekey-transparent-p-witness (cdar x) overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness (cdar x) overridekeys subst)))))))
    :otf-flg t)

  (defthmd svex-alist-overridekey-transparent-p-implies-cdr
    (implies (svex-alist-overridekey-transparent-p x overridekeys subst)
             (svex-alist-overridekey-transparent-p (cdr x) overridekeys subst))
    :hints (("goal" :expand ((svex-alist-overridekey-transparent-p (cdr x) overridekeys subst)
                             (:free (env) (svex-alist-eval x env))
                             (svex-alist-vars x))
             :use ((:instance svex-alist-overridekey-transparent-p-necc
                    (x x)
                    (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness (cdr x) overridekeys subst)))
                    (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness (cdr x) overridekeys subst)))))))
    :otf-flg t)


  (defthmd svex-alist-overridekey-transparent-p-rec
    (equal (svex-alist-overridekey-transparent-p x overridekeys subst)
           (if (atom x)
               t
             (and (or (atom (car x))
                      (not (svar-p (caar x)))
                      (svex-overridekey-transparent-p (cdar x) overridekeys subst))
                  (svex-alist-overridekey-transparent-p (cdr x) overridekeys subst))))
    :hints(("Goal" :in-theory (enable svex-alist-overridekey-transparent-p-implies-cdr
                                      svex-alist-overridekey-transparent-p-implies-cdar
                                      svex-alist-overridekey-transparent-p-when-cdar-cdr
                                      svex-alist-overridekey-transparent-p-when-bad-car
                                      svex-alist-eval)
            :do-not-induct t
            :cases ((svex-alist-overridekey-transparent-p x overridekeys subst))))
    :otf-flg t
    :rule-classes ((:definition :controller-alist ((svex-alist-overridekey-transparent-p t nil nil)))))


  (defthm svex-alist-overridekey-transparent-p-of-pairlis$
    (implies (and (svarlist-p keys)
                  (equal (len keys) (len vals)))
             (equal (svex-alist-overridekey-transparent-p (pairlis$ keys vals) overridekeys subst)
                    (svexlist-overridekey-transparent-p vals overridekeys subst)))
    :hints(("Goal" :induct (pairlis$ keys vals)
            :expand ((:free (a b) (svex-alist-overridekey-transparent-p (cons a b) overridekeys subst))
                     (svexlist-overridekey-transparent-p vals overridekeys subst)))))

  (defthm svex-overridekey-transparent-of-alist-lookup
    (implies (svex-alist-overridekey-transparent-p alist overridekeys subst)
             (svex-overridekey-transparent-p (svex-lookup key alist) overridekeys subst))
    :hints (("goal" :induct (len alist)
             :in-theory (enable svex-overridekey-transparent-p-when-const)
             :expand ((svex-alist-overridekey-transparent-p alist overridekeys subst)
                      (:with svex-lookup-redef (svex-lookup key alist))))))

  (defthm svex-alist-overridekey-transparent-p-by-alist-vals
    (implies (svexlist-overridekey-transparent-p (svex-alist-vals x) overridekeys subst)
             (svex-alist-overridekey-transparent-p x overridekeys subst))
    :hints(("Goal" :in-theory (enable svex-alist-vals)
            :induct t
            :expand ((:free (a b)
                      (svexlist-overridekey-transparent-p (cons a b) overridekeys subst))
                     (svex-alist-overridekey-transparent-p x overridekeys subst))))))



(defxdoc override-transparent
  :parents (svex-decomposition-methodology)
  :short "Description of the override transparency property needed for decomposition"
  :long #{"""<p>In the SVTV decomposition methodology, we expect to be able to
override the values of certain internal signals of a design in order to reason
about fanout logic of those signals without including the fanin logic.  In
order to then compose these theorems with theorems about other decompositions
of the design, we need to know that if we overrode those signals with the same
values they would have anyway, then we get the same outputs.  This is called
the override transparency property. Here we explain that property more
formally.</p>

<p>Override transparency is a property of an expression or set of expressions
with respect to (1) a set of <em>overridekeys</em> (a set of internal signals
that may be overridden) and (2) a substitution (svex-alist) giving the driving
expressions for those internal signals if those expressions evaluate the same
on environments that agree in a certain sense with respect to those variables.
 (When discussing override-transparency of an FSM, we use the FSM's value
substitution for the driving expressions; an FSM is then override-transparent
on a set of keys if its value substitution and nextstate substitution are both
override-transparent with respect to those keys and the value substitution.)  A
set of expressions is override-transparent if the expressions evaluate to the
same values on any two environments which are consistent on all override values
and agree strictly on all other variables.  This notion of consistency on
overridden values essentially says that environment @($\mathrm{env}_1$) overrides a
superset of the signals that @($\mathrm{env}_2$) does, the additional overridden signals
in @($\mathrm{env}_1$) are given the same values as are computed for them under
@($\mathrm{env}_2$), and all other assignments are the same.</p>

<p>To formalize this more completely we need a few definitions.</p>

<p>Each variable has an override property, which may be @('nil'), @(':test'),
or @(':val').  Regular inputs, outputs, and internal signals of a circuit have
override property @('nil') (or, they are non-override variables).  We can
reversibly change the override property of a variable, so each non-override
variable has a unique corresponding override-test and override-val variable.  In LaTeX formulas following, we'll use non-subscripted variables such as @($s$) for non-override variables, @($s_t$) for the corresponding override-test variable, and @($s_v$) for the corresponding override-val variable.</p>

<p>
Before we compose the local assignments for each signal of the circuit to
obtain the full update functions of all signals, we insert override muxes on
some or all internal signals, replacing each use of such signals with a bitwise
if-then-else expression: @($ s_t\ ?\ s_v\ :\ s$).
Non-override variables such as @($s$) are then replaced during composition
with their update functions, while override-test and override-val variables @($s_t$) and @($s_v$)
remain free.  In the resulting formulas, we can then override signal @($s$) or part
of it by setting some bits of @($s_t$) to 1s and
setting the corresponding bits of  @($s_v$) to the desired
values.</p>

<p>We can now define the override consistency condition between environments.
In ACL2 this predicate is named @('overridekeys-envs-agree').  This is a
relation between two environments, parametrized by a set of variables and a
substitution (svex-alist) giving the values of internal signals in terms of
primary inputs and previous state variables.  It is not an equivalence relation
because one environment @($\mathrm{env}_1$) (called @('impl-env') in the ACL2
function) must override a superset of the variables of the other environment
@($\mathrm{env}_2$) (@('spec-env')).</p>

<h4>Definition: Override Consistency of Environments</h4>

<p>Environments @($\mathrm{env}_1$) and @($\mathrm{env}_2$) are
<em>override-consistent</em> with respect to override signals @($S$) and value
substitution @($\sigma$) if for all non-override signals @($s$) and bit
indices @($i$):</p>
<ol>
<li>Values of non-override variables and override test/value variables not in @($S$) are equal in the two environments:
@([\mathrm{env}_1[s] = \mathrm{env}_2[s]])
@([s \notin S \Rightarrow \mathrm{env}_1[s_t] = \mathrm{env}_2[s_t]])
@([s \notin S \Rightarrow \mathrm{env}_1[s_v] = \mathrm{env}_2[s_v]])
</li>
<li>All signal bits overridden in @($\mathrm{env}_2$) are also overridden in @($\mathrm{env}_1$):
@([\mathrm{env}_2[s_t][i] = 1 \Rightarrow \mathrm{env}_1[s_t][i] = 1])
</li>
<li>Signal bits overridden in both environments are overridden to the same value:
@([\mathrm{env}_2[s_t][i] = 1 \Rightarrow \mathrm{env}_1[s_v][i] = \mathrm{env}_2[s_v][i]])
</li>
<li>Signal bits overridden in @($\mathrm{env}_1$) and not @($\mathrm{env}_2$) are overridden there to the corresponding bit of the evaluation with @($\mathrm{env}_2$) of that signal's binding in @($\sigma$):
@([\mathrm{env}_1[s_t][i] = 1 \wedge \mathrm{env}_2[s_t][i] \neq 1 \Rightarrow \mathrm{env}_1[s_v][i] = \textrm{Ev}(\sigma[s],\mathrm{env}_2)[i]])
</li>
</ol>

<p>Finally, we can now define the override transparency property of
expressions, expression lists, and substitutions.  This is parametrized on the
same set of variables and substitution as in the override consistency of
environments, and simply says that for any two environments that satisfy the
override consistency condition, the evaluations of that expression/expression
list/substitution on those two environments are equal.</p>

"""})
