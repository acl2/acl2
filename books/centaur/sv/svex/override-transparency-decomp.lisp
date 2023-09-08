; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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

(include-book "../svex/override-transparency")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defthm svarlist-change-override-of-append
  (equal (svarlist-change-override (append x y) type)
         (append (svarlist-change-override x type)
                 (svarlist-change-override y type)))
  :hints(("Goal" :in-theory (enable svarlist-change-override))))



(defsection overridekeys-envs-agree-decomp

  (local
   (defthm logandc2-equal-0-transitive
     (implies (and (equal (logandc2 x y) 0)
                   (equal (logandc2 y z) 0))
              (equal (logandc2 x z) 0))
     :hints ((bitops::logbitp-reasoning))))
    
  
  (defthm 4vec-muxtest-subsetp-transitive
    (implies (and (4vec-muxtest-subsetp x y)
                  (4vec-muxtest-subsetp y z))
             (4vec-muxtest-subsetp x z))
    :hints(("Goal" :in-theory (e/d (4vec-muxtest-subsetp)
                                   (logandc2)))))

  (defthm 4vec-override-mux-agrees-transitive
    (implies (and (4vec-override-mux-agrees test2 val2 test1 val1 ref)
                  (4vec-override-mux-agrees test3 val3 test2 val2 ref)
                  (4vec-muxtest-subsetp test1 test2)
                  (4vec-muxtest-subsetp test2 test3))
             (4vec-override-mux-agrees test3 val3 test1 val1 ref))
    :hints(("Goal" :in-theory (e/d (4vec-override-mux-agrees
                                    4vec-bit?!
                                    4vec-bitmux
                                    4vec-muxtest-subsetp)
                                   (logandc2)))
           (bitops::logbitp-reasoning)))

  
  (defthm overridekeys-envs-agree-of-append
    (implies (and (overridekeys-envs-agree keys1 env2 env1 values)
                  (overridekeys-envs-agree keys2 env3 env2 values))
             (overridekeys-envs-agree (append keys1 keys2) env3 env1 values))
    :hints ((flet ((make-inst (keys override)
                              `(:instance overridekeys-envs-agree-implies
                                (overridekeys ,keys)
                                (impl-env ,(if (eq keys 'keys1) 'env2 'env3))
                                (spec-env ,(if (eq keys 'keys1) 'env1 'env2))
                                (spec-outs values)
                                (v ,(let ((bg '(overridekeys-envs-agree-badguy
                                                (append keys1 keys2) env3 env1 values)))
                                      (case override
                                        (:test `(svar-change-override ,bg :test))
                                        (:val  `(svar-change-override ,bg :val))
                                        ((nil) `(svar-change-override ,bg nil))
                                        (t     bg)))))))
                  `(:use ((:instance badguy-not-agree-when-not-overridekeys-envs-agree
                           (overridekeys (append keys1 keys2))
                           (impl-env env3)
                           (spec-env env1)
                           (spec-outs values))
                          ,(make-inst 'keys1 t)
                          ,(make-inst 'keys2 t)
                          ,(make-inst 'keys1 :val)
                          ,(make-inst 'keys2 :val)
                          ,(make-inst 'keys1 :test)
                          ,(make-inst 'keys2 :test))
                    :in-theory (e/d (svar-overridekeys-envs-agree)
                                    (badguy-not-agree-when-not-overridekeys-envs-agree
                                     overridekeys-envs-agree-implies))
                    :do-not-induct t))))

  (local (defthm member-svar-change-override-when-member
           (implies (member-equal (svar-fix x) (svarlist-fix y))
                    (member-equal (svar-change-override x type)
                                  (svarlist-change-override y type)))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             svarlist-fix
                                             equal-of-svar-change-override)))))

  (local (defthm member-of-svar-change-override
           (implies (syntaxp (not (equal type ''nil)))
                    (iff (member-equal v (svarlist-change-override x type))
                         (and (svar-p v)
                              (member-equal (svar-change-override v nil)
                                            (svarlist-change-override x nil))
                              (svar-override-p v type))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override)))))

  
  (defthm overridekeys-envs-agree-of-append-implies-keys-decomp-1
    (implies (overridekeys-envs-agree (append keys1 keys2) env2 env1 values)
             (overridekeys-envs-agree keys1 (append (svex-env-extract
                                                     (overridekeys->override-vars keys1)
                                                     env2) env1) env1 values))
    :hints ((flet ((make-inst (override)
                              `(:instance overridekeys-envs-agree-implies
                                (overridekeys (append keys1 keys2))
                                (impl-env env2)
                                (spec-env env1)
                                (spec-outs values)
                                (v ,(let ((bg '(overridekeys-envs-agree-badguy
                                                keys1
                                                (append (svex-env-extract (overridekeys->override-vars keys1) env2) env1)
                                                env1 values)))
                                      (case override
                                        (:test `(svar-change-override ,bg :test))
                                        (:val  `(svar-change-override ,bg :val))
                                        ((nil) `(svar-change-override ,bg nil))
                                        (t     bg)))))))
                  `(:use ((:instance badguy-not-agree-when-not-overridekeys-envs-agree
                           (overridekeys keys1)
                           (impl-env (append (svex-env-extract (overridekeys->override-vars keys1) env2) env1))
                           (spec-env env1)
                           (spec-outs values))
                          ,(make-inst t))
                    :in-theory (e/d (svar-overridekeys-envs-agree
                                     overridekeys->override-vars-under-set-equiv)
                                    (badguy-not-agree-when-not-overridekeys-envs-agree
                                     overridekeys-envs-agree-implies))
                    :do-not-induct t))))

  (defthm overridekeys-envs-agree-of-append-implies-keys-decomp-2
    (implies (overridekeys-envs-agree (append keys1 keys2) env2 env1 values)
             (overridekeys-envs-agree keys2 env2 (append (svex-env-extract
                                                          (overridekeys->override-vars keys1)
                                                          env2)
                                                         env1)
                                      values))
    :hints ((flet ((make-inst (override)
                              `(:instance overridekeys-envs-agree-implies
                                (overridekeys (append keys1 keys2))
                                (impl-env env2)
                                (spec-env env1)
                                (spec-outs values)
                                (v ,(let ((bg '(overridekeys-envs-agree-badguy
                                                keys2
                                                env2
                                                (append (svex-env-extract (overridekeys->override-vars keys1) env2) env1) values)))
                                      (case override
                                        (:test `(svar-change-override ,bg :test))
                                        (:val  `(svar-change-override ,bg :val))
                                        ((nil) `(svar-change-override ,bg nil))
                                        (t     bg)))))))
                  `(:use ((:instance badguy-not-agree-when-not-overridekeys-envs-agree
                           (overridekeys keys2)
                           (impl-env env2)
                           (spec-env (append (svex-env-extract (overridekeys->override-vars keys1) env2) env1))
                           (spec-outs values))
                          ,(make-inst t))
                    :in-theory (e/d (svar-overridekeys-envs-agree
                                     overridekeys->override-vars-under-set-equiv)
                                    (badguy-not-agree-when-not-overridekeys-envs-agree
                                     overridekeys-envs-agree-implies))
                    :do-not-induct t))))

  
  (defthm overridekeys-envs-agree-self
    (overridekeys-envs-agree keys env env values)
    :hints (("goal" :use ((:instance badguy-not-agree-when-not-overridekeys-envs-agree
                           (overridekeys keys)
                           (impl-env env)
                           (spec-env env)
                           (spec-outs values)))
             :in-theory (e/d (svar-overridekeys-envs-agree)
                             (badguy-not-agree-when-not-overridekeys-envs-agree)))))


  )

(defsection override-transparent-p-decompose-by-keys
  (local
   (defthm svexlist-overridekey-transparent-p-decompose-by-keys
     (implies (svexlist-overridekey-transparent-p x (append keys1 keys2) subst)
              (svexlist-overridekey-transparent-p x keys1 subst))
     :hints (("goal" :do-not-induct t
              :expand ((:with svexlist-overridekey-transparent-p
                        (svexlist-overridekey-transparent-p x keys1 subst)))
              :use ((:instance overridekeys-envs-agree-of-append
                     (keys1 keys1)
                     (keys2 keys2)
                     (values (svex-alist-eval subst (mv-nth 1 (svexlist-overridekey-transparent-p-witness x keys1 subst))))
                     (env3 (mv-nth 0 (svexlist-overridekey-transparent-p-witness x keys1 subst)))
                     (env2 (mv-nth 0 (svexlist-overridekey-transparent-p-witness x keys1 subst)))
                     (env1 (mv-nth 1 (svexlist-overridekey-transparent-p-witness x keys1 subst))))
                    (:instance svexlist-overridekey-transparent-p-necc
                     (overridekeys (append keys1 keys2))
                     (impl-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness x keys1 subst)))
                     (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness x keys1 subst)))))
              :in-theory (disable overridekeys-envs-agree-of-append)))))

  (local (defthm append-set-diff-under-set-equiv-when-subsetp
           (implies (subsetp-equal a b)
                    (set-equiv (append a (set-difference-equal b a))
                               b))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))
  
  (defthm svexlist-overridekey-transparent-p-when-subsetp
    (implies (And (svexlist-overridekey-transparent-p x keys1 subst)
                  (subsetp-equal (svarlist-fix keys2) (svarlist-fix keys1)))
             (svexlist-overridekey-transparent-p x keys2 subst))
    :hints (("goal" :use ((:instance svexlist-overridekey-transparent-p-decompose-by-keys
                           (keys1 (svarlist-fix keys2))
                           (keys2 (set-difference-equal (svarlist-fix keys1) (svarlist-fix keys2)))))
             :in-theory (disable svexlist-overridekey-transparent-p-decompose-by-keys
                                 SVEXLIST-OVERRIDEKEY-TRANSPARENT-P-SVARLIST-EQUIV-CONGRUENCE-ON-OVERRIDEKEYS))))


  (defthm svexlist-overridekey-transparent-p-by-decomp
    (implies (and (svexlist-overridekey-transparent-p x keys1 subst)
                  (svex-alist-overridekey-transparent-p subst keys1 subst)
                  (svexlist-overridekey-transparent-p x keys2 subst))
             (svexlist-overridekey-transparent-p x (append keys1 keys2) subst))
    :hints ((b* ((witness '(svexlist-overridekey-transparent-p-witness
                            x (append keys1 keys2) subst))
                 (impl-env `(mv-nth 0 ,witness))
                 (spec-env `(mv-nth 1 ,witness))
                 (mid `(append (svex-env-extract
                                (overridekeys->override-vars keys1) ,impl-env)
                               ,spec-env)))
              `(:do-not-induct t
                :expand ((:with svexlist-overridekey-transparent-p
                          (svexlist-overridekey-transparent-p x (append keys1 keys2) subst)))
                :use ((:instance svexlist-overridekey-transparent-p-necc
                       (overridekeys keys1)
                       (impl-env ,mid)
                       (spec-env ,spec-env))
                      (:instance svex-alist-overridekey-transparent-p-necc
                       (x subst)
                       (overridekeys keys1)
                       (impl-env ,mid)
                       (spec-env ,spec-env))
                      (:instance svexlist-overridekey-transparent-p-necc
                       (overridekeys keys2)
                       (impl-env ,impl-env)
                       (spec-env ,mid)))
                :in-theory (disable svexlist-overridekey-transparent-p-necc)))))



  (local
   (defthm svex-alist-overridekey-transparent-p-decompose-by-keys
     (implies (svex-alist-overridekey-transparent-p x (append keys1 keys2) subst)
              (svex-alist-overridekey-transparent-p x keys1 subst))
     :hints (("goal" :do-not-induct t
              :expand ((:with svex-alist-overridekey-transparent-p
                        (svex-alist-overridekey-transparent-p x keys1 subst)))
              :use ((:instance overridekeys-envs-agree-of-append
                     (keys1 keys1)
                     (keys2 keys2)
                     (values (svex-alist-eval subst (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x keys1 subst))))
                     (env3 (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x keys1 subst)))
                     (env2 (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x keys1 subst)))
                     (env1 (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x keys1 subst))))
                    (:instance svex-alist-overridekey-transparent-p-necc
                     (overridekeys (append keys1 keys2))
                     (impl-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness x keys1 subst)))
                     (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness x keys1 subst)))))
              :in-theory (disable overridekeys-envs-agree-of-append)))))

  (local (defthm append-set-diff-under-set-equiv-when-subsetp
           (implies (subsetp-equal a b)
                    (set-equiv (append a (set-difference-equal b a))
                               b))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))
  
  (defthm svex-alist-overridekey-transparent-p-when-subsetp
    (implies (And (svex-alist-overridekey-transparent-p x keys1 subst)
                  (subsetp-equal (svarlist-fix keys2) (svarlist-fix keys1)))
             (svex-alist-overridekey-transparent-p x keys2 subst))
    :hints (("goal" :use ((:instance svex-alist-overridekey-transparent-p-decompose-by-keys
                           (keys1 (svarlist-fix keys2))
                           (keys2 (set-difference-equal (svarlist-fix keys1) (svarlist-fix keys2)))))
             :in-theory (disable svex-alist-overridekey-transparent-p-decompose-by-keys
                                 SVEX-ALIST-OVERRIDEKEY-TRANSPARENT-P-SVARLIST-EQUIV-CONGRUENCE-ON-OVERRIDEKEYS))))


  (defthm svex-alist-overridekey-transparent-p-by-decomp
    (implies (and (svex-alist-overridekey-transparent-p x keys1 subst)
                  (svex-alist-overridekey-transparent-p subst keys1 subst)
                  (svex-alist-overridekey-transparent-p x keys2 subst))
             (svex-alist-overridekey-transparent-p x (append keys1 keys2) subst))
    :hints ((b* ((witness '(svex-alist-overridekey-transparent-p-witness
                            x (append keys1 keys2) subst))
                 (impl-env `(mv-nth 0 ,witness))
                 (spec-env `(mv-nth 1 ,witness))
                 (mid `(append (svex-env-extract
                                (overridekeys->override-vars keys1) ,impl-env)
                               ,spec-env)))
              `(:do-not-induct t
                :expand ((:with svex-alist-overridekey-transparent-p
                          (svex-alist-overridekey-transparent-p x (append keys1 keys2) subst)))
                :use ((:instance svex-alist-overridekey-transparent-p-necc
                       (overridekeys keys1)
                       (impl-env ,mid)
                       (spec-env ,spec-env))
                      (:instance svex-alist-overridekey-transparent-p-necc
                       (x subst)
                       (overridekeys keys1)
                       (impl-env ,mid)
                       (spec-env ,spec-env))
                      (:instance svex-alist-overridekey-transparent-p-necc
                       (overridekeys keys2)
                       (impl-env ,impl-env)
                       (spec-env ,mid)))
                :in-theory (disable svex-alist-overridekey-transparent-p-necc))))))

