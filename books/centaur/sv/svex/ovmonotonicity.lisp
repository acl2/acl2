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

(include-book "svex-lattice")
(include-book "override-mux")

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "alist-thms"))

(local (std::add-default-post-define-hook :fix))




(define svex-env-ov<<= ((x svex-env-p) (y svex-env-p))
  (and (ec-call
        (svex-env-<<= (svex-env-remove-override x :test)
                      (svex-env-remove-override y :test)))
       (ec-call
        (svex-envs-1mask-equiv (svex-env-filter-override x :test)
                               (svex-env-filter-override y :test))))
  ///
  (defthmd svex-env-ov<<=-necc
    (implies (svex-env-ov<<= x y)
             (and (implies (svar-override-p v :test)
                           (4vec-1mask-equiv (svex-env-lookup v x)
                                             (svex-env-lookup v y)))
                  (implies (not (svar-override-p v :test))
                           (4vec-<<= (svex-env-lookup v x)
                                     (svex-env-lookup v y)))))
    :hints (("goal" :use ((:instance svex-envs-1mask-equiv-necc
                           (k v)
                           (x (svex-env-filter-override x :test))
                           (y (svex-env-filter-override y :test)))
                          (:instance svex-env-<<=-necc
                           (var v)
                           (x (svex-env-remove-override x :test))
                           (y (svex-env-remove-override y :test))))
             :in-theory (disable svex-envs-1mask-equiv-implies-4vec-1mask-equiv-svex-env-lookup-2))))

  (defcong svex-envs-similar equal (svex-env-ov<<= x y) 1)
  (defcong svex-envs-similar equal (svex-env-ov<<= x y) 2)

  (defthm svex-env-ov<<=-self
    (svex-env-ov<<= x x)))

(define svex-env-ov<<=-witness ((x svex-env-p) (y svex-env-p))
  (if (ec-call (svex-env-<<= (svex-env-remove-override x :test)
                             (svex-env-remove-override y :test)))
      (ec-call (svex-envs-1mask-equiv-witness (svex-env-filter-override x :test)
                                              (svex-env-filter-override y :test)))
    (ec-call (svex-env-<<=-witness (svex-env-remove-override x :test)
                                   (svex-env-remove-override y :test))))
  ///
  (defthmd svex-env-ov<<=-by-witness
    (equal (svex-env-ov<<= x y)
           (let ((v (svex-env-ov<<=-witness x y)))
             (and (implies (svar-override-p v :test)
                           (4vec-1mask-equiv (svex-env-lookup v x)
                                             (svex-env-lookup v y)))
                  (implies (not (svar-override-p v :test))
                           (4vec-<<= (svex-env-lookup v x)
                                     (svex-env-lookup v y))))))
    :hints(("Goal" :in-theory (enable svex-env-ov<<=
                                      svex-env-<<=
                                      svex-envs-1mask-equiv
                                      svex-env-ov<<=-necc)))
    :rule-classes :definition))




(defsection svex-ovmonotonic
  :parents (4vec-<<=)
  (defun-sk svex-ovmonotonic (x)
    (forall (env1 env2)
            (implies (svex-env-ov<<= env1 env2)
                     (4vec-<<= (svex-eval x env1) (svex-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svex-ovmonotonic
                      svex-ovmonotonic-necc))

  (defcong svex-eval-equiv equal (svex-ovmonotonic x) 1
    :hints (("goal" :cases ((svex-ovmonotonic x))
             :expand ((:free (x) (svex-ovmonotonic x)))
             :use ((:instance svex-ovmonotonic-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svex-ovmonotonic-witness x)))
                    (env2 (mv-nth 1 (svex-ovmonotonic-witness x))))
                   (:instance svex-ovmonotonic-necc
                    (env1 (mv-nth 0 (svex-ovmonotonic-witness x-equiv)))
                    (env2 (mv-nth 1 (svex-ovmonotonic-witness x-equiv)))))))))


(defsection svexlist-ovmonotonic
  :parents (4vec-<<=)
  (defun-sk svexlist-ovmonotonic (x)
    (forall (env1 env2)
            (implies (svex-env-ov<<= env1 env2)
                     (4veclist-<<= (svexlist-eval x env1) (svexlist-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svexlist-ovmonotonic
                      svexlist-ovmonotonic-necc))


  (defcong svexlist-eval-equiv equal (svexlist-ovmonotonic x) 1
    :hints (("goal" :cases ((svexlist-ovmonotonic x))
             :expand ((:free (x) (svexlist-ovmonotonic x)))
             :use ((:instance svexlist-ovmonotonic-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svexlist-ovmonotonic-witness x)))
                    (env2 (mv-nth 1 (svexlist-ovmonotonic-witness x))))
                   (:instance svexlist-ovmonotonic-necc
                    (env1 (mv-nth 0 (svexlist-ovmonotonic-witness x-equiv)))
                    (env2 (mv-nth 1 (svexlist-ovmonotonic-witness x-equiv)))))))))



(defsection svex-alist-ovmonotonic
  :parents (4vec-<<=)
  (defun-sk svex-alist-ovmonotonic (x)
    (forall (env1 env2)
            (implies (svex-env-ov<<= env1 env2)
                     (svex-env-<<= (svex-alist-eval x env1) (svex-alist-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svex-alist-ovmonotonic
                      svex-alist-ovmonotonic-necc))

  

  (defcong svex-alist-eval-equiv equal (svex-alist-ovmonotonic x) 1
    :hints (("goal" :cases ((svex-alist-ovmonotonic x))
             :expand ((:free (x) (svex-alist-ovmonotonic x)))
             :use ((:instance svex-alist-ovmonotonic-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svex-alist-ovmonotonic-witness x)))
                    (env2 (mv-nth 1 (svex-alist-ovmonotonic-witness x))))
                   (:instance svex-alist-ovmonotonic-necc
                    (env1 (mv-nth 0 (svex-alist-ovmonotonic-witness x-equiv)))
                    (env2 (mv-nth 1 (svex-alist-ovmonotonic-witness x-equiv))))))))


  (defthm lookup-when-svex-alist-ovmonotonic
    (implies (svex-alist-ovmonotonic x)
             (svex-ovmonotonic (svex-lookup k x)))
    :hints (("goal" :expand ((svex-ovmonotonic (svex-lookup k x))
                             (svex-ovmonotonic nil))
             :use ((:instance svex-env-<<=-necc
                    (x (svex-alist-eval x (mv-nth 0 (svex-ovmonotonic-witness (svex-lookup k x)))))
                    (y (svex-alist-eval x (mv-nth 1 (svex-ovmonotonic-witness (svex-lookup k x)))))
                    (var k))
                   (:instance svex-alist-ovmonotonic-necc
                    (env1 (mv-nth 0 (svex-ovmonotonic-witness (svex-lookup k x))))
                    (env2 (mv-nth 1 (svex-ovmonotonic-witness (svex-lookup k x)))))))))

  (defthm svex-compose-lookup-when-svex-alist-ovmonotonic
    (implies (and (svex-alist-ovmonotonic x)
                  (not (svar-override-p k :test)))
             (svex-ovmonotonic (svex-compose-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-compose-lookup
                                      svex-env-ov<<=-necc)
            :expand ((svex-ovmonotonic (svex-var k))
                     (:free (env) (svex-eval (svex-var k) env))))))

  ;; (local (defthm append-extract-superset-under-svex-envs-similar
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (svex-envs-similar (append (svex-env-extract z) x y)
  ;;                                      (append (svex-env-extract z) y)))
  ;;          :hints(("Goal" :in-theory (enable svex-envs-similar)))))
  
  ;; (local (defthm svex-envs-agree-except-append-subset-1
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (equal (svex-envs-agree-except (append x y) z)
  ;;                          (svex-envs-agree-except y z)))
  ;;          :hints(("Goal" :in-theory (enable svex-envs-agree-except)))))


  ;; (local (defthm svex-envs-agree-except-append-subset-2
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (equal (svex-envs-agree-except z (append x y))
  ;;                          (svex-envs-agree-except z y)))
  ;;          :hints(("Goal" 
  ;;                  :use ((:instance svex-envs-agree-except-commutative
  ;;                         (x z) (y (append x y)))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x (append x y)) (y z))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x z) (y y))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x y) (y z)))))))

  (local (defthm member-equal-when-nonoverride-p
           (implies (and (svar-override-p v type)
                         (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-fix v) x)))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p)))))
  
  (defthm svex-env-ov<<=-of-append-<<=
    (implies (And (svex-env-ov<<= c d)
                  (svex-env-<<= a b)
                  (set-equiv (alist-keys (svex-env-fix a))
                             (alist-keys (svex-env-fix b)))
                  (svarlist-nonoverride-p (alist-keys (svex-env-fix a)) :test))
             (svex-env-ov<<= (append a c) (append b d)))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (witness `(svex-env-ov<<=-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-env-<<=-necc (x a) (y b)
                            (var ,witness))
                           (:instance svex-env-ov<<=-necc (x c) (y d)
                            (v ,witness)))
                     :in-theory (enable svex-env-boundp-iff-member-alist-keys))))))
  
  (defthm svex-compose-preserves-svex-ovmonotonic
    (implies (and (svex-ovmonotonic x)
                  (svex-alist-ovmonotonic a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  )
             (svex-ovmonotonic (svex-compose x a)))
    :hints (("Goal" :expand ((:with svex-ovmonotonic
                              (svex-ovmonotonic (svex-compose x a))))
             :use ((:instance svex-ovmonotonic-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-ovmonotonic-witness (svex-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-ovmonotonic-witness (svex-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovmonotonic-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-ovmonotonic-witness (svex-compose x a))))
                    (env2 (mv-nth 1 (svex-ovmonotonic-witness (svex-compose x a))))))
             :do-not-induct t))
    :otf-flg t)

  (defthm svexlist-compose-preserves-svexlist-ovmonotonic
    (implies (and (svexlist-ovmonotonic x)
                  (svex-alist-ovmonotonic a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  )
             (svexlist-ovmonotonic (svexlist-compose x a)))
    :hints (("Goal" :expand ((:with svexlist-ovmonotonic
                              (svexlist-ovmonotonic (svexlist-compose x a))))
             :use ((:instance svexlist-ovmonotonic-necc
                    (env1 (let ((w1 (mv-nth 0 (svexlist-ovmonotonic-witness (svexlist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svexlist-ovmonotonic-witness (svexlist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovmonotonic-necc
                    (x a)
                    (env1 (mv-nth 0 (svexlist-ovmonotonic-witness (svexlist-compose x a))))
                    (env2 (mv-nth 1 (svexlist-ovmonotonic-witness (svexlist-compose x a))))))
             :do-not-induct t))
    :otf-flg t)

  (defthm svex-alist-compose-preserves-svex-alist-ovmonotonic
    (implies (and (svex-alist-ovmonotonic x)
                  (svex-alist-ovmonotonic a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  )
             (svex-alist-ovmonotonic (svex-alist-compose x a)))
    :hints (("Goal" :expand ((:with svex-alist-ovmonotonic
                              (svex-alist-ovmonotonic (svex-alist-compose x a))))
             :use ((:instance svex-alist-ovmonotonic-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-alist-ovmonotonic-witness (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-alist-ovmonotonic-witness (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovmonotonic-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-alist-ovmonotonic-witness (svex-alist-compose x a))))
                    (env2 (mv-nth 1 (svex-alist-ovmonotonic-witness (svex-alist-compose x a))))))
             :do-not-induct t))
    :otf-flg t))



(defsection svex-envs-ovsimilar
  (defun-sk svex-envs-ovsimilar (x y)
    (forall v
            (and (implies (and (not (svar-override-p v :test))
                               (not (svar-override-p v :val)))
                          (equal (svex-env-lookup v x) (svex-env-lookup v y)))
                 (implies (svar-override-p v :test)
                          (4vec-1mask-equiv (svex-env-lookup v x) (svex-env-lookup v y)))
                 (implies (svar-override-p v :val)
                          (equal (4vec-bit?! (svex-env-lookup (svar-change-override v :test) y)
                                             (svex-env-lookup v x)
                                             0)
                                 (4vec-bit?! (svex-env-lookup (svar-change-override v :test) y)
                                             (svex-env-lookup v y)
                                             0)))))
    :rewrite :direct)

  (in-theory (disable svex-envs-ovsimilar-necc
                      svex-envs-ovsimilar))

  (defequiv svex-envs-ovsimilar
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svar-override-p-when-other
                                      svex-envs-ovsimilar-necc)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svar-override-p-when-other)
                   :use ((:instance svex-envs-ovsimilar-necc
                          (v (svex-envs-ovsimilar-witness x z)))
                         (:instance svex-envs-ovsimilar-necc (x y) (y z)
                          (v (svex-envs-ovsimilar-witness x z)))
                         (:instance svex-envs-ovsimilar-necc (x y) (y z)
                          (v (svar-change-override (svex-envs-ovsimilar-witness x z) :test))))))))
  
  (defrefinement svex-envs-similar svex-envs-ovsimilar
    :hints(("Goal" :in-theory (enable svex-envs-ovsimilar)))))


;; (define svex-envs-ovsimilar ((x svex-env-p) (y svex-env-p))
;;   (and (ec-call
;;         (svex-envs-similar (svex-env-remove-override x :test)
;;                            (svex-env-remove-override y :test)))
;;        (ec-call
;;         (svex-envs-1mask-equiv (svex-env-filter-override x :test)
;;                                (svex-env-filter-override y :test))))
;;   ///
;;   (defequiv svex-envs-ovsimilar)
  
;;   (defthmd svex-envs-ovsimilar-necc
;;     (implies (svex-envs-ovsimilar x y)
;;              (and (implies (svar-override-p v :test)
;;                            (equal (4vec-1mask-equiv (svex-env-lookup v x)
;;                                                     (svex-env-lookup v y))
;;                                   t))
;;                   (implies (not (svar-override-p v :test))
;;                            (equal (equal (svex-env-lookup v x)
;;                                          (svex-env-lookup v y))
;;                                   t))))
;;     :hints (("goal" :use ((:instance svex-envs-1mask-equiv-necc
;;                            (k v)
;;                            (x (svex-env-filter-override x :test))
;;                            (y (svex-env-filter-override y :test)))
;;                           (:instance svex-envs-similar-necc
;;                            (k v)
;;                            (x (svex-env-remove-override x :test))
;;                            (y (svex-env-remove-override y :test))))
;;              :in-theory (disable svex-envs-similar-implies-equal-svex-env-lookup-2
;;                                  svex-envs-1mask-equiv-implies-4vec-1mask-equiv-svex-env-lookup-2))))

;;   (defrefinement svex-envs-similar svex-envs-ovsimilar)

;;   (defthm svex-envs-ovsimilar-self
;;     (svex-envs-ovsimilar x x))

;;   (defcong svex-envs-ovsimilar equal (svex-env-ov<<= x y) 1
;;     :hints(("Goal" :in-theory (enable svex-env-ov<<=))))

;;   (defcong svex-envs-ovsimilar equal (svex-env-ov<<= x y) 2
;;     :hints(("Goal" :in-theory (enable svex-env-ov<<=))))

;;   ;; (defthmd equal-of-4vecs-when-<<=
;;   ;;   (implies (4vec-<<= x y)
;;   ;;            (iff (4vec-<<= y x)
;;   ;;                 (4vec-equiv x y)))
;;   ;;   :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-fix))))
  
;;   (defthmd svex-envs-similar-when-<<=
;;     (implies (svex-env-<<= x y)
;;              (iff (svex-env-<<= y x)
;;                   (svex-envs-similar x y)))
;;     :hints((and stable-under-simplificationp
;;                 '(:in-theory (e/d (svex-envs-similar
;;                                    4VEC-<<=-ASYMM)
;;                                   (svex-env-<<=-necc))
;;                   :use ((:instance svex-env-<<=-necc
;;                          (var (svex-envs-similar-witness x y)))
;;                         (:instance svex-env-<<=-necc
;;                          (var (svex-envs-similar-witness x y)) (x y) (y x)))))))
  
;;   (defthmd svex-envs-ovsimilar-when-ov<<=
;;     (implies (svex-env-ov<<= x y)
;;              (iff (svex-env-ov<<= y x)
;;                   (svex-envs-ovsimilar x y)))
;;     :hints(("Goal" :in-theory (enable svex-env-ov<<=
;;                                       svex-envs-similar-when-<<=)))))

;; (define svex-envs-ovsimilar-witness ((x svex-env-p) (y svex-env-p))
;;   (if (ec-call (svex-envs-similar (svex-env-remove-override x :test)
;;                                   (svex-env-remove-override y :test)))
;;       (ec-call (svex-envs-1mask-equiv-witness (svex-env-filter-override x :test)
;;                                               (svex-env-filter-override y :test)))
;;     (ec-call (svex-envs-similar-witness (svex-env-remove-override x :test)
;;                                         (svex-env-remove-override y :test))))
;;   ///
;;   (defthmd svex-envs-ovsimilar-by-witness
;;     (equal (svex-envs-ovsimilar x y)
;;            (let ((v (svex-envs-ovsimilar-witness x y)))
;;              (and (implies (svar-override-p v :test)
;;                            (4vec-1mask-equiv (svex-env-lookup v x)
;;                                              (svex-env-lookup v y)))
;;                   (implies (not (svar-override-p v :test))
;;                            (equal (svex-env-lookup v x)
;;                                   (svex-env-lookup v y))))))
;;     :hints(("Goal" :in-theory (enable svex-envs-ovsimilar
;;                                       svex-envs-similar
;;                                       svex-envs-1mask-equiv
;;                                       svex-envs-ovsimilar-necc)))
;;     :rule-classes :definition))


(defsection svex-ovcongruent
  (defun-sk svex-ovcongruent (x)
    (forall (env1 env2)
            (implies (svex-envs-ovsimilar env1 env2)
                     (equal (Equal (svex-eval x env1) (svex-eval x env2))
                            t)))
    :rewrite :direct)

  (in-theory (disable svex-ovcongruent
                      svex-ovcongruent-necc))

  (defcong svex-eval-equiv equal (svex-ovcongruent x) 1
    :hints (("goal" :cases ((svex-ovcongruent x))
             :expand ((:free (x) (svex-ovcongruent x)))
             :use ((:instance svex-ovcongruent-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svex-ovcongruent-witness x)))
                    (env2 (mv-nth 1 (svex-ovcongruent-witness x))))
                   (:instance svex-ovcongruent-necc
                    (env1 (mv-nth 0 (svex-ovcongruent-witness x-equiv)))
                    (env2 (mv-nth 1 (svex-ovcongruent-witness x-equiv)))))))))


(defsection svexlist-ovcongruent
  :parents (4vec-<<=)
  (defun-sk svexlist-ovcongruent (x)
    (forall (env1 env2)
            (implies (svex-envs-ovsimilar env1 env2)
                     (equal (equal (svexlist-eval x env1) (svexlist-eval x env2)) t)))
    :rewrite :direct)

  (in-theory (disable svexlist-ovcongruent
                      svexlist-ovcongruent-necc))


  (defcong svexlist-eval-equiv equal (svexlist-ovcongruent x) 1
    :hints (("goal" :cases ((svexlist-ovcongruent x))
             :expand ((:free (x) (svexlist-ovcongruent x)))
             :use ((:instance svexlist-ovcongruent-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svexlist-ovcongruent-witness x)))
                    (env2 (mv-nth 1 (svexlist-ovcongruent-witness x))))
                   (:instance svexlist-ovcongruent-necc
                    (env1 (mv-nth 0 (svexlist-ovcongruent-witness x-equiv)))
                    (env2 (mv-nth 1 (svexlist-ovcongruent-witness x-equiv)))))))))



(defsection svex-alist-ovcongruent
  :parents (4vec-<<=)
  (defun-sk svex-alist-ovcongruent (x)
    (forall (env1 env2)
            (implies (svex-envs-ovsimilar env1 env2)
                     (equal (svex-envs-equivalent (svex-alist-eval x env1) (svex-alist-eval x env2))
                            t)))
    :rewrite :direct)

  (in-theory (disable svex-alist-ovcongruent
                      svex-alist-ovcongruent-necc))

  

  (defcong svex-alist-eval-equiv equal (svex-alist-ovcongruent x) 1
    :hints (("goal" :cases ((svex-alist-ovcongruent x))
             :expand ((:free (x) (svex-alist-ovcongruent x)))
             :use ((:instance svex-alist-ovcongruent-necc
                    (x x-equiv)
                    (env1 (mv-nth 0 (svex-alist-ovcongruent-witness x)))
                    (env2 (mv-nth 1 (svex-alist-ovcongruent-witness x))))
                   (:instance svex-alist-ovcongruent-necc
                    (env1 (mv-nth 0 (svex-alist-ovcongruent-witness x-equiv)))
                    (env2 (mv-nth 1 (svex-alist-ovcongruent-witness x-equiv))))))))


  (defthm lookup-when-svex-alist-ovcongruent
    (implies (svex-alist-ovcongruent x)
             (svex-ovcongruent (svex-lookup k x)))
    :hints (("goal" :expand ((svex-ovcongruent (svex-lookup k x))
                             (svex-ovcongruent nil))
             :use ((:instance svex-envs-equivalent-necc
                    (x (svex-alist-eval x (mv-nth 0 (svex-ovcongruent-witness (svex-lookup k x)))))
                    (y (svex-alist-eval x (mv-nth 1 (svex-ovcongruent-witness (svex-lookup k x)))))
                    (k k))
                   (:instance svex-alist-ovcongruent-necc
                    (env1 (mv-nth 0 (svex-ovcongruent-witness (svex-lookup k x))))
                    (env2 (mv-nth 1 (svex-ovcongruent-witness (svex-lookup k x)))))))))

  (defthm svex-compose-lookup-when-svex-alist-ovcongruent
    (implies (and (svex-alist-ovcongruent x)
                  (not (svar-override-p k :test))
                  (not (svar-override-p k :val)))
             (svex-ovcongruent (svex-compose-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-compose-lookup)
            :expand ((svex-ovcongruent (svex-var k))
                     (:free (env) (svex-eval (svex-var k) env)))
            :use ((:instance svex-envs-ovsimilar-necc
                   (x (mv-nth 0 (svex-ovcongruent-witness (svex-var k))))
                   (y (mv-nth 1 (svex-ovcongruent-witness (svex-var k))))
                   (v k))))))

  ;; (local (defthm append-extract-superset-under-svex-envs-similar
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (svex-envs-similar (append (svex-env-extract z) x y)
  ;;                                      (append (svex-env-extract z) y)))
  ;;          :hints(("Goal" :in-theory (enable svex-envs-similar)))))
  
  ;; (local (defthm svex-envs-agree-except-append-subset-1
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (equal (svex-envs-agree-except (append x y) z)
  ;;                          (svex-envs-agree-except y z)))
  ;;          :hints(("Goal" :in-theory (enable svex-envs-agree-except)))))


  ;; (local (defthm svex-envs-agree-except-append-subset-2
  ;;          (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
  ;;                   (equal (svex-envs-agree-except z (append x y))
  ;;                          (svex-envs-agree-except z y)))
  ;;          :hints(("Goal" 
  ;;                  :use ((:instance svex-envs-agree-except-commutative
  ;;                         (x z) (y (append x y)))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x (append x y)) (y z))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x z) (y y))
  ;;                        (:instance svex-envs-agree-except-commutative
  ;;                         (x y) (y z)))))))

  (local (defthm member-equal-when-nonoverride-p
           (implies (and (svar-override-p v type)
                         (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-fix v) x)))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p)))))

  (local (defthm member-equal-svar-change-override-when-nonoverride-p
           (implies (and (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-change-override v type) x)))
           :hints (("goal" :use ((:instance member-equal-when-nonoverride-p
                                  (v (svar-change-override v type))))
                    :in-theory (disable member-equal-when-nonoverride-p)))))
  
  (local
   (defthm svex-envs-ovsimilar-of-append
    (implies (And (svex-envs-ovsimilar c d)
                  (svarlist-nonoverride-p (alist-keys (svex-env-fix a)) :test)
                  (svarlist-nonoverride-p (alist-keys (svex-env-fix a)) :val))
             (equal (svex-envs-ovsimilar (append a c) (append a d))
                    t))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (witness `(svex-envs-ovsimilar-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovsimilar-necc (x c) (y d)
                            (v ,witness))
                           (:instance svex-envs-ovsimilar-necc (x c) (y d)
                            (v (svar-change-override ,witness :test))))
                     :in-theory (enable svex-env-boundp-iff-member-alist-keys
                                        member-when-not-svar-override-p)
                     :do-not-induct t))))))
  
  (defthm svex-compose-preserves-svex-ovcongruent
    (implies (and (svex-ovcongruent x)
                  (svex-alist-ovcongruent a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  (svarlist-nonoverride-p (svex-alist-keys a) :val)
                  )
             (svex-ovcongruent (svex-compose x a)))
    :hints (("Goal" :expand ((:with svex-ovcongruent
                              (svex-ovcongruent (svex-compose x a))))
             :use ((:instance svex-ovcongruent-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-ovcongruent-witness (svex-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-ovcongruent-witness (svex-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovcongruent-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-ovcongruent-witness (svex-compose x a))))
                    (env2 (mv-nth 1 (svex-ovcongruent-witness (svex-compose x a))))))
             :do-not-induct t))
    :otf-flg t)

  (defthm svexlist-compose-preserves-svexlist-ovcongruent
    (implies (and (svexlist-ovcongruent x)
                  (svex-alist-ovcongruent a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  (svarlist-nonoverride-p (svex-alist-keys a) :val)
                  )
             (svexlist-ovcongruent (svexlist-compose x a)))
    :hints (("Goal" :expand ((:with svexlist-ovcongruent
                              (svexlist-ovcongruent (svexlist-compose x a))))
             :use ((:instance svexlist-ovcongruent-necc
                    (env1 (let ((w1 (mv-nth 0 (svexlist-ovcongruent-witness (svexlist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svexlist-ovcongruent-witness (svexlist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovcongruent-necc
                    (x a)
                    (env1 (mv-nth 0 (svexlist-ovcongruent-witness (svexlist-compose x a))))
                    (env2 (mv-nth 1 (svexlist-ovcongruent-witness (svexlist-compose x a))))))
             :do-not-induct t))
    :otf-flg t)

  (defthm svex-alist-compose-preserves-svex-alist-ovcongruent
    (implies (and (svex-alist-ovcongruent x)
                  (svex-alist-ovcongruent a)
                  (svarlist-nonoverride-p (svex-alist-keys a) :test)
                  (svarlist-nonoverride-p (svex-alist-keys a) :val)
                  )
             (svex-alist-ovcongruent (svex-alist-compose x a)))
    :hints (("Goal" :expand ((:with svex-alist-ovcongruent
                              (svex-alist-ovcongruent (svex-alist-compose x a))))
             :use ((:instance svex-alist-ovcongruent-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-alist-ovcongruent-witness (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-alist-ovcongruent-witness (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-ovcongruent-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-alist-ovcongruent-witness (svex-alist-compose x a))))
                    (env2 (mv-nth 1 (svex-alist-ovcongruent-witness (svex-alist-compose x a))))))
             :do-not-induct t))
    :otf-flg t))






