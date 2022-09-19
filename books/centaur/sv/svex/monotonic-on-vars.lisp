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

(include-book "partial-monotonicity")

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "alist-thms"))

(local (std::add-default-post-define-hook :fix))

(local (defthm consp-hons-assoc-equal
         (iff (consp (hons-assoc-equal k x))
              (hons-assoc-equal k x))))

(local
 (defthmd member-alist-keys
   (iff (member-equal k (alist-keys x))
        (hons-assoc-equal k x))
   :hints(("Goal" :in-theory (enable alist-keys)))))

(local
 (defthm member-svex-env-keys
   (implies (and (svex-env-p x)
                 (svar-p k))
            (iff (member-equal k (alist-keys x))
                 (svex-env-boundp k x)))
   :hints(("Goal" :in-theory (enable svex-env-boundp
                                     member-alist-keys)))))

;; (local
;;  (defthm intersectp-of-svex-env-removekeys
;;    (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-removekeys vars env))))
;;    :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

;; (local
;;  (defthm append-removekeys-under-svex-envs-similar
;;    (svex-envs-similar (append (svex-env-removekeys vars env) env)
;;                       env)
;;    :hints(("Goal" :in-theory (enable svex-envs-similar)))))


(defcong set-equiv equal (svex-envs-agree-except vars env1 env2) 1
  :hints (("goal" :cases ((svex-envs-agree-except vars env1 env2)))
          (and stable-under-simplificationp
               (b* ((lit (assoc 'svex-envs-agree-except clause))
                    (?wit `(svex-envs-agree-except-witness . ,(cdr lit)))
                    (?other (if (eq (cadr lit) 'vars) 'vars-equiv 'vars)))
                 `(:expand ((:with svex-envs-agree-except-by-witness ,lit))
                   :use ((:instance svex-envs-agree-except-implies
                          (vars ,other)
                          (var ,wit) (x env1) (y env2))))))))

(defsection svex-monotonic-on-vars
  :parents (4vec-<<=)
  (defun-sk svex-monotonic-on-vars (vars x)
    (forall (env1 env2)
            (implies (and (svex-env-<<= env1 env2)
                          (svex-envs-agree-except vars env1 env2))
                     (4vec-<<= (svex-eval x env1) (svex-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svex-monotonic-on-vars
                      svex-monotonic-on-vars-necc))

  
  (fty::deffixcong svarlist-equiv equal (svex-monotonic-on-vars vars x) vars
    :hints (("goal" :cases ((svex-monotonic-on-vars vars x))
             :expand ((:free (vars) (svex-monotonic-on-vars vars x)))
             :use ((:instance svex-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness (svarlist-fix vars) x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness (svarlist-fix vars) x))))
                   (:instance svex-monotonic-on-vars-necc
                    (vars (svarlist-fix vars))
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x))))))))

  (defcong set-equiv equal (svex-monotonic-on-vars vars x) 1
    :hints (("goal" :cases ((svex-monotonic-on-vars vars x))
             :expand ((:free (vars) (svex-monotonic-on-vars vars x)))
             :use ((:instance svex-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars-equiv x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars-equiv x))))
                   (:instance svex-monotonic-on-vars-necc
                    (vars vars-equiv)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x))))))))

  (defcong svex-eval-equiv equal (svex-monotonic-on-vars vars x) 2
    :hints (("goal" :cases ((svex-monotonic-on-vars vars x))
             :expand ((:free (x) (svex-monotonic-on-vars vars x)))
             :use ((:instance svex-monotonic-on-vars-necc
                    (x x-equiv)
                    (vars vars)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x))))
                   (:instance svex-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars x-equiv)))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars x-equiv)))))))))


(defsection svexlist-monotonic-on-vars
  :parents (4vec-<<=)
  (defun-sk svexlist-monotonic-on-vars (vars x)
    (forall (env1 env2)
            (implies (and (svex-env-<<= env1 env2)
                          (svex-envs-agree-except vars env1 env2))
                     (4veclist-<<= (svexlist-eval x env1) (svexlist-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svexlist-monotonic-on-vars
                      svexlist-monotonic-on-vars-necc))

  
  (fty::deffixcong svarlist-equiv equal (svexlist-monotonic-on-vars vars x) vars
    :hints (("goal" :cases ((svexlist-monotonic-on-vars vars x))
             :expand ((:free (vars) (svexlist-monotonic-on-vars vars x)))
             :use ((:instance svexlist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness (svarlist-fix vars) x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness (svarlist-fix vars) x))))
                   (:instance svexlist-monotonic-on-vars-necc
                    (vars (svarlist-fix vars))
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x))))))))

  (defcong set-equiv equal (svexlist-monotonic-on-vars vars x) 1
    :hints (("goal" :cases ((svexlist-monotonic-on-vars vars x))
             :expand ((:free (vars) (svexlist-monotonic-on-vars vars x)))
             :use ((:instance svexlist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars-equiv x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars-equiv x))))
                   (:instance svexlist-monotonic-on-vars-necc
                    (vars vars-equiv)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x))))))))

  (defcong svexlist-eval-equiv equal (svexlist-monotonic-on-vars vars x) 2
    :hints (("goal" :cases ((svexlist-monotonic-on-vars vars x))
             :expand ((:free (x) (svexlist-monotonic-on-vars vars x)))
             :use ((:instance svexlist-monotonic-on-vars-necc
                    (x x-equiv)
                    (vars vars)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x))))
                   (:instance svexlist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars x-equiv)))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars x-equiv)))))))))



(defsection svex-alist-monotonic-on-vars
  :parents (4vec-<<=)
  (defun-sk svex-alist-monotonic-on-vars (vars x)
    (forall (env1 env2)
            (implies (and (svex-env-<<= env1 env2)
                          (svex-envs-agree-except vars env1 env2))
                     (svex-env-<<= (svex-alist-eval x env1) (svex-alist-eval x env2))))
    :rewrite :direct)

  (in-theory (disable svex-alist-monotonic-on-vars
                      svex-alist-monotonic-on-vars-necc))

  
  (fty::deffixcong svarlist-equiv equal (svex-alist-monotonic-on-vars vars x) vars
    :hints (("goal" :cases ((svex-alist-monotonic-on-vars vars x))
             :expand ((:free (vars) (svex-alist-monotonic-on-vars vars x)))
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness (svarlist-fix vars) x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness (svarlist-fix vars) x))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (vars (svarlist-fix vars))
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x))))))))

  (defcong set-equiv equal (svex-alist-monotonic-on-vars vars x) 1
    :hints (("goal" :cases ((svex-alist-monotonic-on-vars vars x))
             :expand ((:free (vars) (svex-alist-monotonic-on-vars vars x)))
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars-equiv x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars-equiv x))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (vars vars-equiv)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x))))))))

  (defcong svex-alist-eval-equiv equal (svex-alist-monotonic-on-vars vars x) 2
    :hints (("goal" :cases ((svex-alist-monotonic-on-vars vars x))
             :expand ((:free (x) (svex-alist-monotonic-on-vars vars x)))
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (x x-equiv)
                    (vars vars)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (vars vars)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars x-equiv)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars x-equiv))))))))


  (defthm lookup-when-svex-alist-monotonic-on-vars
    (implies (svex-alist-monotonic-on-vars vars x)
             (svex-monotonic-on-vars vars (svex-lookup k x)))
    :hints (("goal" :expand ((svex-monotonic-on-vars vars (svex-lookup k x))
                             (svex-monotonic-on-vars vars nil))
             :use ((:instance svex-env-<<=-necc
                    (x (svex-alist-eval x (mv-nth 0 (svex-monotonic-on-vars-witness vars (svex-lookup k x)))))
                    (y (svex-alist-eval x (mv-nth 1 (svex-monotonic-on-vars-witness vars (svex-lookup k x)))))
                    (var k))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars (svex-lookup k x))))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars (svex-lookup k x)))))))))

  (defthm svex-compose-lookup-when-svex-alist-monotonic-on-vars
    (implies (svex-alist-monotonic-on-vars vars x)
             (svex-monotonic-on-vars vars (svex-compose-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-compose-lookup)
            :expand ((svex-monotonic-on-vars vars (svex-var k))
                     (:free (env) (svex-eval (svex-var k) env))))))

  (local (defthm append-extract-superset-under-svex-envs-similar
           (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
                    (svex-envs-similar (append (svex-env-extract vars z) x y)
                                       (append (svex-env-extract vars z) y)))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))
  
  (local (defthm svex-envs-agree-except-append-subset-1
           (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
                    (equal (svex-envs-agree-except vars (append x y) z)
                           (svex-envs-agree-except vars y z)))
           :hints(("Goal" :in-theory (enable svex-envs-agree-except)))))


  (local (defthm svex-envs-agree-except-append-subset-2
           (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix vars))
                    (equal (svex-envs-agree-except vars z (append x y))
                           (svex-envs-agree-except vars z y)))
           :hints(("Goal" 
                   :use ((:instance svex-envs-agree-except-commutative
                          (x z) (y (append x y)))
                         (:instance svex-envs-agree-except-commutative
                          (x (append x y)) (y z))
                         (:instance svex-envs-agree-except-commutative
                          (x z) (y y))
                         (:instance svex-envs-agree-except-commutative
                          (x y) (y z)))))))

  (defthm svex-compose-preserves-svex-monotonic-on-vars
    (implies (and (svex-monotonic-on-vars vars x)
                  (svex-alist-monotonic-on-vars vars a)
                  (subsetp-equal (svex-alist-keys a) (svarlist-fix vars)))
             (svex-monotonic-on-vars vars (svex-compose x a)))
    :hints (("Goal" :expand ((:with svex-monotonic-on-vars
                              (svex-monotonic-on-vars vars
                                                      (svex-compose x a))))
             :use ((:instance svex-monotonic-on-vars-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-monotonic-on-vars-witness vars (svex-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-monotonic-on-vars-witness vars (svex-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-monotonic-on-vars-witness vars (svex-compose x a))))
                    (env2 (mv-nth 1 (svex-monotonic-on-vars-witness vars (svex-compose x a))))))
             :do-not-induct t))
    :otf-flg t)

  (defthm svexlist-compose-preserves-svexlist-monotonic-on-vars
    (implies (and (svexlist-monotonic-on-vars vars x)
                  (svex-alist-monotonic-on-vars vars a)
                  (subsetp-equal (svex-alist-keys a) (svarlist-fix vars)))
             (svexlist-monotonic-on-vars vars (svexlist-compose x a)))
    :hints (("Goal" :expand ((:with svexlist-monotonic-on-vars
                              (svexlist-monotonic-on-vars vars
                                                      (svexlist-compose x a))))
             :use ((:instance svexlist-monotonic-on-vars-necc
                    (env1 (let ((w1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars (svexlist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars (svexlist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (x a)
                    (env1 (mv-nth 0 (svexlist-monotonic-on-vars-witness vars (svexlist-compose x a))))
                    (env2 (mv-nth 1 (svexlist-monotonic-on-vars-witness vars (svexlist-compose x a))))))
             :do-not-induct t))
    :otf-flg t)


  (defthm svex-alist-compose-preserves-svex-alist-monotonic-on-vars
    (implies (and (svex-alist-monotonic-on-vars vars x)
                  (svex-alist-monotonic-on-vars vars a)
                  (subsetp-equal (svex-alist-keys a) (svarlist-fix vars)))
             (svex-alist-monotonic-on-vars vars (svex-alist-compose x a)))
    :hints (("Goal" :expand ((:with svex-alist-monotonic-on-vars
                              (svex-alist-monotonic-on-vars vars
                                                      (svex-alist-compose x a))))
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (env1 (let ((w1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w1) w1)))
                    (env2 (let ((w2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars (svex-alist-compose x a)))))
                            (append (svex-alist-eval a w2) w2))))
                   (:instance svex-alist-monotonic-on-vars-necc
                    (x a)
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars (svex-alist-compose x a))))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars (svex-alist-compose x a))))))
             :do-not-induct t))
    :otf-flg t))





