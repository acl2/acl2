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

(include-book "env-ops")
(include-book "alist-equiv")
(include-book "rewrite-base")
(local (include-book "std/lists/sets" :Dir :system))
(local (include-book "alist-thms"))
(local (std::add-default-post-define-hook :fix))

(local (defthm svex-envs-agree-of-cons-when-not-member
         (implies (not (member-equal v (svarlist-fix vars)))
                  (svex-envs-agree vars (cons (cons v val) env)
                                   env))
         :hints(("Goal" :in-theory (enable svex-envs-agree svarlist-fix svex-env-lookup)))))

(local (defthm svex-envs-similar-of-cons-same
         (svex-envs-similar (list* (cons var val1)
                                   (cons var val2)
                                   rest)
                            (cons (cons var val1) rest))
         :hints(("Goal" :in-theory (enable svex-envs-similar
                                           svex-env-lookup)))))

(local (defthm svex-envs-similar-of-cons-non-svar
         (implies (not (svar-p var))
                  (svex-envs-similar (list* (cons var val)
                                            rest)
                                     rest))
         :hints(("Goal" :in-theory (enable svex-envs-similar
                                           svex-env-lookup)))))


(defsection svex-depends-on
  (defun-sk svex-depends-on (var x)
    (exists env
            (not (equal (svex-eval x (cons (cons (svar-fix var) (4vec-x)) env))
                        (svex-eval x env)))))

  (in-theory (disable svex-depends-on-suff
                      svex-depends-on))



  (defcong svar-equiv equal (svex-depends-on var x) 1
    :hints (("goal" :cases ((svex-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svex-depends-on clause))
                      (other (sublis '((var . var-equiv) (var-equiv . var)) lit))
                      (w `(svex-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svex-depends-on-suff
                            (var ,(second lit))
                            (env ,w))))))))

  (defcong svex-eval-equiv equal (svex-depends-on var x) 2
    :hints (("goal" :cases ((svex-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svex-depends-on clause))
                      (other (sublis '((x . x-equiv) (x-equiv . x)) lit))
                      (w `(svex-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svex-depends-on-suff
                            (x ,(third lit))
                            (env ,w))))))))
  
  (defthm svex-not-depends-on-implies
    (implies (and (bind-free
                   (case-match var
                     (('svar-fix$inline v) `((v . ,v)))
                     (& `((v . ,var)))))
                  (equal (svar-fix v) var)
                  (not (svex-depends-on v x)))
             (equal (svex-eval x (cons (cons var val) env))
                    (svex-eval x env)))
    :hints (("goal" :use ((:instance svex-depends-on-suff
                           (env (cons (cons (svar-fix var) val) env)))
                          (:instance svex-depends-on-suff)))
            '(:cases ((svar-p var))
              :do-not-induct t))
    :otf-flg t)


  (local (defthm svex-evals-equal-when-envs-agree
           (implies (svex-envs-agree (svex-vars x) env1 env2)
                    (equal (equal (svex-eval x env1) (svex-eval x env2)) t))
           :hints(("Goal" :in-theory (enable svex-eval-when-envs-agree)))))
  
  (defthm svex-not-depends-on-when-not-member-vars
    (implies (not (member-equal (svar-fix var) (svex-vars x)))
             (not (svex-depends-on var x)))
    :hints (("goal" :expand ((svex-depends-on var x))))))


(defsection svexlist-depends-on
  (defun-sk svexlist-depends-on (var x)
    (exists env
            (not (equal (svexlist-eval x (cons (cons (svar-fix var) (4vec-x)) env))
                        (svexlist-eval x env)))))

  (in-theory (disable svexlist-depends-on-suff
                      svexlist-depends-on))
  
  (defcong svexlist-eval-equiv equal (svexlist-depends-on var x) 2
    :hints (("goal" :cases ((svexlist-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svexlist-depends-on clause))
                      (other (sublis '((x . x-equiv) (x-equiv . x)) lit))
                      (w `(svexlist-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svexlist-depends-on-suff
                            (x ,(third lit))
                            (env ,w))))))))

  (defcong svar-equiv equal (svexlist-depends-on var x) 1
    :hints (("goal" :cases ((svexlist-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svexlist-depends-on clause))
                      (other (sublis '((var . var-equiv) (var-equiv . var)) lit))
                      (w `(svexlist-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svexlist-depends-on-suff
                            (var ,(second lit))
                            (env ,w))))))))

  (defthm svexlist-not-depends-on-implies
    (implies (and (bind-free
                   (case-match var
                     (('svar-fix$inline v) `((v . ,v)))
                     (& `((v . ,var)))))
                  (equal (svar-fix v) var)
                  (not (svexlist-depends-on v x)))
             (equal (svexlist-eval x (cons (cons var val) env))
                    (svexlist-eval x env)))
    :hints (("goal" :use ((:instance svexlist-depends-on-suff
                           (env (cons (cons (svar-fix var) val) env)))
                          (:instance svexlist-depends-on-suff)))
            '(:cases ((svar-p var))
              :do-not-induct t))
    :otf-flg t)

  (local (defthm svexlist-evals-equal-when-envs-agree
           (implies (svex-envs-agree (svexlist-vars x) env1 env2)
                    (equal (equal (svexlist-eval x env1) (svexlist-eval x env2)) t))
           :hints(("Goal" :in-theory (enable svexlist-eval-when-envs-agree)))))
  
  (defthm svexlist-not-depends-on-when-not-member-vars
    (implies (not (member-equal (svar-fix var) (svexlist-vars x)))
             (not (svexlist-depends-on var x)))
    :hints (("goal" :expand ((svexlist-depends-on var x)))))


  (defthm svexlist-depends-on-when-atom
    (implies (atom x)
             (not (svexlist-depends-on var x)))
    :hints(("Goal" :in-theory (enable svexlist-depends-on))))

  (defthmd svexlist-depends-on-when-car
    (implies (and (consp x)
                  (svex-depends-on var (car x)))
             (svexlist-depends-on var x))
    :hints(("Goal" :expand ((svex-depends-on var (car x))
                            (:free (env) (svexlist-eval x env)))
            :use ((:instance svexlist-depends-on-suff
                   (env (svex-depends-on-witness var (car x)))))
            :in-theory (disable svexlist-depends-on-suff
                                svexlist-not-depends-on-implies))))

  (defthmd svexlist-depends-on-when-cdr
    (implies (and (consp x)
                  (svexlist-depends-on var (cdr x)))
             (svexlist-depends-on var x))
    :hints(("Goal" :expand ((svexlist-depends-on var (cdr x))
                            (:free (env) (svexlist-eval x env)))
            :use ((:instance svexlist-depends-on-suff
                   (env (svexlist-depends-on-witness var (cdr x)))))
            :in-theory (disable svexlist-depends-on-suff
                                svexlist-not-depends-on-implies))))

  (defthmd svexlist-not-depends-on-when-not-car/cdr
    (implies (and (not (svex-depends-on var (car X)))
                  (not (svexlist-depends-on var (cdr x))))
             (not (svexlist-depends-on var x)))
    :hints (("goal" :expand ((svexlist-depends-on var x))
             :use ((:instance svexlist-depends-on-suff
                    (x (cdr x)) (env (svexlist-depends-on-witness var x)))
                   (:instance svex-depends-on-suff
                    (x (car x)) (env (svexlist-depends-on-witness var x))))
             :in-theory (disable svexlist-depends-on-suff
                                 svexlist-not-depends-on-implies
                                 svex-depends-on-suff
                                 svex-not-depends-on-implies))))

  (defthmd svexlist-depends-on-redef
    (equal (svexlist-depends-on var x)
           (if (atom x)
               nil
             (or (svex-depends-on var (car x))
                 (svexlist-depends-on var (cdr x)))))
    :hints(("Goal" :cases ((svexlist-depends-on var x))
            :in-theory (enable svexlist-depends-on-when-cdr
                               svexlist-depends-on-when-car
                               svexlist-not-depends-on-when-not-car/cdr)))
    :rule-classes ((:definition :install-body nil))))

(defsection svex-alist-depends-on
  (defun-sk svex-alist-depends-on (var x)
    (exists env
            (not (svex-envs-equivalent
                  (svex-alist-eval x (cons (cons (svar-fix var) (4vec-x)) env))
                  (svex-alist-eval x env)))))

  (in-theory (disable svex-alist-depends-on-suff
                      svex-alist-depends-on))
  
  (defcong svex-alist-eval-equiv equal (svex-alist-depends-on var x) 2
    :hints (("goal" :cases ((svex-alist-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svex-alist-depends-on clause))
                      (other (sublis '((x . x-equiv) (x-equiv . x)) lit))
                      (w `(svex-alist-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svex-alist-depends-on-suff
                            (x ,(third lit))
                            (env ,w))))))))
  

  (defcong svar-equiv equal (svex-alist-depends-on var x) 1
    :hints (("goal" :cases ((svex-alist-depends-on var x)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svex-alist-depends-on clause))
                      (other (sublis '((var . var-equiv) (var-equiv . var)) lit))
                      (w `(svex-alist-depends-on-witness . ,(cdr other))))
                   `(:expand (,other)
                     :use ((:instance svex-alist-depends-on-suff
                            (var ,(second lit))
                            (env ,w))))))))

  (defthm svex-alist-not-depends-on-implies
    (implies (and (bind-free
                   (case-match var
                     (('svar-fix$inline v) `((v . ,v)))
                     (& `((v . ,var)))))
                  (equal (svar-fix v) var)
                  (not (svex-alist-depends-on (double-rewrite var) x)))
             (svex-envs-equivalent
              (svex-alist-eval x (cons (cons var val) env))
              (svex-alist-eval x env)))
    :hints (("goal" :use ((:instance svex-alist-depends-on-suff
                           (env (cons (cons (svar-fix var) val) env)))
                          (:instance svex-alist-depends-on-suff)))
            '(:cases ((svar-p var))
              :do-not-induct t))
    :otf-flg t)

  (local (defthm svex-alist-evals-equal-when-envs-agree
           (implies (svex-envs-agree (svex-alist-vars x) env1 env2)
                    (equal (svex-envs-equivalent (svex-alist-eval x env1) (svex-alist-eval x env2)) t))
           :hints(("Goal" :in-theory (enable svex-alist-eval-when-envs-agree)))))
  
  (defthm svex-alist-not-depends-on-when-not-member-vars
    (implies (not (member-equal (svar-fix var) (svex-alist-vars x)))
             (not (svex-alist-depends-on var x)))
    :hints (("goal" :expand ((svex-alist-depends-on var x)))))


  (defthm svex-alist-depends-on-when-atom
    (implies (atom x)
             (not (svex-alist-depends-on var x)))
    :hints(("Goal" :in-theory (enable svex-alist-depends-on
                                      svex-alist-eval)))))
  




(define svex-dependencies-aux ((vars svarlist-p) (x svex-p))
  :returns (deps svarlist-p)
  (if (atom vars)
      nil
    (if (ec-call (svex-depends-on (car vars) x))
        (cons (svar-fix (car vars))
              (svex-dependencies-aux (cdr vars) x))
      (svex-dependencies-aux (cdr vars) x)))
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (member-equal v (svarlist-fix vars))
              (svex-depends-on v x))))

  (local (defret setp-vars-implies-<<-car
           (implies (and (setp vars)
                         (svarlist-p vars)
                         (<< v (car vars))
                         (consp deps))
                    (<< v (car deps)))
           :hints(("Goal" :in-theory (enable setp)))))

  (defret setp-of-<fn>
    (implies (and (setp vars)
                  (svarlist-p vars))
             (setp deps))
    :hints(("Goal" :in-theory (enable setp)))))


(local
 (defthm svarlist-p-of-set-difference
    (implies (svarlist-p x)
             (svarlist-p (set-difference-equal x y)))))

(defsection svex-env-removekeys-of-diff-is-svex-env-reduce
  

  (defthm svarlist-p-alist-keys
    (implies (svex-env-p x)
             (svarlist-p (alist-keys x)))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (local (defthm not-svex-env-boundp-when-member-alist-keys
           (implies (not (member-equal (svar-fix var) (alist-keys (svex-env-fix x))))
                    (not (svex-env-boundp var x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp-iff-member-alist-keys)))))
  
  (defthm svex-env-removekeys-of-diff-is-svex-env-reduce
    (svex-envs-equivalent (svex-env-removekeys (set-difference-equal (alist-keys (svex-env-fix x))
                                                                     (svarlist-fix keys))
                                               x)
                          (svex-env-reduce keys x))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                      svex-env-lookup-when-not-boundp))))

  

  (defthmd svex-env-reduce-to-removekeys
    (svex-envs-equivalent (svex-env-reduce keys x)
                          (svex-env-removekeys (set-difference-equal (alist-keys (svex-env-fix x))
                                                                     (svarlist-fix keys))
                                               x))))

(local (in-theory (e/d (svex-env-reduce-to-removekeys)
                       (svex-env-removekeys-of-diff-is-svex-env-reduce))))


(local (defthm svex-env-extract-under-svex-envs-similar
         (svex-envs-similar (svex-env-extract keys x)
                            (svex-env-reduce keys x))
         :hints(("Goal" :in-theory (enable svex-envs-similar
                                           svex-env-lookup-when-not-boundp
                                           svex-env-boundp-iff-member-alist-keys)))))



(local (defthm not-intersectp-of-set-diff-superset
         (implies (subsetp a b)
                  (not (intersectp-equal a (set-difference-equal c b))))))

(define svex-dependencies ((x svex-p))
  :returns (deps svarlist-p)
  (svex-dependencies-aux (svex-vars x) x)
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (svar-p v)
              (svex-depends-on v x))))

  (defret setp-of-<fn>
    (setp deps))

  (defcong svex-eval-equiv equal (svex-dependencies x) 1
    :hints(("Goal" :in-theory (e/d (double-containment
                                    pick-a-point-subset-strategy
                                    set::in-to-member)
                                   (svex-dependencies)))))

  (local (in-theory (disable svex-dependencies)))

  (defthm svex-eval-of-append-svarlist-x-env-of-non-deps
    (implies (not (intersectp-equal (svarlist-fix keys) (svex-dependencies x)))
             (equal (svex-eval x (append (svarlist-x-env keys) env))
                    (svex-eval x env)))
    :hints (("goal" :induct (svarlist-x-env keys)
             :in-theory (enable svarlist-x-env))))
  
  (defthm svex-eval-of-reduce-supserset-of-dependencies
    (implies (subsetp-equal (svex-dependencies x) (svarlist-fix keys))
             (equal (svex-eval x (svex-env-reduce keys env))
                    (svex-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthm svex-eval-of-extract-supserset-of-dependencies
    (implies (subsetp-equal (svex-dependencies x) (svarlist-fix keys))
             (equal (svex-eval x (svex-env-extract keys env))
                    (svex-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthmd svex-eval-equal-when-extract-dependencies-similar
    (implies (svex-envs-similar (svex-env-extract (svex-dependencies x) env2)
                                (svex-env-extract (svex-dependencies x) env1))
             (equal (equal (svex-eval x env2)
                           (svex-eval x env1))
                    t))
    :hints (("goal" :use ((:instance svex-eval-of-extract-supserset-of-dependencies
                           (keys (svex-dependencies x))
                           (env env1))
                          (:instance svex-eval-of-extract-supserset-of-dependencies
                           (keys (svex-dependencies x))
                           (env env2)))
             :in-theory (disable svex-eval-of-extract-supserset-of-dependencies)))))



(define svexlist-dependencies-aux ((vars svarlist-p) (x svexlist-p))
  :returns (deps svarlist-p)
  (if (atom vars)
      nil
    (if (ec-call (svexlist-depends-on (car vars) x))
        (cons (svar-fix (car vars))
              (svexlist-dependencies-aux (cdr vars) x))
      (svexlist-dependencies-aux (cdr vars) x)))
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (member-equal v (svarlist-fix vars))
              (svexlist-depends-on v x))))

  (local (defret setp-vars-implies-<<-car
           (implies (and (setp vars)
                         (svarlist-p vars)
                         (<< v (car vars))
                         (consp deps))
                    (<< v (car deps)))
           :hints(("Goal" :in-theory (enable setp)))))

  (defret setp-of-<fn>
    (implies (and (setp vars)
                  (svarlist-p vars))
             (setp deps))
    :hints(("Goal" :in-theory (enable setp)))))

(define svexlist-dependencies ((x svexlist-p))
  :returns (deps svarlist-p)
  (svexlist-dependencies-aux (svexlist-vars x) x)
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (svar-p v)
              (svexlist-depends-on v x))))

  (defret setp-of-<fn>
    (setp deps))

  (defcong svexlist-eval-equiv equal (svexlist-dependencies x) 1
    :hints(("Goal" :in-theory (e/d (double-containment
                                    pick-a-point-subset-strategy
                                    set::in-to-member)
                                   (svexlist-dependencies)))))

  (local (in-theory (disable svexlist-dependencies)))

  (defthm svexlist-eval-of-append-svarlist-x-env-of-non-deps
    (implies (not (intersectp-equal (svarlist-fix keys) (svexlist-dependencies x)))
             (equal (svexlist-eval x (append (svarlist-x-env keys) env))
                    (svexlist-eval x env)))
    :hints (("goal" :induct (svarlist-x-env keys)
             :in-theory (enable svarlist-x-env))))
  
  (defthm svexlist-eval-of-reduce-supserset-of-dependencies
    (implies (subsetp-equal (svexlist-dependencies x) (svarlist-fix keys))
             (equal (svexlist-eval x (svex-env-reduce keys env))
                    (svexlist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthm svexlist-eval-of-extract-supserset-of-dependencies
    (implies (subsetp-equal (svexlist-dependencies x) (svarlist-fix keys))
             (equal (svexlist-eval x (svex-env-extract keys env))
                    (svexlist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthmd svexlist-eval-equal-when-extract-dependencies-similar
    (implies (svex-envs-similar (svex-env-extract (svexlist-dependencies x) env2)
                                (svex-env-extract (svexlist-dependencies x) env1))
             (equal (equal (svexlist-eval x env2)
                           (svexlist-eval x env1))
                    t))
    :hints (("goal" :use ((:instance svexlist-eval-of-extract-supserset-of-dependencies
                           (keys (svexlist-dependencies x))
                           (env env1))
                          (:instance svexlist-eval-of-extract-supserset-of-dependencies
                           (keys (svexlist-dependencies x))
                           (env env2)))
             :in-theory (disable svexlist-eval-of-extract-supserset-of-dependencies)))))



(define svex-alist-dependencies-aux ((vars svarlist-p) (x svex-alist-p))
  :returns (deps svarlist-p)
  (if (atom vars)
      nil
    (if (ec-call (svex-alist-depends-on (car vars) x))
        (cons (svar-fix (car vars))
              (svex-alist-dependencies-aux (cdr vars) x))
      (svex-alist-dependencies-aux (cdr vars) x)))
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (member-equal v (svarlist-fix vars))
              (svex-alist-depends-on v x))))

  (local (defret setp-vars-implies-<<-car
           (implies (and (setp vars)
                         (svarlist-p vars)
                         (<< v (car vars))
                         (consp deps))
                    (<< v (car deps)))
           :hints(("Goal" :in-theory (enable setp)))))

  (defret setp-of-<fn>
    (implies (and (setp vars)
                  (svarlist-p vars))
             (setp deps))
    :hints(("Goal" :in-theory (enable setp)))))

(define svex-alist-dependencies ((x svex-alist-p))
  :returns (deps svarlist-p)
  (svex-alist-dependencies-aux (svex-alist-vars x) x)
  ///
  (defret member-of-<fn>
    (iff (member-equal v deps)
         (and (svar-p v)
              (svex-alist-depends-on v x))))

  (defret setp-of-<fn>
    (setp deps))

  (defcong svex-alist-eval-equiv equal (svex-alist-dependencies x) 1
    :hints(("Goal" :in-theory (e/d (double-containment
                                    pick-a-point-subset-strategy
                                    set::in-to-member)
                                   (svex-alist-dependencies)))))

  (local (in-theory (disable svex-alist-dependencies)))

  (defthm svex-alist-eval-of-append-svarlist-x-env-of-non-deps
    (implies (not (intersectp-equal (svarlist-fix keys) (svex-alist-dependencies x)))
             (svex-envs-equivalent (svex-alist-eval x (append (svarlist-x-env keys) env))
                                   (svex-alist-eval x env)))
    :hints (("goal" :induct (svarlist-x-env keys)
             :in-theory (enable svarlist-x-env))))
  
  (defthm svex-alist-eval-of-reduce-supserset-of-dependencies
    (implies (subsetp-equal (svex-alist-dependencies x) (svarlist-fix keys))
             (svex-envs-equivalent (svex-alist-eval x (svex-env-reduce keys env))
                                   (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthm svex-alist-eval-of-extract-supserset-of-dependencies
    (implies (subsetp-equal (svex-alist-dependencies x) (svarlist-fix keys))
             (svex-envs-equivalent (svex-alist-eval x (svex-env-extract keys env))
                                   (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-under-svex-envs-similar))))

  (defthmd svex-alist-eval-equiv-when-extract-dependencies-similar
    (implies (svex-envs-similar (svex-env-extract (svex-alist-dependencies x) env2)
                                (svex-env-extract (svex-alist-dependencies x) env1))
             (equal (svex-envs-equivalent (svex-alist-eval x env2)
                                          (svex-alist-eval x env1))
                    t))
    :hints (("goal" :use ((:instance svex-alist-eval-of-extract-supserset-of-dependencies
                           (keys (svex-alist-dependencies x))
                           (env env1))
                          (:instance svex-alist-eval-of-extract-supserset-of-dependencies
                           (keys (svex-alist-dependencies x))
                           (env env2)))
             :in-theory (disable svex-alist-eval-of-extract-supserset-of-dependencies)))))
  

  


(defsection svex-depends-on-of-compose

  (local (defthm append-cons-x-split-under-svex-envs-similar
           (svex-envs-similar (append a (cons (cons v (4vec-x)) b))
                              (if (or (not (svar-p v))
                                      (svex-env-boundp v a))
                                  (append a b)
                                (cons (cons v (4vec-x)) (append a b))))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svex-env-lookup-of-cons-split)
                   :do-not-induct t))))
  
  (defthm svex-depends-on-of-svex-compose-strong
    (implies (and (or (not (svex-depends-on v x))
                      (svex-lookup v a))
                  (not (svex-alist-depends-on v a)))
             (not (svex-depends-on v (svex-compose x a))))
    :hints (("goal" :expand ((svex-depends-on v (svex-compose x a))))
            '(:cases ((svex-lookup v a)))))

  (defthm svexlist-depends-on-of-svexlist-compose-strong
    (implies (and (or (not (svexlist-depends-on v x))
                      (svex-lookup v a))
                  (not (svex-alist-depends-on v a)))
             (not (svexlist-depends-on v (svexlist-compose x a))))
    :hints (("goal" :expand ((svexlist-depends-on v (svexlist-compose x a))))
            '(:cases ((svex-lookup v a)))))
  
  (defthm svex-alist-depends-on-of-svex-alist-compose-strong
    (implies (and (or (not (svex-alist-depends-on v x))
                      (svex-lookup v a))
                  (not (svex-alist-depends-on v a)))
             (not (svex-alist-depends-on v (svex-alist-compose x a))))
    :hints (("goal" :expand ((svex-alist-depends-on v (svex-alist-compose x a))))
            '(:cases ((svex-lookup v a))))))


