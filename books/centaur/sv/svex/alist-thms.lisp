; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "alist-equiv")
(include-book "rewrite-base")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))

(defthmd svex-lookup-of-cons
  (equal (svex-lookup k (cons pair rest))
         (if (and (consp pair)
                  (svar-p (car pair))
                  (equal (svar-fix k) (car pair)))
             (svex-fix (cdr pair))
           (svex-lookup k rest)))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

(local (in-theory (enable svex-lookup-of-cons)))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (cons x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(define svex-pair-eval-equiv (x y)
   :verify-guards nil
   (and (iff (consp x) (consp y))
        (implies (consp x)
                 (and (equal (car x) (car y))
                      (svex-eval-equiv (cdr x) (cdr y)))))
   ///
   (defequiv svex-pair-eval-equiv)
   (defcong svex-pair-eval-equiv svex-alist-eval-equiv (cons pair rest) 1
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                       svex-lookup))))

   (defcong svex-eval-equiv svex-pair-eval-equiv (cons key val) 2))


(defthm svex-compose-lookup-when-svex-lookup
  (implies (svex-lookup v x)
           (equal (svex-compose-lookup v x)
                  (svex-lookup v x)))
  :hints(("Goal" :in-theory (enable svex-compose-lookup))))

(defthm svex-compose-lookup-when-not-svex-lookup
  (implies (not (svex-lookup v x))
           (equal (svex-compose-lookup v x)
                  (svex-var v)))
  :hints(("Goal" :in-theory (enable svex-compose-lookup))))


(defthm svex-env-extract-nil
  (equal (svex-env-extract nil x) nil)
  :hints(("Goal" :in-theory (enable svex-env-extract))))


(defthmd svex-env-lookup-of-cons
  (Equal (svex-env-lookup k (cons (cons key val) a))
         (if (equal (svar-fix k) key)
             (4vec-fix val)
           (svex-env-lookup k a)))
  :hints(("Goal" :in-theory (enable svex-env-lookup))))


(defthm svex-alist-eval-equiv-of-cons
  (implies (svex-eval-equiv val1 val2)
           (svex-alist-eval-equiv (cons (cons key val1) rest)
                                  (cons (cons key val2) rest)))
  :hints (("goal" :in-theory (enable svex-alist-eval-equiv
                                     svex-lookup)))
  :rule-classes :congruence)

(defcong svex-alist-eval-equiv svex-eval-equiv (svex-compose x al) 2
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(defcong svex-eval-equiv svex-eval-equiv (svex-compose x al) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-extract vars al) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(defcong set-equiv svex-alist-eval-equiv (svex-alist-extract vars al) 1
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(defthmd svex-env-lookup-when-not-boundp
  (implies (not (svex-env-boundp var x))
           (equal (svex-env-lookup var x) (4vec-x)))
  :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp))))


(defthm svex-lookup-of-append
  (equal (svex-lookup k (append a b))
         (or (svex-lookup k a)
             (svex-lookup k b)))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))


(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-reduce keys x) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defthm svex-alist-eval-equiv-of-reduce-keys
  (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys x) x) x)
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

(defthm append-svex-alist-eval-when-svex-alist-compose-equiv
  (implies (svex-alist-compose-equiv x y)
           (svex-envs-similar (append (svex-alist-eval x env) env)
                              (append (svex-alist-eval y env) env)))
  :hints(("Goal" :in-theory (e/d (svex-envs-similar svex-compose-lookup)
                                 (svex-alist-compose-equiv-necc
                                  svex-alist-compose-equiv-implies-svex-eval-equiv-svex-compose-lookup-2))
          :expand ((:free (var) (svex-eval (svex-var var) env)))
          :use ((:instance svex-alist-compose-equiv-necc
                 (var (svex-envs-similar-witness
                       (append (svex-alist-eval x env) env)
                       (append (svex-alist-eval y env) env)))))))
  :rule-classes :congruence)


(defcong svex-alist-compose-equiv svex-eval-equiv
  (svex-compose x subst) 2
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(defcong svex-alist-compose-equiv svex-alist-eval-equiv
  (svex-alist-compose x subst) 2
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-compose x subst) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

;; (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-compose x subst) 2
;;   :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))




(defthm svex-compose-lookup-of-append
  (equal (Svex-compose-lookup key (append x y))
         (or (svex-lookup key x)
             (svex-compose-lookup key y)))
  :hints(("Goal" :in-theory (enable svex-compose-lookup))))


(defthmd svex-eval-equiv-of-svex-lookup-when-compose-equiv
  (implies (and (svex-alist-compose-equiv x y)
                (svex-lookup k x) (svex-lookup k y))
           (equal (svex-eval-equiv (svex-lookup k x) (svex-lookup k y)) t))
  :hints (("goal" :use ((:instance svex-alist-compose-equiv-necc
                         (var k)))
           :in-theory (e/d (svex-compose-lookup)
                           (svex-alist-compose-equiv-necc)))))



(defcong svex-alist-compose-equiv svex-alist-compose-equiv
  (svex-alist-reduce keys x) 2
  :hints ((and stable-under-simplificationp
               (let* ((lit (car (last clause))))
                 `(:expand (,lit)
                   :use ((:instance svex-alist-compose-equiv-necc
                          (var (svex-alist-compose-equiv-witness . ,(cdr lit)))
                          (y x-equiv)))
                   :in-theory (e/d (svex-compose-lookup)
                                   (svex-alist-compose-equiv-necc
                                    svex-alist-compose-equiv-implies-svex-eval-equiv-svex-compose-lookup-2)))))))






(defthm svex-alist-compose-of-svex-identity-subst
  (implies (subsetp-equal vars (svex-alist-keys x))
           (equal (svex-alist-compose (svex-identity-subst vars) x)
                  (svex-alist-reduce vars x)))
  :hints(("Goal" :in-theory (enable svex-alist-compose
                                    ;; svex-alist-keys
                                    svex-identity-subst
                                    svarlist-fix
                                    svex-acons
                                    svex-compose
                                    pairlis$
                                    svarlist->svexes
                                    svex-alist-reduce))))

(defcong svex-envs-similar svex-envs-similar (svex-env-removekeys keys env) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(defcong set-equiv svex-envs-equivalent (svex-env-removekeys keys env) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defthmd svex-env-removekeys-under-svex-envs-similar
  (svex-envs-similar (svex-env-removekeys vars x)
                     (append (svarlist-x-env vars) x))
  :hints(("Goal" :in-theory (enable svex-envs-similar))))

(encapsulate nil

  (local (defthm svex-lookup-of-svarlist-x-subst-split
           (equal (Svex-lookup v (svarlist-x-subst x))
                  (and (member-equal (svar-fix v) (svarlist-fix x))
                       (svex-x)))
           :hints(("Goal" :in-theory (enable svarlist-x-subst)))))

  (defcong set-equiv svex-alist-eval-equiv (svarlist-x-subst x) 1
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))


(defthmd svex-env-boundp-iff-member-alist-keys
  (iff (svex-env-boundp var env)
       (member (svar-fix var) (alist-keys (svex-env-fix env))))
  :hints(("Goal" :in-theory (enable svex-env-boundp alist-keys))))

(defthm svex-alist-keys-of-append
  (equal (svex-alist-keys (append x y))
         (append (svex-alist-keys x)
                 (svex-alist-keys y)))
  :hints(("Goal" :in-theory (enable svex-alist-keys))))

(defthm svex-alist-eval-of-pairlis$-vars
  (implies (svarlist-p vars)
           (equal (svex-alist-eval (pairlis$ vars (svarlist->svexes vars)) env)
                  (svex-env-extract vars env)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-extract svarlist->svexes svex-eval))))


(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-compose-equiv svex-alist-compose-equiv (append x y) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-removekeys keys x) 2
     :hints((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

(defthmd svex-compose-lookup-of-svex-alist-removekeys
  (equal (svex-compose-lookup v (svex-alist-removekeys keys x))
         (if (member-equal (svar-fix v) (svarlist-fix keys))
             (svex-var v)
           (svex-compose-lookup v x)))
  :hints(("Goal" :in-theory (enable svex-compose-lookup))))

(local (in-theory (enable svex-compose-lookup-of-svex-alist-removekeys)))

(defcong svex-alist-compose-equiv svex-alist-compose-equiv (svex-alist-removekeys keys x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))


(defthmd svex-compose-lookup-of-svex-alist-compose
  (equal (Svex-compose-lookup v (svex-alist-compose x a))
         (if (svex-lookup v x)
             (svex-compose (svex-lookup v x) a)
           (svex-var v)))
  :hints(("Goal" :in-theory (enable svex-compose-lookup))))


(defthm alist-keys-of-svex-alist-eval
  (equal (alist-keys (svex-alist-eval x env))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval alist-keys))))


;; not technically about alists
(defthm svex-compose-nil
  (svex-eval-equiv (svex-compose x nil) x)
  :hints(("Goal" :in-theory (enable svex-eval-equiv svex-alist-eval))))

(defthm svex-alist-eval-equiv-of-compose-nil
  (svex-alist-eval-equiv (svex-alist-compose x nil) x)
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                    svex-alist-eval))))

(defthm svex-alist-removekeys-of-nil
  (equal (svex-alist-removekeys keys nil) nil)
  :hints(("Goal" :in-theory (enable svex-alist-removekeys))))

(defthm svex-alist-keys-of-svex-alist-compose
  (Equal (svex-alist-keys (svex-alist-compose x a))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-compose
                                    svex-alist-keys))))

(defthm svex-alist-compose-of-append
  (equal (svex-alist-compose (append x y) a)
         (append (svex-alist-compose x a)
                 (svex-alist-compose y a)))
  :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons))))



(defthm svex-alist-removekeys-of-append-subset
  (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix vars))
           (equal (svex-alist-removekeys vars (append x y))
                  (svex-alist-removekeys vars y)))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys))))

(defthm svex-alist-removekeys-of-non-intersect
  (implies (not (intersectp-equal (svex-alist-keys x) (svarlist-fix vars)))
           (equal (svex-alist-removekeys vars x)
                  (svex-alist-fix x)))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys
                                    svex-alist-fix))))



(std::defret-mutual svex-eval-of-append-when-subsetp-first
  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svex-vars x) (alist-keys (svex-env-fix env)))
             (equal (svex-eval x (append env env2))
                    val))
    :hints ('(:expand ((:free (env) <call>)
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :fn svex-eval)
  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svexlist-vars x) (alist-keys (svex-env-fix env)))
             (equal (svexlist-eval x (append env env2))
                    vals))
    :hints ('(:expand ((:free (env) <call>)
                       (svexlist-vars x))))
    :fn svexlist-eval)
  :mutual-recursion svex-eval)

(defthm svex-alist-eval-of-append-when-subsetp-first
  (implies (subsetp (svex-alist-vars x) (alist-keys (svex-env-fix a)))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))


   

(defthm svex-alist-compose-of-append-when-subsetp-first
  (implies (subsetp (svex-alist-vars x) (svex-alist-keys a))
           (svex-alist-eval-equiv (svex-alist-compose x (append a b))
                                  (svex-alist-compose x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))

(defthm svex-alist-eval-of-svex-alist-removekeys
  (equal (svex-alist-eval (svex-alist-removekeys vars x) a)
         (svex-env-removekeys vars (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-removekeys svex-env-removekeys))))


(defthmd svex-alist-removekeys-when-superset
  (implies (subsetp (svex-alist-keys a) (svarlist-fix keys))
           (equal (svex-alist-removekeys keys a) nil))
  :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys svex-alist-fix))))

(defthm svex-alist-keys-of-svex-alist-removekeys
  (equal (svex-alist-keys (svex-alist-removekeys vars alist))
         (set-difference-equal (svex-alist-keys alist) (svarlist-fix vars)))
  :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys set-difference-equal))))




(defthm svex-compose-of-compose
  (svex-eval-equiv (svex-compose (svex-compose x a) b)
                   (svex-compose x (append (svex-alist-compose a b) b)))
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(defthm svex-alist-compose-of-svex-alist-compose
  (svex-alist-eval-equiv (svex-alist-compose (svex-alist-compose x a) b)
                         (svex-alist-compose x (append (svex-alist-compose a b) b)))
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

(defthm svex-alist-removekeys-of-append
  (Equal (svex-alist-removekeys vars (append a b))
         (append (svex-alist-removekeys vars a)
                 (svex-alist-removekeys vars b)))
  :hints(("Goal" :in-theory (enable svex-alist-removekeys))))

(defthm svex-alist-compose-of-removekeys
  (equal (svex-alist-compose (svex-alist-removekeys keys x) a)
         (svex-alist-removekeys keys (svex-alist-compose x a)))
  :hints(("Goal" :in-theory (enable svex-alist-compose svex-alist-removekeys svex-acons))))

(defthm svex-alist-removekeys-idempotent
  (equal (svex-alist-removekeys vars (svex-alist-removekeys vars x))
         (svex-alist-removekeys vars x))
  :hints(("Goal" :in-theory (enable svex-alist-removekeys))))


(defthm svex-env-extract-of-append
  (equal (svex-env-extract (append a b) x)
         (append (svex-env-extract a x)
                 (svex-env-extract b x)))
  :hints(("Goal" :in-theory (enable svex-env-extract))))



(defthm svex-envs-similar-of-append-extracts
  (iff (svex-envs-similar (append (svex-env-extract a x)
                                  (svex-env-extract b x))
                          (append (svex-env-extract a y)
                                  (svex-env-extract b y)))
       (and (svex-envs-similar (svex-env-extract a x)
                               (svex-env-extract a y))
            (svex-envs-similar (svex-env-extract b x)
                               (svex-env-extract b y))))
  :hints ((and stable-under-simplificationp
               (b* ((lit (assoc 'svex-envs-similar clause))
                    (appendp (eq (car (cadr lit)) 'binary-append))
                    )
                 `(:expand (,lit)
                   ,@(and (not appendp)
                          `(:use ((:instance svex-envs-similar-necc
                                   (x (append (svex-env-extract a x)
                                              (svex-env-extract b x)))
                                   (y (append (svex-env-extract a y)
                                              (svex-env-extract b y)))
                                   (k (svex-envs-similar-witness . ,(cdr lit)))))
                            :in-theory (disable SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-LOOKUP-2)))))))
  :otf-flg t)

(local (defthm svex-envs-similar-of-single
         (implies (svar-p var)
                  (iff (svex-envs-similar (list (cons var val1)) (list (cons var val2)))
                       (4vec-equiv val1 val2)))
         :hints (("goal" :use ((:instance svex-envs-similar-necc
                                (x (list (cons var val1))) (y (list (cons var val2)))
                                (k var)))
                  :in-theory (e/d (svex-env-lookup-of-cons)
                                  (svex-envs-similar-implies-equal-svex-env-lookup-2))))))

(std::defret-mutual svex-eval-equal-when-extract-vars-similar
  (defretd <fn>-equal-when-extract-vars-similar
    (implies (svex-envs-similar (svex-env-extract (svex-vars x) env2)
                                (svex-env-extract (svex-vars x) env))
             (equal (equal (svex-eval x env2)
                           val)
                    t))
    :hints ('(:expand ((:free (env) <call>)
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-extract))))
    :fn svex-eval)
  (defretd <fn>-equal-when-extract-vars-similar
    (implies (svex-envs-similar (svex-env-extract (svexlist-vars x) env2)
                                (svex-env-extract (svexlist-vars x) env))
             (equal (equal (svexlist-eval x env2)
                           vals)
                    t))
    :hints ('(:expand ((:free (env) <call>)
                       (svexlist-vars x))))
    :fn svexlist-eval)
  :mutual-recursion svex-eval)


(defthmd svex-alist-eval-equal-when-extract-vars-similar
  (implies (svex-envs-similar (svex-env-extract (svex-alist-vars x) env2)
                              (svex-env-extract (svex-alist-vars x) env))
           (equal (equal (svex-alist-eval x env2)
                         (svex-alist-eval x env))
                  t))
  :hints(("Goal" :in-theory (enable svex-alist-vars svex-alist-eval
                                    svex-eval-equal-when-extract-vars-similar)
          :induct t)))

(defthmd svex-alist-eval-equivalent-when-extract-vars-similar
  (implies (svex-envs-similar (svex-env-extract (svex-alist-vars x) env2)
                              (svex-env-extract (svex-alist-vars x) env))
           (equal (svex-envs-equivalent (svex-alist-eval x env2)
                                        (svex-alist-eval x env))
                  t))
  :hints(("Goal" :use svex-alist-eval-equal-when-extract-vars-similar
          :in-theory (disable svex-alist-eval-equal-when-extract-vars-similar))))

(encapsulate nil
  (local (defthm svex-alist-compose-eval-equiv-when-extract-vars-similar-lemma
           (implies (svex-alist-compose-equiv (svex-alist-reduce vars a1)
                                           (svex-alist-reduce vars a2))
                    (equal (svex-envs-similar
                            (svex-env-extract vars (APPEND (SVEX-ALIST-EVAL A1 env) env))
                            (svex-env-extract vars (APPEND (SVEX-ALIST-EVAL A2 env) env)))
                           t))
           :hints(("Goal" :in-theory (e/d (svex-envs-similar svex-eval)
                                          (svex-alist-compose-equiv-necc
                                           SVEX-ALIST-COMPOSE-EQUIV-IMPLIES-SVEX-EVAL-EQUIV-SVEX-COMPOSE-LOOKUP-2))
                   :use ((:instance svex-alist-compose-equiv-necc
                          (var (svex-envs-similar-witness
                                (svex-env-extract vars (APPEND (SVEX-ALIST-EVAL A1 env) env))
                                (svex-env-extract vars (APPEND (SVEX-ALIST-EVAL A2 env) env))))
                          (x (svex-alist-reduce vars a1))
                          (y (svex-alist-reduce vars a2))))))))
  (defthmd svex-alist-compose-eval-equiv-when-extract-vars-similar
    (implies (svex-alist-compose-equiv (svex-alist-reduce (svex-alist-vars x) a1)
                                       (svex-alist-reduce (svex-alist-vars x) a2))
             (equal (svex-alist-eval-equiv (svex-alist-compose x a1)
                                           (svex-alist-compose x a2))
                    t))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equivalent-when-extract-vars-similar)
            :expand ((:with svex-alist-eval-equiv-in-terms-of-envs-equivalent
                      (svex-alist-eval-equiv (svex-alist-compose x a1)
                                             (svex-alist-compose x a2))))))))



(local
 (encapsulate nil
   (local (defthm svex-envs-similar-of-extract-append-reduce-superset
            (implies (subsetp-equal (svarlist-fix vars1) (svarlist-fix vars))
                     (svex-envs-similar (svex-env-extract vars1 (append a (svex-env-reduce vars b) c))
                                        (svex-env-extract vars1 (append a b c))))
            :hints(("Goal" :in-theory (enable svex-envs-similar)))))
   (defthm svex-alist-eval-append-reduce-superset
     (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
              (equal (svex-alist-eval x (append a (svex-env-reduce vars b) c))
                     (svex-alist-eval x (append a b c))))
     :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar))))))



(defthm svex-compose-of-append-first-superset
  (implies (subsetp (svex-vars x) (svex-alist-keys a))
           (svex-eval-equiv (svex-compose x (append a b))
                            (svex-compose x a)))
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(std::defret-mutual svex-eval-of-append-when-non-intersectp-first
  (defret <fn>-of-append-when-non-intersectp-first
    (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix env2))))
             (equal (svex-eval x (append env2 env))
                    val))
    :hints ('(:expand ((:free (env) <call>)
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :fn svex-eval)
  (defret <fn>-of-append-when-non-intersectp-first
    (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix env2))))
             (equal (svexlist-eval x (append env2 env))
                    vals))
    :hints ('(:expand ((:free (env) <call>)
                       (svexlist-vars x))))
    :fn svexlist-eval)
  :mutual-recursion svex-eval)

(defthm svex-compose-of-append-first-non-intersect
  (implies (not (intersectp-equal (svex-vars x) (svex-alist-keys a)))
           (svex-eval-equiv (svex-compose x (append a b))
                            (svex-compose x b)))
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(std::defret-mutual svex-eval-of-append-non-intersecting
  (defret <fn>-of-append-non-intersecting
    :pre-bind ((env (append a c)))
    (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix b))))
             (equal (svex-eval x (append a b c))
                    val))
    :hints ('(:expand ((:free (env) <call>)
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :fn svex-eval)
  (defret <fn>-of-append-non-intersecting
    :pre-bind ((env (append a c)))
    (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix b))))
             (equal (svexlist-eval x (append a b c))
                    vals))
    :hints ('(:expand ((:free (env) <call>)
                       (svexlist-vars x))))
    :fn svexlist-eval)
  :mutual-recursion svex-eval)

(defthm svex-compose-of-append-second-non-intersect
  (implies (not (intersectp-equal (svex-vars x) (svex-alist-keys a)))
           (svex-eval-equiv (svex-compose x (append b a))
                            (svex-compose x b)))
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))



(defthm append-svex-alist-reduce-under-svex-alist-eval-equiv
  (svex-alist-eval-equiv (append (svex-alist-reduce keys x) x) x)
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))


(defsection svex-alist-same-keys
  (acl2::def-universal-equiv svex-alist-same-keys
    :qvars nil
    :equiv-terms ((set-equiv (svex-alist-keys x))))


  (defthmd svex-lookup-iff-member-svex-alist-keys
    (iff (svex-lookup k x)
         (member-equal (svar-fix k) (svex-alist-keys x))))


  (defcong svex-alist-same-keys iff (svex-lookup k x) 2
    :hints(("Goal" :in-theory (e/d (svex-alist-same-keys
                                    svex-lookup-iff-member-svex-alist-keys)
                                   (member-svex-alist-keys)))))

  (defthm set-equiv-forward-to-svex-alist-same-keys
    (implies (set-equiv (svex-alist-keys x) (svex-alist-keys y))
             (svex-alist-same-keys x y))
    :hints(("Goal" :in-theory (enable svex-alist-same-keys)))
    :rule-classes :forward-chaining)

  (defrefinement svex-alist-eval-equiv svex-alist-same-keys
    :hints(("Goal" :in-theory (enable svex-alist-same-keys))))

  (encapsulate
    (((svex-alist-same-keys-lookup-witness * *) => *))
    (local (defun svex-alist-same-keys-lookup-witness (x y)
             (svar-fix (acl2::set-unequal-witness (svex-alist-keys x)
                                                  (svex-alist-keys y)))))
    (defthm svar-p-of-svex-alist-same-keys-lookup-witness
      (svar-p (svex-alist-same-keys-lookup-witness x y)))
           
    (defthmd svex-alist-same-keys-in-terms-of-lookup
      (equal (svex-alist-same-keys x y)
             (let ((var (svex-alist-same-keys-lookup-witness x y)))
               (iff (svex-lookup var x) (svex-lookup var y))))
      :hints(("Goal" :in-theory (e/d (svex-alist-same-keys)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (acl2::set-unequal-witness-correct
                                     svex-alist-same-keys-lookup-witness
                                     svex-lookup-iff-member-svex-alist-keys)
                                    (member-svex-alist-keys)))))
      :rule-classes ((:definition :install-body nil))))

  (defcong svex-alist-same-keys set-equiv (svex-alist-keys x) 1
    :hints(("Goal" :in-theory (enable svex-alist-same-keys)))))





(defthm svex-alist-keys-of-svex-alist-compose
  (Equal (svex-alist-keys (svex-alist-compose x a))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose))))

(Defthm svex-alist-keys-of-svex-alist-reduce
  (equal (svex-alist-keys (svex-alist-reduce keys x))
         (intersection-equal (svarlist-fix keys) (svex-alist-keys x)))
  :hints(("Goal" :in-theory (enable svex-alist-reduce svex-alist-keys))))


(defthmd svex-lookup-redef
  (equal (svex-lookup key alist)
         (cond ((atom alist) nil)
               ((and (consp (car alist))
                     (equal (caar alist) (svar-fix key)))
                (svex-fix (cdar alist)))
               (t (svex-lookup key (cdr alist)))))
  :hints(("Goal" :in-theory (enable svex-lookup)))
  :rule-classes ((:definition :install-body nil)))

(defthmd svex-lookup-redef2
  (equal (svex-lookup key alist)
         (let ((alist (svex-alist-fix alist)))
           (cond ((atom alist) nil)
                 ((and (consp (car alist))
                       (equal (caar alist) (svar-fix key)))
                  (cdar alist))
                 (t (svex-lookup key (cdr alist))))))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))
  :rule-classes ((:definition :install-body nil)))




(defthm svarlist-p-alist-keys-of-svex-env
  (implies (svex-env-p x)
           (svarlist-p (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))


