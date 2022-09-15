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

(include-book "monotonic-on-vars")
(include-book "width")
(local (include-book "alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (in-theory (disable signed-byte-p
                           hons-dups-p)))

(local (std::add-default-post-define-hook :fix))


(define 4vec-bit-index-is-x ((n natp) (x 4vec-p))
  (b* (((4vec x)))
    (and (logbitp n x.upper)
         (not (logbitp n x.lower))))
  ///
  (local (defthm 4vec-bit-index-when-4vec-<<=-lemma
           (and (implies (and (4vec-<<= x y)
                              (not (4vec-bit-index-is-x n x)))
                         (not (4vec-bit-index-is-x n y))))
           :hints(("Goal" :in-theory (enable 4vec-<<=))
                  (acl2::logbitp-reasoning))))

  (defthm 4vec-bit-index-is-x-when-4vec-<<=
    (and (implies (and (4vec-<<= x y)
                       (not (4vec-bit-index-is-x n x)))
                  (not (4vec-bit-index-is-x n y)))
         (implies (and (4vec-<<= x y)
                       (4vec-bit-index-is-x n y))
                  (4vec-bit-index-is-x n x)))
    :hints(("Goal" :in-theory (disable 4vec-bit-index-is-x))))

  (defthm equal-of-4vec-bit-index-when-4vec-<<=
    (implies (4vec-<<= x y)
             (equal (equal (4vec-bit-index n x) (4vec-bit-index n y))
                    (equal (4vec-bit-index-is-x n x)
                           (4vec-bit-index-is-x n y))))
    :hints(("Goal" :in-theory (enable 4vec-bit-index-is-x 4vec-bit-index 4vec-<<=))
           (acl2::logbitp-reasoning)))

  (defthm 4vec-bit-index-is-x-of-x
    (4vec-bit-index-is-x n (4vec-x))))

(define 4vec-x-count ((w natp) (x 4vec-p))
  :returns (count natp :rule-classes :type-prescription)
  (if (zp w)
      0
    (+ (bool->bit (4vec-bit-index-is-x (1- w) x))
       (4vec-x-count (1- w) x)))
  ///
  (defthm 4vec-x-count-when-4vec-<<=
    (implies (4vec-<<= x y)
             (<= (4vec-x-count w y) (4vec-x-count w x)))
    :rule-classes :linear)

  ;; (local (defthmd loghead-equal-implies-logbitp-equal
  ;;          (implies (and (equal (loghead n x) (loghead n y))
  ;;                        (< (nfix m) (nfix n)))
  ;;                   (equal (logbitp m x) (logbitp m y)))
  ;;          :hints ((acl2::logbitp-reasoning)
  ;;                  (and stable-under-simplificationp
  ;;                       '(:expand ((hide (equal (logbitp m x) (logbitp m y)))))))))

  (local (defthmd loghead-equal-when-logbitp-equal
           (implies (posp n)
                    (iff (equal (loghead n x) (loghead n y))
                         (and (equal (logbitp (+ -1 n) x)
                                     (logbitp (+ -1 n) y))
                              (equal (loghead (+ -1 n) x)
                                     (loghead (+ -1 n) y)))))
           :hints ((acl2::logbitp-reasoning :prune-examples nil)
                   (and stable-under-simplificationp
                        '(:expand ((hide (not (equal (logbitp (+ -1 n) x) (logbitp (+ -1 n) y))))
                                   (hide (equal (logbitp (+ -1 n) x) (logbitp (+ -1 n) y))))))
                   (and stable-under-simplificationp
                        '(:cases ((integerp n)))))
           :otf-flg t))

  (local (defthm equal-of-bool->bit
           (implies (and (booleanp x) (booleanp y))
                    (equal (equal (bool->bit x) (bool->bit y))
                           (equal x y)))
           :hints(("Goal" :in-theory (enable bool->bit)))))
  
  (local (defthm 4vec-zero-ext-equal-open
           (implies (and (2vec-p w)
                         (posp (2vec->val w)))
                    (equal (equal (4vec-zero-ext w x)
                                  (4vec-zero-ext w y))
                           (and (equal (4vec-bit-index (1- (2vec->val w)) x)
                                       (4vec-bit-index (1- (2vec->val w)) y))
                                (equal (4vec-zero-ext (2vec (1- (2vec->val w))) x)
                                       (4vec-zero-ext (2vec (1- (2vec->val w))) y)))))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext
                                             4vec-bit-index)
                   :use ((:instance loghead-equal-when-logbitp-equal
                          (n (2vec->val w))
                          (x (4vec->upper x))
                          (y (4vec->upper y)))
                         (:instance loghead-equal-when-logbitp-equal
                          (n (2vec->val w))
                          (x (4vec->lower x))
                          (y (4vec->lower y))))))
           :otf-flg t))

  (local (defthm 4vec-zero-ext-of-0
           (equal (4vec-zero-ext 0 x) 0)
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))
  
  (local (defthm 4vec-x-count-less-when-4vec-<<=-ext
           (implies (and (4vec-<<= x y)
                         (not (equal (4vec-zero-ext (2vec (nfix w)) x) (4vec-zero-ext (2vec (nfix w)) y))))
                    (< (4vec-x-count w y) (4vec-x-count w x)))
           :hints (("goal" :induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (enable bool->bit))))
           :rule-classes :linear))

  (local (defthm equal-loghead-when-signed-byte-p
           (implies (and (signed-byte-p n x)
                         (signed-byte-p n y))
                    (equal (equal (loghead n x) (loghead n y))
                           (equal x y)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm 4vec-zero-ext-equal-when-4vec-width-p
           (implies (and (2vec-p n)
                         (< 0 (2vec->val n))
                         (4vec-width-p (2vec->val n) x)
                         (4vec-width-p (2vec->val n) y))
                    (equal (equal (4vec-zero-ext n x) (4vec-zero-ext n y))
                           (equal (4vec-fix x) (4vec-fix y))))
           :hints(("Goal" :in-theory (enable 4vec-width-p 4vec-zero-ext
                                             4vec-fix-is-4vec-of-fields)))))
  
  (deffixequiv 4vec-x-count)
  
  (defthm 4vec-x-count-less-when-4vec-<<=
    (implies (and (4vec-<<= x y)
                  (posp w)
                  (4vec-width-p w x)
                  (4vec-width-p w y))
             (equal (< (4vec-x-count w y) (4vec-x-count w x))
                    (not (equal (4vec-fix x) (4vec-fix y)))))
    :hints (("goal" :do-not-induct t
             :use 4vec-x-count-less-when-4vec-<<=-ext
             :in-theory (disable 4vec-x-count-less-when-4vec-<<=-ext)))
    :rule-classes (:rewrite
                   (:linear :corollary
                    (implies (and (4vec-<<= x y)
                                  (posp w)
                                  (4vec-width-p w x)
                                  (4vec-width-p w y)
                                  (not (equal (4vec-fix x) (4vec-fix y))))
                             (< (4vec-x-count w y) (4vec-x-count w x))))))

  (defthm 4vec-x-count-of-x
    (equal (4vec-x-count w (4vec-x))
           (nfix w)))

  (defthm 4vec-x-count-max
    (<= (4vec-x-count w x) (nfix w))
    :rule-classes :linear))


(define svex-alist-env-widths-match-p ((x svex-alist-p)
                                       (env svex-env-p))
  (if (atom x)
      t
    (and (if (mbt (and (consp (car x)) (svar-p (caar x))))
             (b* ((expr-width (svex-width (cdar x))))
               (or (not expr-width)
                   (4vec-width-p expr-width (svex-env-lookup (caar x) env))))
           t)
         (svex-alist-env-widths-match-p (cdr x) env)))
  ///
  (local (defthm svex-alist-env-widths-match-p-of-cons-irrelevant-env
           (implies (not (svex-lookup key x))
                    (equal (svex-alist-env-widths-match-p x (cons (cons key val) env))
                           (svex-alist-env-widths-match-p x env)))
           :hints(("Goal" :in-theory (enable svex-lookup-redef
                                             svex-env-lookup-of-cons-split)))))
  
  (defthm svex-alist-env-widths-match-p-of-svex-alist-eval
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (svex-alist-env-widths-match-p x (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval
                                      svex-env-lookup-of-cons))))

  (defthm 4vec-width-p-of-lookup-when-svex-alist-env-widths-match-p
    (implies (and (svex-alist-env-widths-match-p x env)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (svex-lookup k x)
                  (svex-width (svex-lookup k x)))
             (4vec-width-p (svex-width (svex-lookup k x))
                           (svex-env-lookup k env)))
    :hints(("Goal" :in-theory (enable svex-lookup-redef
                                      svex-env-lookup-of-cons-split
                                      svex-alist-keys)
            :induct (svex-alist-keys x))))

  (defthm svex-alist-env-widths-match-p-of-svarlist-x-env
    (svex-alist-env-widths-match-p x (svarlist-x-env v)))


  (defthm svex-alist-env-widths-match-p-of-svex-env-extract-superset
    (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix keys))
             (equal (svex-alist-env-widths-match-p x (svex-env-extract keys env))
                    (svex-alist-env-widths-match-p x env)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))
  
  (local (in-theory (enable svex-alist-fix))))


(define svex-alist-env-x-count ((x svex-alist-p)
                                (env svex-env-p))
  :returns (x-count natp :rule-classes :type-prescription)
  :guard (svex-alist-width x)
  :verify-guards nil
  (if (atom x)
      0
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (+ (4vec-x-count (svex-width (cdar x))
                         (svex-env-lookup (caar x) env))
           (svex-alist-env-x-count (cdr x) env))
      (svex-alist-env-x-count (cdr x) env)))
  ///
  (local (in-theory (enable svex-alist-fix)))

  
  
  (defthm svex-alist-env-x-count-decreases
    (implies (and (svex-alist-width x)
                  (svex-alist-env-widths-match-p x env1)
                  (svex-alist-env-widths-match-p x env2)
                  (svex-env-<<= env1 env2))
             (and (<= (svex-alist-env-x-count x env2)
                      (svex-alist-env-x-count x env1))
                  (iff (< (svex-alist-env-x-count x env2)
                          (svex-alist-env-x-count x env1))
                       (not (equal (svex-env-extract (svex-alist-keys x) env1)
                                   (svex-env-extract (svex-alist-keys x) env2))))))
    :hints(("Goal" :in-theory (enable svex-alist-env-widths-match-p
                                      svex-alist-keys
                                      svex-alist-width
                                      svex-env-extract))
           (and stable-under-simplificationp
                '(:use ((:instance 4vec-x-count-less-when-4vec-<<=
                         (x (svex-env-lookup (caar x) env1))
                         (y (svex-env-lookup (caar x) env2))
                         (w (svex-width (cdar x)))))
                  :in-theory (disable 4vec-x-count-less-when-4vec-<<=))))

    :rule-classes
    (:rewrite
     (:linear :corollary
      (implies (and (svex-alist-width x)
                    (svex-alist-env-widths-match-p x env1)
                    (svex-alist-env-widths-match-p x env2)
                    (svex-env-<<= env1 env2))
               (<= (svex-alist-env-x-count x env2)
                   (svex-alist-env-x-count x env1))))
     (:linear :corollary
      (implies (and (svex-alist-width x)
                    (svex-alist-env-widths-match-p x env1)
                    (svex-alist-env-widths-match-p x env2)
                    (svex-env-<<= env1 env2)
                    (not (equal (svex-env-extract (svex-alist-keys x) env1)
                                (svex-env-extract (svex-alist-keys x) env2))))
               (< (svex-alist-env-x-count x env2)
                  (svex-alist-env-x-count x env1))))))


  (defthm svex-alist-env-x-count-of-svarlist-x-env
    (implies (svex-alist-width x)
             (equal (svex-alist-env-x-count x (svarlist-x-env v))
                    (svex-alist-width x)))
    :hints(("Goal" :in-theory (enable svex-alist-width
                                      svex-width-sum))))


  (defthm svex-alist-env-x-count-max
    (implies (svex-alist-width x)
             (<= (svex-alist-env-x-count x env) (svex-alist-width x)))
    :hints(("Goal" :in-theory (enable svex-alist-width
                                      svex-width-sum)))
    :rule-classes :linear))



(defthm svex-env-extract-of-svarlist-x-env
  (equal (svex-env-extract keys (svarlist-x-env any))
         (svarlist-x-env keys))
  :hints(("Goal" :in-theory (enable svex-env-extract svarlist-x-env))))


(local
 (defthm svex-env-removekeys-when-subsetp
   (implies (subsetp (alist-keys (svex-env-fix x)) (svarlist-fix vars))
            (equal (svex-env-removekeys vars x) nil))
   :hints(("Goal" :in-theory (enable svex-env-removekeys svex-env-fix alist-keys)))))
                    

(defthm svex-env-<<=-of-svarlist-x-env
  (svex-env-<<= (svarlist-x-env keys) x)
  :hints(("Goal" :in-theory (enable svex-env-<<=))))


(defthm svex-env-<<=-of-svex-env-extract
  (implies (svex-env-<<= env1 env2)
           (svex-env-<<= (svex-env-extract vars env1)
                         (svex-env-extract vars env2)))
  :hints(("Goal" :expand ((svex-env-<<= (svex-env-extract vars env1)
                                        (svex-env-extract vars env2))))))

(define svex-alist-eval-fixpoint-step ((x svex-alist-p)
                                  (env svex-env-p)
                                  (in-env svex-env-p))
  :returns (next-env svex-env-p)
  :guard (and (equal (svex-alist-keys x) (alist-keys env))
              (not (acl2::hons-dups-p (svex-alist-keys x))))
  (b* ((full-env (append (mbe :logic (svex-env-extract (svex-alist-keys x) env)
                                   :exec env)
                         in-env)))
    (with-fast-alist full-env
      (svex-alist-eval x full-env)))
  ///
  (defret alist-keys-of-<fn>
    (equal (alist-keys next-env)
           (svex-alist-keys x)))

  (defthm svex-alist-eval-fixpoint-step-of-svex-env-extract
    (equal (svex-alist-eval-fixpoint-step x (svex-env-extract (svex-alist-keys x) env) in-env)
           (svex-alist-eval-fixpoint-step x env in-env)))

  (defthm svex-alist-eval-fixpoint-step-monotonic
    (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (svex-env-<<= env1 env2))
             (svex-env-<<= (svex-alist-eval-fixpoint-step x env1 in-env)
                           (svex-alist-eval-fixpoint-step x env2 in-env)))
    :hints(("Goal" :in-theory (enable svex-alist-monotonic-on-vars-necc))))

  (defret svex-alist-env-widths-match-p-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (svex-alist-env-widths-match-p x next-env))))


(define svex-alist-eval-fixpoint-iterate-aux ((n natp)
                                         (x svex-alist-p)
                                         (env svex-env-p)
                                         (in-env svex-env-p))
  :guard (and (equal (svex-alist-keys x) (alist-keys env))
              (not (acl2::hons-dups-p (svex-alist-keys x))))
  :returns (ans-env svex-env-p)
  :verify-guards nil
  (b* (((when (zp n))
        (mbe :logic (svex-env-extract (svex-alist-keys x) env) :exec env))
       (next-env (svex-alist-eval-fixpoint-step x env in-env)))
    (mbe :logic (svex-alist-eval-fixpoint-iterate-aux (1- n) x next-env in-env)
         :exec (if (equal next-env env)
                   next-env
                 (svex-alist-eval-fixpoint-iterate-aux (1- n) x next-env in-env))))
  ///
  (defthm svex-alist-eval-fixpoint-iterate-aux-of-svex-env-extract
    (equal (svex-alist-eval-fixpoint-iterate-aux n x (svex-env-extract (svex-alist-keys x) env) in-env)
           (svex-alist-eval-fixpoint-iterate-aux n x env in-env)))
  (defthm svex-alist-eval-fixpoint-iterate-aux-compose
    (equal (svex-alist-eval-fixpoint-iterate-aux n x (svex-alist-eval-fixpoint-iterate-aux m x env in-env) in-env)
           (svex-alist-eval-fixpoint-iterate-aux (+ (nfix n) (nfix m)) x env in-env)))

  (defthm svex-env-extract-of-svex-alist-eval-fixpoint-iterate-aux
    (Equal (svex-env-extract (svex-alist-keys x)
                             (svex-alist-eval-fixpoint-iterate-aux n x env in-env))
           (svex-alist-eval-fixpoint-iterate-aux n x env in-env)))

  (defthm alist-keys-of-svex-alist-eval-fixpoint-iterate-aux
    (equal (alist-keys (svex-alist-eval-fixpoint-iterate-aux n x env in-env))
           (svex-alist-keys x)))
  
  (defthmd svex-alist-eval-fixpoint-iterate-aux-step
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-eval-fixpoint-step x (svex-alist-eval-fixpoint-iterate-aux n x env in-env) in-env)
                    (svex-alist-eval-fixpoint-iterate-aux (+ 1 (nfix n)) x env in-env)))
    :hints (("goal" :use ((:instance svex-alist-eval-fixpoint-iterate-aux-compose (n 1) (m n)))
             :in-theory (disable svex-alist-eval-fixpoint-iterate-aux
                                 svex-alist-eval-fixpoint-iterate-aux-compose)
             :expand ((:free (env) (svex-alist-eval-fixpoint-iterate-aux 1 x env in-env))
                      (:free (env) (svex-alist-eval-fixpoint-iterate-aux 0 x env in-env)))
             :do-not-induct t)))

  (local
   (defthmd svex-alist-eval-fixpoint-iterate-aux-when-fixpoint
     (implies (and (equal (svex-alist-eval-fixpoint-step x env in-env)
                          env)
                   (no-duplicatesp-equal (svex-alist-keys x)))
              (equal (svex-alist-eval-fixpoint-iterate-aux n x env in-env) env))
     :hints (("Goal" :induct t)
             (And stable-under-simplificationp
                  '(:use (alist-keys-of-svex-alist-eval-fixpoint-step
                          svex-env-p-of-svex-alist-eval-fixpoint-step)
                    :in-theory (disable alist-keys-of-svex-alist-eval-fixpoint-step
                                        svex-env-p-of-svex-alist-eval-fixpoint-step))))))

  (verify-guards svex-alist-eval-fixpoint-iterate-aux
    :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-iterate-aux-when-fixpoint)))))

(defthm alist-keys-of-svarlist-x-env
  (equal (alist-keys (svarlist-x-env vars))
         (svarlist-fix vars))
  :hints(("Goal" :in-theory (enable alist-keys svarlist-x-env))))




(defthm svex-env-<<=-of-svex-env-extract-left
  (svex-env-<<= (svex-env-extract vars x) x)
  :hints(("Goal" :in-theory (enable svex-env-<<=))))

(define svex-alist-eval-fixpoint-iterate ((n natp)
                                          (x svex-alist-p)
                                          (start-env svex-env-p)
                                          (in-env svex-env-p))
  :guard (and (equal (alist-keys start-env) (svex-alist-keys x))
              (not (acl2::hons-dups-p (svex-alist-keys x))))
  :returns (iter-env svex-env-p)
  :verify-guards nil
  (mbe :logic (if (zp n)
                  (svex-env-extract (svex-alist-keys x) start-env)
                (svex-alist-eval-fixpoint-step
                 x
                 (svex-alist-eval-fixpoint-iterate (1- n) x start-env in-env)
                 in-env))
       :exec (svex-alist-eval-fixpoint-iterate-aux n x start-env in-env))
  ///
  (local (defthm svex-alist-eval-fixpoint-iterate-aux-elim
           (implies (no-duplicatesp-equal (svex-alist-keys x))
                    (equal (svex-alist-eval-fixpoint-iterate-aux n x start-env in-env)
                           (svex-alist-eval-fixpoint-iterate n x start-env in-env)))
           :hints (("goal" :induct t
                    :in-theory (enable svex-alist-eval-fixpoint-iterate-aux))
                   (and stable-under-simplificationp
                        '(:use ((:instance svex-alist-eval-fixpoint-iterate-aux-step
                                 (n (1- n))
                                 (env start-env))))))))
  
  (verify-guards svex-alist-eval-fixpoint-iterate
    :hints (("goal" :expand ((:free (env) (svex-alist-eval-fixpoint-iterate-aux 0 x env in-env))
                             (:free (env) (svex-alist-eval-fixpoint-iterate-aux n x env in-env))))))


  (defret svex-env-extract-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (Equal (svex-env-extract (svex-alist-keys x) iter-env)
                    iter-env)))

  (defret svex-alist-env-widths-match-p-of-<fn>
    (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                  (svex-alist-env-widths-match-p x start-env))
             (svex-alist-env-widths-match-p x iter-env)))

  (defret alist-keys-of-svex-alist-eval-fixpoint-iterate
    (equal (alist-keys iter-env)
           (svex-alist-keys x)))

  (defret svex-alist-eval-fixpoint-iterate-step-increases
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x)))
             (svex-env-<<= iter-env
                           (svex-alist-eval-fixpoint-step x iter-env in-env)))
    :hints (("goal" :induct <call>
             :expand ((:free (start-env) (svex-alist-eval-fixpoint-iterate n x start-env in-env))
                      (:free (start-env) (svex-alist-eval-fixpoint-iterate 0 x start-env in-env))
                      (:free (start-env) (svex-alist-eval-fixpoint-iterate 1 x start-env in-env))))))


  (local (defun count-down (n)
           (if (zp n)
               n
             (count-down (1- n)))))
  
  (defret svex-alist-eval-fixpoint-iterate-increases
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (<= (nfix n) (nfix m)))
             (svex-env-<<= iter-env
                           (svex-alist-eval-fixpoint-iterate m x start-env in-env)))
    :hints (("goal" :induct (count-down m)
             :expand ((:free (start-env) (svex-alist-eval-fixpoint-iterate m x start-env in-env)))
             :in-theory (enable svex-env-<<=-transitive-1))))

  (fty::deffixequiv svex-alist-eval-fixpoint-iterate)

  (defret svex-alist-eval-fixpoint-iterate-fixpoint-preserved
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (equal (svex-alist-eval-fixpoint-step x iter-env in-env) iter-env)
                  (< (nfix n) (nfix m)))
             (equal (svex-alist-eval-fixpoint-iterate m x start-env in-env)
                    (svex-alist-eval-fixpoint-iterate n x start-env in-env)))
    :hints (("goal" :induct (count-down m)
             :expand ((:free (start-env) (svex-alist-eval-fixpoint-iterate m x start-env in-env))))))

  (defret svex-alist-eval-fixpoint-iterate-fixpoint-lemma
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (svex-alist-width x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (< (- (svex-alist-width x) (nfix n))
                     (svex-alist-env-x-count x iter-env)))
             (equal (svex-alist-eval-fixpoint-step x iter-env in-env)
                    iter-env))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance svex-alist-env-x-count-decreases
                          (env1 (svex-alist-eval-fixpoint-iterate (1- n) x (svarlist-x-env (svex-alist-keys x)) in-env))
                          (env2 (svex-alist-eval-fixpoint-step
                                 x (svex-alist-eval-fixpoint-iterate
                                    (1- n) x (svarlist-x-env (svex-alist-keys x)) in-env) in-env))))
                   :in-theory (disable svex-alist-env-x-count-decreases)))))

  ;; This shows that this function produces a fixpoint for x if iterated
  ;; sufficiently, i.e. n >= (svex-alist-width x), with start-env of all Xes.
  (defret svex-alist-eval-fixpoint-iterate-fixpoint
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (svex-alist-width x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x))
                  (<= (svex-alist-width x) (nfix n)))
             (equal (svex-alist-eval-fixpoint-step x iter-env in-env)
                    iter-env))
    :hints (("goal" :use (svex-alist-eval-fixpoint-iterate-fixpoint-lemma
                          (:instance svex-alist-env-x-count-decreases
                           (env1 (svex-alist-eval-fixpoint-iterate n x (svarlist-x-env (svex-alist-keys x)) in-env))
                           (env2 (svex-alist-eval-fixpoint-step
                                  x (svex-alist-eval-fixpoint-iterate n x (svarlist-x-env (svex-alist-keys x)) in-env) in-env))))
             :in-theory (disable svex-alist-eval-fixpoint-iterate-fixpoint-lemma
                                 svex-alist-env-x-count-decreases)
             :do-not-induct t)))

  (defthm svex-alist-eval-fixpoint-iterate-monotonic
    (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (svex-env-<<= start-env1 start-env2))
             (svex-env-<<= (svex-alist-eval-fixpoint-iterate n x start-env1 in-env)
                           (svex-alist-eval-fixpoint-iterate n x start-env2 in-env)))
    :hints (("goal" :induct t)))
  
  ;; This shows that when this function is run with a start env all Xes, its
  ;; result is <<= any fixpoint.  This shows that the fixpoint we get when
  ;; iterating this sufficiently on all-X start env is the unique least
  ;; fixpoint.
  (defret svex-alist-eval-fixpoint-iterate-least-fixpoint
    :pre-bind ((start-env (svarlist-x-env (svex-alist-keys x))))
    (implies (and (svex-envs-similar (svex-alist-eval-fixpoint-step x fixpoint-env in-env)
                                     (svex-env-extract (svex-alist-keys x) fixpoint-env))
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x))
             (svex-env-<<= iter-env fixpoint-env))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance svex-alist-eval-fixpoint-step-monotonic
                          (env1 (svex-alist-eval-fixpoint-iterate (1- n) x (svarlist-x-env (svex-alist-keys x)) in-env))
                          (env2 fixpoint-env)))
                   :in-theory (e/d (svex-env-<<=-transitive-1)
                                   (svex-alist-eval-fixpoint-step-monotonic)))))))


(define svex-alist-eval-least-fixpoint ((x svex-alist-p)
                                        (in-env svex-env-p))
  :guard (and (not (acl2::hons-dups-p (svex-alist-keys x)))
              (svex-alist-width x))
  :returns (least-fixpoint svex-env-p)
  (svex-alist-eval-fixpoint-iterate (svex-alist-width x) x
                                    (svarlist-x-env (svex-alist-keys x))
                                    in-env)
  ///

  (defret svex-env-extract-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (Equal (svex-env-extract (svex-alist-keys x) least-fixpoint)
                    least-fixpoint)))

  (defret svex-alist-env-widths-match-p-of-<fn>
    (implies (and (no-duplicatesp-equal (svex-alist-keys x))
                  (svex-alist-env-widths-match-p x start-env))
             (svex-alist-env-widths-match-p x least-fixpoint)))

  (defret alist-keys-of-<fn>
    (equal (alist-keys least-fixpoint)
           (svex-alist-keys x)))

  (defret <fn>-is-fixpoint
    (implies (and (svex-alist-width x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x)))
             (equal (svex-alist-eval-fixpoint-step x least-fixpoint in-env)
                    least-fixpoint)))

  (defret <fn>-is-fixpoint-2
    (implies (and (svex-alist-width x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x)))
             (equal (svex-alist-eval x (append least-fixpoint in-env))
                    least-fixpoint))
    :hints (("Goal" :use <fn>-is-fixpoint
             :in-theory (e/d (svex-alist-eval-fixpoint-step)
                             (<fn> <fn>-is-fixpoint)))))

  (defret <fn>-<<=-other-fixpoint
    (implies (and (svex-envs-similar (svex-alist-eval-fixpoint-step x fixpoint-env in-env)
                                     (svex-env-extract (svex-alist-keys x) fixpoint-env))
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x))
             (svex-env-<<= least-fixpoint fixpoint-env))))

(defthm svex-env-extract-keys-under-svex-envs-equivalent
  (implies (set-equiv (double-rewrite keys) (alist-keys (svex-env-fix x)))
           (svex-envs-equivalent (svex-env-extract keys x) x))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                    svex-env-boundp-iff-member-alist-keys
                                    svex-env-lookup-when-not-boundp))))


(encapsulate nil
  (local (defthm svex-alist-extract-when-bad-car
           (implies (and (consp x)
                         (or (not (consp (Car x)))
                             (not (svar-p (caar x)))
                             (not (member-equal (caar x) (svarlist-fix keys)))))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable svex-alist-extract
                                             svex-lookup-redef)))))
  (local
   (defthm svex-alist-extract-when-svex-alist-keys-equal-lemma
     (implies (no-duplicatesp-equal (svex-alist-keys x))
              (equal (svex-alist-extract (svex-alist-keys x) x) (svex-alist-fix x)))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-extract svex-alist-fix
                                       svex-lookup-redef)))))
  
  (defthm svex-alist-extract-when-svex-alist-keys-equal
    (implies (and (equal (svex-alist-keys x) keys)
                  (no-duplicatesp-equal keys))
             (equal (svex-alist-extract keys x) (svex-alist-fix x)))))


(defthm svex-alist-compose-preserves-svex-alist-monotonic-on-vars-with-nonkeys
  (implies (and (svex-alist-monotonic-on-vars vars x)
                (svex-alist-monotonic-on-vars (svex-alist-keys a) x)
                (svex-alist-monotonic-on-vars vars a))
           (svex-alist-monotonic-on-vars vars (svex-alist-compose x a)))
  :hints ((and stable-under-simplificationp
               (b* ((lit (car (last clause)))
                    (witness `(svex-alist-monotonic-on-vars-witness . ,(cdr lit))))
                 `(:expand (,lit)
                   :use ((:instance svex-alist-monotonic-on-vars-necc
                          (x a)
                          (vars vars)
                          (env1 (mv-nth 0 ,witness))
                          (env2 (mv-nth 1 ,witness)))
                         (:instance svex-alist-monotonic-on-vars-necc
                          (vars (svex-alist-keys a))
                          (env1 (append (svex-alist-eval a (mv-nth 0 ,witness)) (mv-nth 0 ,witness)))
                          (env2 (append (svex-alist-eval a (mv-nth 1 ,witness)) (mv-nth 0 ,witness))))
                         (:instance svex-alist-monotonic-on-vars-necc
                          (vars vars)
                          (env1 (append (svex-alist-eval a (mv-nth 1 ,witness)) (mv-nth 0 ,witness)))
                          (env2 (append (svex-alist-eval a (mv-nth 1 ,witness)) (mv-nth 1 ,witness)))))
                   :in-theory (e/d (svex-env-<<=-transitive-1)
                                   (svex-alist-monotonic-on-vars-necc)))))))

(defthm svex-alist-monotonic-on-vars-of-svex-alist-extract
  (implies (svex-alist-monotonic-on-vars vars x)
           (svex-alist-monotonic-on-vars vars (svex-alist-extract keys x)))
  :hints((and stable-under-simplificationp
              (b* ((lit (car (last clause))))
                `(:expand (,lit)
                  :in-theory (enable svex-alist-monotonic-on-vars-necc))))))

(define svex-alist-fixpoint-iterate ((n natp)
                                     (x svex-alist-p)
                                     (start-subst svex-alist-p))
  :guard (and (equal (svex-alist-keys start-subst) (svex-alist-keys x))
              (not (acl2::hons-dups-p (svex-alist-keys x))))
  :returns (iter-subst svex-alist-p)
  :verify-guards :after-returns
  (if (zp n)
      (mbe :logic (svex-alist-extract (svex-alist-keys x) start-subst)
           :exec start-subst)
    (svex-alist-compose
     x
     (svex-alist-fixpoint-iterate (1- n) x start-subst)))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys iter-subst)
           (svex-alist-keys x)))
  
  (defret svex-alist-extract-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (Equal (svex-alist-extract (svex-alist-keys x) iter-subst)
                    iter-subst)))
  
  (defret eval-of-<fn>
    (equal (svex-alist-eval iter-subst in-env)
           (svex-alist-eval-fixpoint-iterate n x (svex-alist-eval start-subst in-env) in-env))
    :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-iterate
                                      svex-alist-eval-fixpoint-step))))

  (defret <fn>-monotonic
    (implies (and (svex-alist-monotonic-on-vars vars x)
                  (svex-alist-monotonic-on-vars vars start-subst)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x))
             (svex-alist-monotonic-on-vars vars iter-subst))))

(defthm svex-alist-monotonic-on-vars-of-svarlist-x-subst
  (svex-alist-monotonic-on-vars vars (svarlist-x-subst keys))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-on-vars))))

(define svex-alist-least-fixpoint ((x svex-alist-p))
  :guard (and (not (acl2::hons-dups-p (svex-alist-keys x)))
              (svex-alist-width x))
  :returns (least-fixpoint svex-alist-p)
  (svex-alist-fixpoint-iterate (svex-alist-width x) x
                               (svarlist-x-subst (svex-alist-keys x)))
  ///

  (defret svex-alist-extract-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (Equal (svex-alist-extract (svex-alist-keys x) least-fixpoint)
                    least-fixpoint)))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys least-fixpoint)
           (svex-alist-keys x)))

  (defret eval-of-<fn>
    (equal (svex-alist-eval least-fixpoint in-env)
           (svex-alist-eval-least-fixpoint x in-env))
    :hints(("Goal" :in-theory (enable svex-alist-eval-least-fixpoint))))

  (defret <fn>-is-fixpoint
    (implies (and (svex-alist-width x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                  (no-duplicatesp-equal (svex-alist-keys x)))
             (svex-alist-eval-equiv! (svex-alist-compose x least-fixpoint)
                                     least-fixpoint))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv!-when-svex-alist-eval-equiv
                                    svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (<fn>)))))

  (local (defthm svex-alist-eval-equiv-compose-implies-keys
           (implies (svex-alist-eval-equiv (svex-alist-compose x other-fixpoint)
                                           other-fixpoint)
                    (set-equiv (svex-alist-keys other-fixpoint)
                               (svex-alist-keys x)))
           :hints (("goal" :use ((:instance svex-alist-keys-of-svex-alist-compose
                                  (a other-fixpoint)))
                    :in-theory (disable svex-alist-keys-of-svex-alist-compose)))))

  (defret <fn>-<<=-other-fixpoint
    (implies (and (svex-alist-eval-equiv (svex-alist-compose x other-fixpoint)
                                         other-fixpoint)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x))
             (svex-alist-<<= least-fixpoint other-fixpoint))
    :hints(("Goal" :in-theory (e/d (svex-alist-<<=
                                    svex-alist-eval-fixpoint-step)
                                   (<fn>
                                    svex-alist-eval-equiv-implies-svex-envs-equivalent-svex-alist-eval-1
                                    svex-alist-eval-least-fixpoint-<<=-other-fixpoint))
            :use ((:instance svex-alist-eval-equiv-implies-svex-envs-equivalent-svex-alist-eval-1
                   (alist (svex-alist-compose x other-fixpoint))
                   (alist-equiv other-fixpoint)
                   (env (svex-alist-<<=-witness (svex-alist-least-fixpoint x) other-fixpoint)))
                  (:instance svex-alist-eval-least-fixpoint-<<=-other-fixpoint
                   (fixpoint-env (svex-alist-eval other-fixpoint (svex-alist-<<=-witness (svex-alist-least-fixpoint x) other-fixpoint)))
                   (in-env (svex-alist-<<=-witness (svex-alist-least-fixpoint x) other-fixpoint)))))))

  (defret <fn>-monotonic
    (implies (and (svex-alist-monotonic-on-vars vars x)
                  (svex-alist-monotonic-on-vars (svex-alist-keys x) x))
             (svex-alist-monotonic-on-vars vars least-fixpoint))))
