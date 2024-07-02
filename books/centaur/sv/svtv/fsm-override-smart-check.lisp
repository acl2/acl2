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

(include-book "../svex/override-transparency-decomp")
(include-book "../svex/override-syntax-check")
(include-book "../svex/override-semantic-check")
(include-book "fsm-override-transparency")
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/meta/variable-free" :dir :system)
(include-book "tools/trivial-ancestors-check" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/alist-thms"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (include-book "std/osets/element-list" :dir :system))

(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))

(defthm svarlist-change-override-when-override-p
    (implies (svarlist-override-p x type)
             (equal (svarlist-change-override x type) (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-fix
                                      svarlist-change-override
                                      svarlist-override-p))))

(defsection svarlist-override-p-of-svarlist-override-p-of-svexlist-overridekeys-syntax-check
  (local (defthmd svarlist-override-p-of-svexlist-overridekeys-syntax-check-lemma
           (svarlist-override-p (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data keys values))
                                nil)
           :hints (("goal" :induct (len keys)
                    :in-theory (enable svarlist-override-p)
                    :expand ((:with svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data keys values)))
                             (:with svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data nil values))))))))
  (defthm svarlist-override-p-of-svexlist-overridekeys-syntax-check
    (svarlist-override-p (svexlist-overridekeys-syntax-check x data)
                         nil)
    :hints (("goal" :use ((:instance svarlist-override-p-of-svexlist-overridekeys-syntax-check-lemma
                           (keys (overridekey-syntaxcheck-data->keys data))
                           (values (overridekey-syntaxcheck-data->values data))))))))

(define fsm-override-syntax-check ((x fsm-p)
                                        (keys svarlist-p))
  :returns (bad-keys svarlist-p)
  (b* (((fsm x)))
    (acl2::with-fast-alist x.values
      (b* ((syntaxcheck-data (make-overridekey-syntaxcheck-data :keys keys
                                                                :values x.values))
           (bad-keys1 (svexlist-overridekeys-syntax-check (svex-alist-vals x.nextstate) syntaxcheck-data))
           (bad-keys2 (svexlist-overridekeys-syntax-check (svex-alist-vals x.values) syntaxcheck-data))
           (ans (union bad-keys1 bad-keys2)))
        (cw "Remaining bad keys after syntax check: ~x0 out of ~x1~%~x2~%"  (len ans) (len keys) ans)
        ans)))
  ///

  (local (defthm difference-of-insert-when-in
           (equal (difference (insert a b) c)
                  (if (in a c)
                      (difference b c)
                    (insert a (difference b c))))
           :hints(("Goal" :in-theory (enable double-containment
                                             set::pick-a-point-subset-strategy)))))

  (local (defthm mergesort-of-append
           (equal (mergesort (append a b))
                  (union (mergesort a) (mergesort b)))
           :hints(("Goal" :in-theory (enable double-containment
                                             set::pick-a-point-subset-strategy)))))

  (local (defthm svexlist-overridekeys-syntax-check-of-set-difference
           (equal (svexlist-overridekeys-syntax-check x (overridekey-syntaxcheck-data
                                                         (set-difference-equal (svarlist-change-override keys nil)
                                                                               (svarlist-change-override keys2 nil))
                                                         values))
                  (difference (svexlist-overridekeys-syntax-check
                               x (overridekey-syntaxcheck-data keys values))
                              (mergesort (svarlist-change-override keys2 nil))))
           :hints (("goal" :induct (len keys)
                    :in-theory (enable svarlist-change-override
                                       set-difference-equal
                                       svarlist-fix)
                    :expand ((:with svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (svexlist-overridekeys-syntax-check
                               x (overridekey-syntaxcheck-data keys values)))
                             (:with svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (svexlist-overridekeys-syntax-check
                               x (overridekey-syntaxcheck-data nil values)))
                             (:with svexlist-overridekeys-syntax-check-in-terms-of-overridekey-syntax-check
                              (:free (a b)
                               (svexlist-overridekeys-syntax-check
                                x (overridekey-syntaxcheck-data (cons a b) values)))))))))





  (local (defthmd difference-of-union-lemma
           (and (emptyp (difference x (union y x)))
                (emptyp (difference x (union x y))))
           :hints(("Goal" :in-theory (e/d (double-containment
                                           set::pick-a-point-subset-strategy)
                                          (not))))))

  (local (defthm difference-of-union-2
           (and (equal (difference x (union y x)) nil)
                (equal (difference x (union x y)) nil))
           :hints (("goal" :use difference-of-union-lemma
                    :in-theory (e/d (emptyp)
                                    (set::union-subset-y
                                     set::subset-difference))))))


  (defret <fn>-correct
    (fsm-overridekey-transparent-p
     x (set-difference-equal (svarlist-change-override keys nil)
                             bad-keys))
    :hints(("Goal" :in-theory (e/d (fsm-overridekey-transparent-p)
                                   (overridekeys-transparent-p-when-svexlist-overridekeys-syntax-check))
            :use ((:instance overridekeys-transparent-p-when-svexlist-overridekeys-syntax-check
                   (x (svex-alist-vals (fsm->values x)))
                   (data (overridekey-syntaxcheck-data
                          (set-difference-equal (svarlist-change-override keys nil)
                                                (svarlist-change-override
                                                 (fsm-override-syntax-check x keys) nil))
                          (fsm->values x))))
                  (:instance overridekeys-transparent-p-when-svexlist-overridekeys-syntax-check
                   (x (svex-alist-vals (fsm->nextstate x)))
                   (data (overridekey-syntaxcheck-data
                          (set-difference-equal (svarlist-change-override keys nil)
                                                (svarlist-change-override
                                                 (fsm-override-syntax-check x keys) nil))
                          (fsm->values x))))))))

  (local (defthm set-diff-nil
           (set-equiv (set-difference-equal x nil) x)
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  (defret <fn>-correct-when-no-bad-keys
    (implies (not bad-keys)
             (fsm-overridekey-transparent-p
              x keys))
    :hints (("goal" :use <fn>-correct
             :in-theory (disable <fn>-correct <fn>))))

  (defret svarlist-override-p-of-<fn>
    (svarlist-override-p bad-keys nil))


  (defret <fn>-subsetp-of-keys
    (subsetp-equal bad-keys (svarlist-change-override keys nil))
    :hints (("goal" :use ((:instance svexlist-override-syntax-check-subsetp-of-keys
                           (data (overridekey-syntaxcheck-data keys (fsm->values x)))
                           (x (svex-alist-vals (fsm->values x))))
                          (:instance svexlist-override-syntax-check-subsetp-of-keys
                           (data (overridekey-syntaxcheck-data keys (fsm->values x)))
                           (x (svex-alist-vals (fsm->nextstate x)))))))))




(define svex-alists-equivalence-prune ((x svex-alist-p)
                                       (y svex-alist-p))
  :guard (equal (svex-alist-keys x) (svex-alist-keys y))
  :returns (mv (new-x svex-alist-p)
               (new-y svex-alist-p))
  :measure (+ (len x) (len y))
  :verify-guards nil
  (b* (((when (or (atom x) (atom y))) (mv nil nil))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-alists-equivalence-prune (cdr X) y))
       ((unless (mbt (and (consp (car y)) (svar-p (caar y)))))
        (svex-alists-equivalence-prune x (cdr y)))
       ((when (hons-equal (svex-fix (cdar x)) (svex-fix (cdar y))))
        (svex-alists-equivalence-prune (cdr x) (cdr y)))
       ((mv rest-x rest-y)
        (svex-alists-equivalence-prune (cdr x) (cdr y))))
    (mv (cons (mbe :logic (cons (caar x) (svex-fix (cdar x)))
                   :exec (car x))
              rest-x)
        (cons (mbe :logic (cons (caar y) (svex-fix (cdar y)))
                   :exec (car y))
              rest-y)))
  ///
  (verify-guards svex-alists-equivalence-prune
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (Defthm svex-alist-eval-under-iff
           (iff (svex-alist-eval x env)
                (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval)))))

  (defret <fn>-correct
    (implies (equal (svex-alist-keys x) (svex-alist-keys y))
             (equal (equal (svex-alist-eval new-x env)
                           (svex-alist-eval new-y env))
                    (equal (svex-alist-eval x env)
                           (svex-alist-eval y env))))
    :hints(("Goal" :in-theory (e/d (svex-alist-keys svex-alist-eval))
            :induct <call>
            :do-not-induct t)))

  (defret true-listp-of-<fn>
    (and (true-listp new-x)
         (true-listp new-y)))


  (defret keys-equiv-of-<fn>
    (implies (equal (svex-alist-keys x) (svex-alist-keys y))
             (equal (svex-alist-keys new-x) (svex-alist-keys new-y)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defret len-of-<fn>
    (equal (len new-y) (len new-x)))

  (local (in-theory (enable svex-alist-fix))))

(define svex-alists-equivalence-prune-top ((x svex-alist-p)
                                           (y svex-alist-p))
  :enabled t
  :guard (equal (svex-alist-keys x) (svex-alist-keys y))
  :prepwork ((local (defthm svex-alists-equivalence-prune-values
                      (b* ((ans (svex-alists-equivalence-prune x y))
                           ((mv new-x new-y) ans))
                        (equal (list new-x new-y) ans))
                      :hints(("Goal" :in-theory (enable svex-alists-equivalence-prune))))))
  (mbe :logic (svex-alists-equivalence-prune x y)
       :exec (b* ((- (cw "Svex-alists-equivalence-prune:~%Original length: ~x0~%" (len x)))
                  (- (cw "Original vars: ~x0~%" (len (svexlist-collect-vars (append (svex-alist-vals x) (svex-alist-vals y))))))
                  ((mv new-x new-y) (svex-alists-equivalence-prune x y))
                  (new-x-vals (svex-alist-vals new-x))
                  (new-y-vals (Svex-alist-vals new-y))
                  (all-vals (append new-x-vals new-y-vals))
                  (- (cw "Nontrivial equivs: ~x0~%" (len new-x)))
                  (- (cw "Nontrivial equiv vars: ~x0~%" (len (svexlist-collect-vars all-vals)))))
               (mv new-x new-y))))

(define svex-alists-equivalence-for-semantic-check ((x svex-alist-p)
                                                    (y svex-alist-p)
                                                    (env svex-env-p))
  :guard (equal (svex-alist-keys x) (svex-alist-keys y))
  :returns (equiv)
  :verify-guards nil
  (b* (((mv new-x new-y) (svex-alists-equivalence-prune-top x y))
       (new-len (len new-x))
       (new-x-vals (svex-alist-vals new-x))
       (new-y-vals (Svex-alist-vals new-y))
       (all-vals (append new-x-vals new-y-vals))
       (eval (svexlist-eval-for-symbolic all-vals env '((:allvars)))))
    (equal (take new-len eval)
           (nthcdr new-len eval)))
  ///
  (verify-guards svex-alists-equivalence-for-semantic-check
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (local (defthm take-of-svex-alist-eval
           (implies (and (<= (nfix n) (len x))
                         (svex-alist-p x))
                    (equal (take n (svex-alist-eval x env))
                           (svex-alist-eval (take n x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-p take)))))

  (local (defthm nthcdr-of-append
           (implies (equal (len x) (nfix n))
                    (Equal (nthcdr n (append x y))
                           y))
           :hints(("Goal" :in-theory (enable nthcdr)
                   :induct (nthcdr n x)))))

  (local (defthm take-of-append
           (implies (equal (len x) (nfix n))
                    (Equal (take n (append x y))
                           (true-list-fix x)))
           :hints(("Goal" :in-theory (enable take)
                   :induct (take n x)))))

  (local (defthm len-of-svex-alist-keys
           (equal (len (svex-alist-keys x))
                  (len (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix
                                             svex-alist-keys)))))

  (local (defthm equal-of-pairlis$
           (implies (and (not (equal vals1 vals2))
                         (true-listp vals1)
                         (true-listp vals2)
                         (equal (len vals1) (len keys))
                         (equal (len vals2) (len keys)))
                    (not (equal (pairlis$ keys vals1)
                                (pairlis$ keys vals2))))
           :hints (("Goal" :induct (list (pairlis$ keys vals1)
                                         (pairlis$ keys vals2))))))

  (local (defthmd svex-alist-eval-in-terms-of-svexlist-eval
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals
                                             svexlist-eval
                                             svex-alist-eval
                                             svex-alist-keys)))))

  (local (defthm equal-of-svexlist-eval-svex-alist-vals
           (implies (equal (svex-alist-keys x) (svex-alist-keys y))
                    (equal (equal (svexlist-eval (svex-alist-vals x) env)
                                  (svexlist-eval (svex-alist-vals y) env))
                           (equal (svex-alist-eval x env) (svex-alist-eval y env))))
           :hints (("goal"
                    :in-theory (enable svex-alist-eval-in-terms-of-svexlist-eval)))))

  (defret <fn>-correct
    (implies (equal (svex-alist-keys x) (svex-alist-keys y))
             (equal equiv
                    (equal (svex-alist-eval x env) (svex-alist-eval y env)))))

  (local (in-theory (enable svex-alist-fix))))




(define fsm-override-semantic-check-on-env ((x fsm-p)
                                                 (keys svarlist-p)
                                                 (env svex-env-p))
  :returns (ok)
  (b* (((fsm x))

       ;; Create the substitution for the equivalence check
       (subst (make-fast-alist (svarlist-overridekeys-semantic-check-subst keys x.values))))
    (and (equal (svex-alist-eval x.nextstate env)
                (svex-alist-eval (svex-alist-compose x.nextstate subst) env))
         (equal (svex-alist-eval x.values env)
                (svex-alist-eval (svex-alist-compose x.values subst) env))))
  ///
  (local (defun ind (x x1)
           (if (atom x)
               x1
             (ind (cdr x) (cdr x1)))))

  (local (defthm equal-of-append
           (implies (and (true-listp x) (true-listp x1)
                         (equal (len x) (len x1)))
                    (equal (equal (append x y) (append x1 y1))
                           (and (equal x x1) (equal y y1))))
           :hints (("goal" :induct (ind x x1)))))

  (local (defthm len-of-svex-alist-eval
           (equal (len (svex-alist-eval x env))
                  (len (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix svex-alist-eval)))))

  (fgl::def-fgl-rewrite fsm-override-semantic-check-on-env-fgl-2
    (equal (fsm-override-semantic-check-on-env x keys env)
           (b* (((fsm x))
                ;; Create the substitution for the equivalence check
                (subst (make-fast-alist (svarlist-overridekeys-semantic-check-subst keys x.values)))
                (app (append x.nextstate x.values))
                (comp (svex-alist-compose app subst)))
             (svex-alists-equivalence-for-semantic-check app comp env)))))



(defchoose fsm-override-semantic-check-badguy (env) (x keys)
  (not (fsm-override-semantic-check-on-env x keys env)))




(define fsm-override-semantic-check ((x fsm-p)
                                          (keys svarlist-p))
  :returns (ok)
  (b* (((fsm x))

       ;; Create the substitution for the equivalence check
       (subst (make-fast-alist (svarlist-overridekeys-semantic-check-subst keys x.values))))

    (and (svex-alist-eval-equiv!! x.nextstate (svex-alist-compose x.nextstate subst))
         (svex-alist-eval-equiv!! x.values (svex-alist-compose x.values subst))))

  ///
  (local (defthm svex-alist-eval-in-terms-of-keys-vals
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals
                                             svex-alist-keys
                                             svexlist-eval
                                             svex-alist-eval)))))

  (local (defthm equal-of-pairlis$-same
           (equal (equal (pairlis$ x y1) (pairlis$ x y2))
                  (equal (take (len x) y1)
                         (take (len x) y2)))
           :hints(("Goal" :in-theory (enable pairlis$ take)))))

  (defthmd fsm-override-semantic-check-in-terms-of-badguy
    (equal (fsm-override-semantic-check x keys)
           (fsm-override-semantic-check-on-env
            x keys
            (fsm-override-semantic-check-badguy x keys)))
    :hints(("Goal" :in-theory (e/d (fsm-override-semantic-check-on-env
                                    svex-alist-eval-equiv!!)
                                   (SVEX-ALIST-EVAL-OF-SVEX-COMPOSE))
            :do-not-induct t)
           (and stable-under-simplificationp
                (b* ((lit (assoc 'svexlist-eval-equiv clause))
                     (witness `(svexlist-eval-equiv-witness . ,(cdr lit))))
                  `(:use ((:instance fsm-override-semantic-check-badguy
                           (env ,witness)))
                    :expand (,lit)))))
    :rule-classes ((:definition :install-body nil))
    :otf-flg t)

  (defthm fsm-override-semantic-check-implies-on-env
    (implies (fsm-override-semantic-check x keys)
             (fsm-override-semantic-check-on-env x keys env))
    :hints(("Goal" :in-theory (enable fsm-override-semantic-check-on-env))))

  (defret fsm-overridekey-transparent-p-when-<fn>
    (b* (((fsm x)))
      (implies (and ok
                    (svarlist-override-okp (svex-alist-vars x.values))
                    (svarlist-override-okp (svex-alist-vars x.nextstate)))
               (fsm-overridekey-transparent-p x keys)))
    :hints(("Goal" :in-theory (enable fsm-overridekey-transparent-p)))))


(define fsm-override-smart-check-on-env ((x fsm-p)
                                              (keys svarlist-p)
                                              (env svex-env-p))

  (b* (((fsm x))
       ((unless (svarlist-override-okp (svexlist-collect-vars (append (svex-alist-vals x.values)
                                                                      (svex-alist-vals x.nextstate)))))
        (cw "Vars didn't satisfy svarlist-override-okp~%"))
       (bad-keys (fsm-override-syntax-check x keys))
       ((unless bad-keys) t))
    (cw "The following keys failed the override syntax check: ~x0~%" bad-keys)
    (fsm-override-semantic-check-on-env x bad-keys env)))



(defchoose fsm-override-smart-check-badguy (env) (x keys)
  (not (fsm-override-smart-check-on-env x keys env)))


(defthm fsm-overridekey-transparent-p-by-decomp
  (implies (and (fsm-overridekey-transparent-p x keys1)
                (fsm-overridekey-transparent-p x keys2))
           (fsm-overridekey-transparent-p x (append keys1 keys2)))
  :hints(("Goal" :in-theory (enable fsm-overridekey-transparent-p))))


(local
  (defcong set-equiv equal (svarlist-override-okp x) 1
    :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                      (acl2::element-p (lambda (x) (svar-override-okp x)))
                                      (acl2::element-list-final-cdr-p (lambda (x) t))
                                      (acl2::element-list-p (lambda (x) (svarlist-override-okp x))))
                           (x x) (y x-equiv)))
             :in-theory (enable svarlist-override-okp)))))




(define fsm-override-smart-check ((x fsm-p)
                                       (keys svarlist-p))
  :returns (ok)
  (b* (((fsm x))
       ((unless (svarlist-override-okp (svexlist-collect-vars (append (svex-alist-vals x.values)
                                                                      (svex-alist-vals x.nextstate)))))
        (cw "Vars didn't satisfy svarlist-override-okp~%"))
       (bad-keys (fsm-override-syntax-check x keys))
       ((unless bad-keys) t))
    (cw "The following keys failed the override syntax check: ~x0~%" bad-keys)
    (fsm-override-semantic-check x bad-keys))
  ///
  (defthmd fsm-override-smart-check-in-terms-of-badguy
    (equal (fsm-override-smart-check x keys)
           (fsm-override-smart-check-on-env
            x keys
            (fsm-override-smart-check-badguy x keys)))
    :hints(("Goal" :in-theory (enable fsm-override-smart-check-on-env)
            :cases ((fsm-override-smart-check x keys))
            :do-not-induct t)
           (and stable-under-simplificationp
                (b* ((lit (assoc 'fsm-override-semantic-check clause)))
                  `(:expand ((:with fsm-override-semantic-check-in-terms-of-badguy ,lit))
                    :use ((:instance fsm-override-smart-check-badguy
                           (env (fsm-override-semantic-check-badguy . ,(cdr lit)))))))))
    :rule-classes ((:definition :install-body nil))
    :otf-flg t)


  (defthm fsm-override-smart-check-implies-on-env
    (implies (fsm-override-smart-check x keys)
             (fsm-override-smart-check-on-env x keys env))
    :hints(("Goal" :in-theory (enable fsm-override-smart-check-on-env))))


  (defthm append-set-difference-of-subset
    (implies (subsetp-equal x y)
             (set-equiv (append x (set-difference-equal y x))
                        y))
    :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw))))


  (defret fsm-overridekey-transparent-p-when-<fn>
    (b* (((fsm x)))
      (implies ok
               (fsm-overridekey-transparent-p x keys)))
    :hints(("Goal" :in-theory (e/d (svexlist-vars-of-svex-alist-vals)
                                   (fsm-overridekey-transparent-p-by-decomp))
            :use ((:instance fsm-overridekey-transparent-p-by-decomp
                   (keys1 (set-difference-equal (svarlist-change-override keys nil)
                                                (fsm-override-syntax-check x keys)))
                   (keys2 (fsm-override-syntax-check x keys)))
                  (:instance fsm-overridekey-transparent-p-by-decomp
                   (keys1 (set-difference-equal (svarlist-change-override keys nil)
                                                (fsm-override-syntax-check x keys)))
                   (keys2 (fsm-override-syntax-check x keys))))))))







(define fsm-overridekey-transparent-p-by-assumptions-collect-args (fsm-term clause)
  (b* (((when (atom clause)) nil)
       (lit (car clause)))
    (case-match lit
      (('not ('fsm-overridekey-transparent-p !fsm-term arg))
       (cons arg (fsm-overridekey-transparent-p-by-assumptions-collect-args fsm-term (cdr clause))))
      (& (fsm-overridekey-transparent-p-by-assumptions-collect-args fsm-term (cdr clause))))))

(define nest-binary-appends (lst)

  (if (atom lst)
      ''nil
    (if (atom (cdr lst))
        (car lst)
      `(binary-append ,(car lst)
                      ,(nest-binary-appends (cdr lst))))))

(define fsm-overridekey-transparent-p-by-assumptions-bind-free (fsm-term mfc state)
  (declare (ignore state)
           (xargs :stobjs state))
  (let ((args (fsm-overridekey-transparent-p-by-assumptions-collect-args fsm-term (mfc-clause mfc))))
    `((args . ,(nest-binary-appends args)))))



(defthm fsm-overridekey-transparent-p-when-subsetp
  (implies (and (fsm-overridekey-transparent-p fsm keys1)
                (subsetp-equal (svarlist-fix keys2) (svarlist-fix keys1)))
           (fsm-overridekey-transparent-p fsm keys2))
  :hints(("Goal" :in-theory (enable fsm-overridekey-transparent-p))))


(defthm overridekeys-envs-agree-of-nil
  (iff (overridekeys-envs-agree nil impl-env spec-env spec-outs)
       (svex-envs-similar impl-env spec-env))
  :hints (("goal" :cases ((overridekeys-envs-agree nil impl-env spec-env spec-outs)))
          (and stable-under-simplificationp
               '(:in-theory (enable svex-envs-similar
                                    svar-overridekeys-envs-agree)
                 :use ((:instance overridekeys-envs-agree-implies
                        (overridekeys nil)
                        (v (svex-envs-similar-witness impl-env spec-env))))))))

(defthm fsm-overridekey-transparent-p-of-empty-keys
  (fsm-overridekey-transparent-p fsm nil)
  :hints(("Goal" :in-theory (enable fsm-overridekey-transparent-p
                                    svex-alist-overridekey-transparent-p))))

(encapsulate nil
  (local (defthm subsetp-of-append-set-diff
           (subsetp-equal keys
                          (append args (set-difference-equal keys args)))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))
  (local (defthm subsetp-set-diff
           (subsetp-equal (set-difference-equal keys args) keys)
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

  (defthm fsm-overridekey-transparent-p-by-assumptions
    ;; when rewriting a fsm-overridekey-transparent-p positive literal
    ;; (conclusion), look for (negative literals? existing theorems?), form the
    ;; append of all their arguments, and rewrite to the set-difference of our
    ;; argument and theirs.
    (implies (and (acl2::rewriting-positive-literal `(fsm-overridekey-transparent-p ,fsm ,keys))
                  (bind-free (fsm-overridekey-transparent-p-by-assumptions-bind-free
                              fsm mfc state)
                             (args))
                  (equal args-val (force-execute (svarlist-fix args)))
                  (equal keys-val (force-execute (svarlist-fix keys)))
                  (syntaxp (and (quotep args-val) (quotep keys-val)))
                   ;; we don't want to do this if it's ineffective, but if keys
                   ;; is actually nil (but wrapped up in a function
                   ;; definition), then we want to open it.
                  (implies keys-val args-val)
                  (equal remaining (force-execute (acl2::hons-set-diff keys-val args-val)))
                  (fsm-overridekey-transparent-p fsm args))
             (equal (fsm-overridekey-transparent-p fsm keys)
                    (fsm-overridekey-transparent-p fsm remaining)))
    :hints(("Goal" :in-theory (e/d (force-execute)
                                   (fsm-overridekey-transparent-p-by-decomp))
            :do-not-induct t
            :cases ((fsm-overridekey-transparent-p fsm keys))
            :use ((:instance fsm-overridekey-transparent-p-by-decomp
                   (keys1 args) (keys2 (set-difference-equal (svarlist-fix keys) (svarlist-fix args))) (x fsm)))))))

(defun def-override-transparent-collect-thms-and-keys
    (alist ;; table-alist entry mapping thmnames to keylists
     targets-set ;; hons-set
     found-set
     thms-acc)
  ;; returns thms, found-set
  (b* (((when (atom alist)) (mv thms-acc found-set))
       ((cons thm keys) (car alist))
       (target-keys (acl2::hons-int1 keys targets-set))
       (needed-keys (acl2::hons-sd1 target-keys found-set))
       ((unless needed-keys)
        (def-override-transparent-collect-thms-and-keys (cdr alist) targets-set found-set thms-acc))
       (found-set (acl2::hons-put-list needed-keys t found-set)))
    (def-override-transparent-collect-thms-and-keys (cdr alist) targets-set found-set (cons thm thms-acc))))


(defconst *def-override-transparent-template*
  '(with-output :off (event)
     (encapsulate nil
       (local (acl2::use-trivial-ancestors-check))
       (:@ :has-missing-keys
        (local
         (progn
           (defund tmp-override-transparent-keys ()
             '<missing-keys>)

           (:@ :fgl-semantic-check
            (fgl::disable-definition sv::svex-env-fix$inline)
            (fgl::disable-definition sv::svex-env-lookup)
            (memoize 'svex-mask-alist-p)

            (:@ :default-aignet-transforms
             (defun tmp-svtv-generalize-fgl-transforms-config ()
               (declare (xargs :guard t
                               :guard-hints (("goal" :in-theory (executable-counterpart-theory :here)))))
               #!aignet
               (list (change-fraig-config *fraig-default-config*
                                          :random-seed-name nil
                                          :ctrex-queue-limit 64
                                          :sim-words 2
                                          :initial-sim-words 1
                                          :initial-sim-rounds 1
                                          :ctrex-force-resim t
                                          :ipasir-limit 100
                                          :miters-only t
                                          :ipasir-recycle-count 40000
                                          )))
             (defattach fgl::fgl-aignet-transforms-config
               tmp-svtv-generalize-fgl-transforms-config)

             (define tmp-svtv-generalize-monolithic-sat-with-transforms ()
               :guard-hints (("goal" :in-theory '((booleanp))))
               (fgl::make-fgl-satlink-monolithic-sat-config :transform t))
             (defattach fgl::fgl-toplevel-sat-check-config tmp-svtv-generalize-monolithic-sat-with-transforms))


            (fgl::def-fgl-thm tmp-def-override-transparent-smart-check-fgl
              (fsm-override-smart-check-on-env <fsm> (tmp-override-transparent-keys) env)))

           (:@ (not :fgl-semantic-check)
            (defthmd def-override-transparent-open-fsm
              (implies (and (syntaxp
                             ((lambda (mfc state)
                                (declare (ignore state))
                                ;; dumb way to prevent looping
                                (not (mfc-ancestors mfc)))
                              mfc state))
                            (equal fsm-val (force-execute <fsm>))
                            (syntaxp (quotep fsm-val)))
                       (equal <fsm> fsm-val))
              :hints (("goal" :in-theory '(force-execute)))))

           (defthm tmp-def-override-transparent-smart-check
             (fsm-overridekey-transparent-p <fsm> (tmp-override-transparent-keys))
             (:@ :fgl-semantic-check
              :hints(("Goal" :in-theory '(fsm-override-smart-check-in-terms-of-badguy
                                          tmp-def-override-transparent-smart-check-fgl
                                          fsm-overridekey-transparent-p-when-fsm-override-smart-check))))
             (:@ (not :fgl-semantic-check)
              :hints (("goal" :in-theory '(def-override-transparent-open-fsm
                                            cmr::force-execute-force-execute
                                            fsm-overridekey-transparent-p-when-fsm-override-smart-check
                                            (tmp-override-transparent-keys)
                                            (fsm-override-smart-check)))))))))

       (defthm <name>
         (fsm-overridekey-transparent-p <fsm> <keys>)
         :hints (("goal" :in-theory '(fsm-overridekey-transparent-p-by-assumptions
                                      fsm-overridekey-transparent-p-by-decomp
                                      fsm-overridekey-transparent-p-of-empty-keys
                                      cmr::force-execute-force-execute)
                  :use <instances>)))

       (table def-override-transparent-table '<fsm>
              (cons (cons '<name> '<keys-val>)
                    (cdr (assoc-equal '<fsm> (table-alist 'def-override-transparent-table world))))))))



(defun def-override-transparent-fn (name fsm-expr keys-expr
                                         fgl-semantic-check
                                         use-default-aignet-transforms
                                         state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((ctx `(def-override-transparent . ,name))
       (wrld (w state))
       ((acl2::er (cons & keys-val))
        (acl2::simple-translate-and-eval keys-expr nil nil
                                         (msg "~x0" keys-expr)
                                         ctx (w state) state nil))
       (keys-set (pairlis$ keys-val nil))
       ((mv thms found-set)
        (with-fast-alist keys-set
          (def-override-transparent-collect-thms-and-keys
            (cdr (assoc-equal fsm-expr (table-alist 'def-override-transparent-table wrld)))
            keys-set nil nil)))
       (remainder (acl2::hons-sd1 keys-val found-set))
       (thms (if remainder (cons 'tmp-def-override-transparent-smart-check thms) thms))
       (- (fast-alist-free found-set)))
    (value
     (acl2::template-subst *def-override-transparent-template*
                           :atom-alist `((<fsm> . ,fsm-expr)
                                         (<keys> . ,keys-expr)
                                         (<missing-keys> . ,remainder)
                                         (<name> . ,name)
                                         (<instances> . ,thms)
                                         (<keys-val> . ,keys-val))
                           :features (append (and fgl-semantic-check '(:fgl-semantic-check))
                                             (and use-default-aignet-transforms '(:default-aignet-transforms))
                                             (and remainder '(:has-missing-keys)))))))

(defmacro def-override-transparent (name &key fsm keys fgl-semantic-check
                                         (use-default-aignet-transforms 't))
  `(make-event (def-override-transparent-fn ',name ',fsm ',keys ',fgl-semantic-check ',use-default-aignet-transforms state)))


(defxdoc def-override-transparent
  :parents (svex-decomposition-methodology def-svtv-refinement)
  :short "For a given FSM and set of keys (internal signal names), prove that the FSM is @(see override-transparent) with respect to those keys."
  :long "<p>This utility tries to prove that the given FSM is @(see
override-transparent) with respect to a set of keys, using a syntactic check
and, if necessary and the @(':fgl-semantic-check') keyword argument is
provided, a semantic check using FGL and equivalence checking.</p>

<p>Usage:</p>
@({
 (def-override-transparent name-of-theorem-to-prove
    :fsm (my-fsm) :keys (my-keys)
    ;; optional:
    :fgl-semantic-check t                ;; default: nil
    :use-default-aignet-transforms nil)  ;; default: t
  })

"
  )



;; test of def-override-transparent
(local
 (progn
   (defund my-fsm ()
     (fsm nil nil))

   (defund my-keys1 () '(a b c))

   (def-override-transparent fsm-transparent1 :fsm (my-fsm) :keys (my-keys1))


   (defund my-keys2 () '(d b c))

   (def-override-transparent fsm-transparent2 :fsm (my-fsm) :keys (my-keys2))


   (defund my-keys3 () '(a b c d))

   (def-override-transparent fsm-transparent3 :fsm (my-fsm) :keys (my-keys3))))
