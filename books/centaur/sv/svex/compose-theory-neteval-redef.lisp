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
(include-book "compose-theory-base")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))



(defun-sk exists-neteval-for-assign (value assign network env)
  (exists eval
          (and (neteval-p eval network env)
               (equal (4vec-fix value)
                      (svex-eval assign (svex-network-join-envs network eval env))))))

(deffixcong 4vec-equiv equal (exists-neteval-for-assign value assign network env) value
  :hints (("goal" :use ((:instance exists-neteval-for-assign-suff
                         (value (4vec-fix value))
                         (eval (exists-neteval-for-assign-witness value assign network env)))
                        (:instance exists-neteval-for-assign-suff
                         (eval (exists-neteval-for-assign-witness (4vec-fix value) assign network env))))
           :in-theory (disable neteval-p)
           :cases ((exists-neteval-for-assign value assign network env)))))

(deffixcong svex-equiv equal (exists-neteval-for-assign value assign network env) assign
  :hints (("goal" :use ((:instance exists-neteval-for-assign-suff
                         (assign (svex-fix assign))
                         (eval (exists-neteval-for-assign-witness value assign network env)))
                        (:instance exists-neteval-for-assign-suff
                         (eval (exists-neteval-for-assign-witness value (svex-fix assign) network env))))
           :in-theory (disable neteval-p))))

(deffixcong svex-alist-equiv equal (exists-neteval-for-assign value assign network env) network
  :hints (("goal" :use ((:instance exists-neteval-for-assign-suff
                         (network (svex-alist-fix network))
                         (eval (exists-neteval-for-assign-witness value assign network env)))
                        (:instance exists-neteval-for-assign-suff
                         (eval (exists-neteval-for-assign-witness value assign (svex-alist-fix network) env))))
           :in-theory (disable neteval-p))))

(deffixcong svex-env-equiv equal (exists-neteval-for-assign value assign network env) env
  :hints (("goal" :use ((:instance exists-neteval-for-assign-suff
                         (env (svex-env-fix env))
                         (eval (exists-neteval-for-assign-witness value assign network env)))
                        (:instance exists-neteval-for-assign-suff
                         (eval (exists-neteval-for-assign-witness value assign network (svex-env-fix env)))))
           :in-theory (disable neteval-p))))

(define neteval-witness-for-assign ((value 4vec-p)
                                    (assign svex-p)
                                    (network svex-alist-p)
                                    (env svex-env-p))
  :returns (neteval-witness neteval-witness-p)
  (ec-call
   (neteval-witness-fix
    (neteval-p-witness (exists-neteval-for-assign-witness (4vec-fix value)
                                                          (svex-fix assign)
                                                          (svex-alist-fix network)
                                                          (svex-env-fix env))
                       (svex-alist-fix network) (svex-env-fix env))))
  ///
  ;; ugh, all this fixing
  (defthm exists-neteval-for-assign-redef
    (equal (exists-neteval-for-assign value assign network env)
           (let ((eval (neteval-witness->neteval (neteval-witness-for-assign value assign network env)
                                                 network env)))
             (equal (4vec-fix value)
                    (svex-eval assign (svex-network-join-envs network eval env)))))
    :hints(("Goal" :in-theory (e/d (;; exists-neteval-for-assign
                                    ;; neteval-p
                                    )
                                   (exists-neteval-for-assign-suff
                                    neteval-p-suff
                                    exists-neteval-for-assign
                                    neteval-p))
            :use ((:instance exists-neteval-for-assign-suff
                   (eval (neteval-witness->neteval (neteval-witness-for-assign value assign network env)
                                                   network env))
                   (value (4vec-fix value))
                   (assign (svex-fix assign))
                   (network (svex-alist-fix network))
                   (env (svex-env-fix env)))
                  (:instance neteval-p-suff
                   (neteval (neteval-witness->neteval (neteval-witness-for-assign value assign network env)
                                                      network env))
                   (neteval-witness (neteval-witness-for-assign value assign network env))
                   (network (svex-alist-fix network))
                   (env (svex-env-fix env)))
                  (:instance exists-neteval-for-assign
                   (value (4vec-fix value))
                   (assign (svex-fix assign))
                   (network (svex-alist-fix network))
                   (env (svex-env-fix env)))
                  (:instance neteval-p
                   (neteval (EXISTS-NETEVAL-FOR-ASSIGN-WITNESS (4VEC-FIX VALUE)
                                                               (SVEX-FIX ASSIGN)
                                                               (SVEX-ALIST-FIX NETWORK)
                                                               (SVEX-ENV-FIX ENV)))
                   (network (svex-alist-fix network))
                   (env (svex-env-fix env)))))))

  (defthm exists-neteval-for-assign-redef-suff
    (implies (let ((eval (neteval-witness->neteval neteval-witness network env)))
               (equal (4vec-fix value)
                      (svex-eval assign (svex-network-join-envs network eval env))))
             (exists-neteval-for-assign value assign network env))
    :hints (("goal" :use ((:instance exists-neteval-for-assign-suff
                           (eval (neteval-witness->neteval neteval-witness network env)))
                          (:instance neteval-p-suff
                           (neteval (neteval-witness->neteval neteval-witness network env))))
             :in-theory (disable exists-neteval-for-assign-suff
                                 neteval-p-suff)))))

(define neteval-p-badguy-aux ((keys svarlist-p)
                                 (eval svex-env-p)
                                 (network svex-alist-p)
                                 (env svex-env-p))
  ;; Env must only bind primary input signals, not internal ones.
  :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                (svex-alist-keys network)))
  :verify-guards nil
  :returns (badguy (iff (svar-p badguy) badguy))
  (b* (((when (atom keys)) nil)
       (signal (svar-fix (car keys)))
       ((unless (svex-env-boundp signal eval))
        (neteval-p-badguy-aux (cdr keys) eval network env))
       (value (svex-env-lookup signal eval))
       (assign (svex-lookup signal network))
       ((unless assign) signal)
       ((unless (exists-neteval-for-assign value assign network env))
        signal))
    (neteval-p-badguy-aux (cdr keys) eval network env))
  ///
  
  (defret <fn>-when-exists
    (implies (and (member-equal signal (svarlist-fix keys))
                  (svex-env-boundp signal eval)
                  (let* ((val (svex-env-lookup signal eval))
                         (assign (svex-lookup signal network)))
                    (not (and assign
                              (exists-neteval-for-assign val assign network env)))))
             (let ((signal badguy))
               (and (member-equal signal (svarlist-fix keys))
                    (svex-env-boundp signal eval)
                    (let* ((val (svex-env-lookup signal eval))
                         (assign (svex-lookup signal network)))
                    (not (and assign
                              (exists-neteval-for-assign val assign network env)))))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup svex-env-boundp)
                                   (exists-neteval-for-assign
                                    exists-neteval-for-assign-redef)))))


  (local (in-theory (disable exists-neteval-for-assign
                             exists-neteval-for-assign-redef)))
  (local (in-theory (enable svex-env-fix))))

(define neteval-p-badguy ((eval svex-env-p)
                             (network svex-alist-p)
                             (env svex-env-p))
  :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                (svex-alist-keys network)))
  :verify-guards nil
  :returns (badguy (iff (svar-p badguy) badguy))
  (neteval-p-badguy-aux (alist-keys (svex-env-fix eval))
                           eval network env)
  ///

  (local (defthm svarlist-p-of-alist-keys
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (local (defthm member-of-alist-keys
           (iff (member V (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret <fn>-when-exists
    (implies (and (svex-env-boundp signal eval)
                  (let* ((val (svex-env-lookup signal eval))
                         (assign (svex-lookup signal network)))
                    (not (and assign
                              (exists-neteval-for-assign val assign network env)))))
             (let ((signal badguy))
               (and (svex-env-boundp signal eval)
                    (let* ((val (svex-env-lookup signal eval))
                         (assign (svex-lookup signal network)))
                    (not (and assign
                              (exists-neteval-for-assign val assign network env)))))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup svex-env-boundp)
                                   (exists-neteval-for-assign
                                    exists-neteval-for-assign-redef
                                    neteval-p-badguy-aux-when-exists))
            :use ((:instance neteval-p-badguy-aux-when-exists
                   (keys (alist-keys (svex-env-fix eval)))
                   (signal (svar-fix signal))))))))

(local (in-theory (disable exists-neteval-for-assign
                           exists-neteval-for-assign-redef)))

(define neteval-p-by-badguy ((eval svex-env-p)
                                (network svex-alist-p)
                                (env svex-env-p))
  :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                (svex-alist-keys network)))
  :verify-guards nil
  (let ((signal (neteval-p-badguy eval network env)))
    (implies (svex-env-boundp signal eval)
             (let* ((val (svex-env-lookup signal eval))
                    (assign (svex-lookup signal network)))
               (and assign
                    (exists-neteval-for-assign val assign network env)))))
  ///
  (defthm neteval-p-by-badguy-implies
    (implies (and (neteval-p-by-badguy eval network env)
                  (svex-env-boundp signal eval))
             (let* ((val (svex-env-lookup signal eval))
                    (assign (svex-lookup signal network)))
               (and assign
                    (exists-neteval-for-assign val assign network env))))
    :hints (("goal" :use neteval-p-badguy-when-exists
             :in-theory (disable neteval-p-badguy-when-exists)))))


;; We want to show that neteval-p-by-badguy is the same as neteval-p.

;; First, show neteval-p-by-badguy implies neteval-p.  For this, we know
;; that for any signal bound in eval, it has an assignment (it is bound in the
;; network) and there is an neteval of the assignment under env that
;; evaluates to its value in eval.  Use this to build an neteval-witness such that
;; neteval-witness->evalution produces an equivalent neteval.
(define neteval-p-compute-witness-aux ((keys svarlist-p)
                                          (eval svex-env-p)
                                          (network svex-alist-p)
                                          (env svex-env-p))
  :verify-guards nil
  :returns (neteval-witness neteval-witness-p)
  (b* (((when (atom keys))
        nil)
       (signal (svar-fix (car keys)))
       ((unless (svex-env-boundp signal eval))
        (neteval-p-compute-witness-aux (cdr keys) eval network env))
       (value (svex-env-lookup signal eval))
       (assign (svex-lookup signal network))
       ;; The assign must exist...
       (neteval-witness (neteval-witness-for-assign value assign network env)))
    (cons (cons signal neteval-witness)
          (neteval-p-compute-witness-aux (cdr keys) eval network env)))
  ///
  (defret <fn>-when-not-member
    (implies (not (member-equal (svar-fix signal) (svarlist-fix keys)))
             (not (hons-assoc-equal signal neteval-witness))))

  (defret <fn>-when-not-svar-p
    (implies (not (svar-p signal))
             (not (hons-assoc-equal signal neteval-witness))))

  (local (defthm svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp k x))
                    (equal (svex-env-lookup k x) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

  (defret <fn>-produces-equivalent-eval-when-neteval-p-by-badguy
    (implies (and (neteval-p-by-badguy eval network env)
                  (member-equal (svar-fix signal) (svarlist-fix keys)))
             (and (iff (hons-assoc-equal signal neteval-witness)
                       (and (svar-p signal)
                            (svex-env-boundp signal eval)))
                  (equal (svex-env-lookup signal (neteval-witness->neteval neteval-witness network env))
                         (svex-env-lookup signal eval))))
    :hints (("goal" :induct <call>
             :in-theory (enable svarlist-fix))
            (and stable-under-simplificationp
                 '(:use ((:instance neteval-p-by-badguy-implies
                          (signal (car keys))))
                   :in-theory (e/d (exists-neteval-for-assign-redef)
                                   (neteval-p-by-badguy-implies)))))))

(define neteval-p-compute-witness ((eval svex-env-p)
                                      (network svex-alist-p)
                                      (env svex-env-p))
  :returns (neteval-witness neteval-witness-p)
  :verify-guards nil
  (neteval-p-compute-witness-aux (alist-keys (svex-env-fix eval)) eval network env)
  ///
  (local (defthm svarlist-p-of-alist-keys
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (local (defthmd member-of-alist-keys
           (iff (member V (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm member-of-alist-keys-of-svex-env-fix
           (iff (member V (alist-keys (svex-env-fix x)))
                (and (svar-p v)
                     (svex-env-boundp v x)))
           :hints(("Goal" :in-theory (enable member-of-alist-keys svex-env-boundp)))))

  (local (defthm svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp k x))
                    (equal (svex-env-lookup k x) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

  (defret <fn>-when-not-boundp
    (implies (not (svex-env-boundp signal eval))
             (not (hons-assoc-equal signal neteval-witness)))
    :hints(("Goal" :in-theory (enable svex-env-boundp)
            :cases ((svar-p signal)))))

  (defret <fn>-produces-equivalent-eval-when-neteval-p-by-badguy
    (implies (neteval-p-by-badguy eval network env)
             (and (iff (hons-assoc-equal signal neteval-witness)
                       (and (svar-p signal)
                            (svex-env-boundp signal eval)))
                  (equal (svex-env-lookup signal (neteval-witness->neteval neteval-witness network env))
                         (svex-env-lookup signal eval))))
    :hints (("goal" :cases ((svex-env-boundp signal eval))
             :in-theory (disable SVEX-ENV-LOOKUP-OF-NETEVAL-WITNESS->NETEVAL))))

  (local (defthm svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp k x))
                    (equal (svex-env-lookup k x) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp))))))
       


(defthm neteval-p-by-badguy-implies-neteval-p
  (implies (neteval-p-by-badguy eval network env)
           (neteval-p eval network env))
  :hints(("Goal" :in-theory (e/d (svex-envs-equivalent)
                                 (neteval-p-suff))
          :use ((:instance neteval-p-suff
                 (neteval eval)
                 (neteval-witness (neteval-p-compute-witness eval network env)))))))



;; Next we want to show neteval-p implies neteval-p-by-badguy.  So we
;; need to take the neteval-p-witness provided by neteval-p and, together
;; with an arbitrary signal witnessing neteval-p-by-badguy, produce a
;; witness for exists-neteval-for-assign.  This witness 
(defsection neteval-p-implies-neteval-p-by-badguy
  (local (defthm svex-env-lookup-when-equiv-neteval-witness->neteval
           (implies (svex-envs-equivalent eval
                                          (neteval-witness->neteval x network env))
                    (equal (svex-env-lookup key eval)
                           (let* ((look (hons-assoc-equal (svar-fix key) (neteval-witness-fix x)))
                                  (witness (cdr look))
                                  (assign (svex-lookup key network)))
                             (if look
                                 (svex-eval assign
                                            (svex-network-join-envs network
                                                                    (neteval-witness->neteval witness network env)
                                                                    env))
                               (4vec-x)))))))


  (local (defthm lookup-in-witness-when-equiv-neteval
           (implies (and (svex-env-boundp key eval)
                         (not (hons-assoc-equal (svar-fix key) witness)))
                    (not (svex-envs-equivalent eval (neteval-witness->neteval witness network env))))
           :hints (("goal" :use ((:instance svex-env-boundp-of-neteval-witness->neteval
                                  (x witness)))))))

  (defthm neteval-p-implies-neteval-p-by-badguy
    (implies (neteval-p eval network env)
             (neteval-p-by-badguy eval network env))
    :hints (("goal" :in-theory (enable neteval-p neteval-p-by-badguy))
            (and stable-under-simplificationp
                 (cond ((eq (car (car (last clause))) 'svex-lookup)
                        '(:use ((:instance svex-env-boundp-of-neteval-witness->neteval
                                 (x (neteval-p-witness eval network env))
                                 (key (neteval-p-badguy eval network env))))
                          :in-theory (disable svex-env-boundp-of-neteval-witness->neteval)))
                       (t '(:use ((:instance exists-neteval-for-assign-redef-suff
                                   (Value (svex-env-lookup (neteval-p-badguy eval network env) eval))
                                   (assign (svex-lookup (neteval-p-badguy eval network env) network))
                                   (neteval-witness
                                    (CDR (HONS-ASSOC-EQUAL
                                          (SVAR-FIX (NETEVAL-P-BADGUY EVAL NETWORK ENV))
                                          (NETEVAL-P-WITNESS EVAL NETWORK ENV))))))
                            :in-theory (disable exists-neteval-for-assign-redef-suff))))))))

(in-theory (disable neteval-p neteval-p-suff))

(defsection neteval-p-redef

  (local (Defthm neteval-p-is-by-badguy
           (equal (neteval-p eval network env)
                  (neteval-p-by-badguy eval network env))
           :hints (("goal" :cases ((neteval-p eval network env))))))

  (defthmd neteval-p-redef
    (equal (neteval-p eval network env)
           (let ((signal (neteval-p-badguy eval network env)))
             (implies (svex-env-boundp signal eval)
                      (let* ((val (svex-env-lookup signal eval))
                             (assign (svex-lookup signal network)))
                        (and assign
                             (exists-neteval-for-assign val assign network env))))))
    :hints (("goal" :in-theory (enable neteval-p-by-badguy)))
    :rule-classes :definition)


  (defthmd neteval-p-implies
    (implies (and (neteval-p eval network env)
                  (svex-env-boundp signal eval))
             (let* ((val (svex-env-lookup signal eval))
                    (assign (svex-lookup signal network)))
               (and assign
                    (exists-neteval-for-assign val assign network env))))))






(defsection neteval-p-of-cons
  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup key (cons (cons var val) rest))
                  (if (and (svar-p var)
                           (equal (svar-fix key) var))
                      (4vec-fix val)
                    (svex-env-lookup key rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix)))))

  (local (defthm svex-env-boundp-of-cons
           (equal (svex-env-boundp key (cons (cons var val) rest))
                  (if (and (svar-p var)
                           (equal (svar-fix key) var))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix)))))

  (defthm neteval-p-of-cons
    (implies (and (neteval-p rest network env)
                  (svex-lookup signal network)
                  (neteval-p sig-eval network env))
             (neteval-p (cons (cons signal (svex-eval
                                            (svex-lookup signal network)
                                            (svex-network-join-envs network sig-eval env)))
                              rest)
                        network env))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable neteval-p-implies))))))
