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
(include-book "eval")
(include-book "alist-equiv")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))


;; Theory for evaluation of not-necessarily-monotonic networks.

;; For networks of monotonic update functions, a least fixpoint is a sensible
;; spec for a complete network evaluation (neteval for short).  E.g., for 4v-sexprs, which had strictly
;; monotonic semantics, we had the half-lattice relation x [ 1, x [ 0, x [ z,
;; we said a complete neteval is a least fixpoint: specifically, a valuation
;; function v (a mapping from signals to values) is a fixpoint if for any
;; signal s, signal s with assignment function f_s, v(s) = f_s(v).  It is a
;; least fixpoint if for every fixpoint v', v [= v' (pointwise).  Because of
;; monotonicity we can show that there is always a least fixpoint for every
;; network of 4v-sexpr assignments.

;; For SV, we don't have monotonicity because we support nonmonotonic
;; SystemVerilog operators like ===.  As a consequence we can't show that we
;; have a unique least fixpoint.  In fact, there are simple networks that have
;; multiple equally valid least fixpoints.  E.g.:

;; assign a = (a === 1'bx) ?
;;                         (b === 1'bx) ?
;;                                       1'b0
;;                                       : b 
;;                         : a;
;; 
;; assign b = (b === 1'bx) ?
;;                         (a === 1'bx) ?
;;                                       1'b1
;;                                       : a 
;;                         : b;

;; We can usually reach a least fixpoint by starting all internal signals with
;; a value of X and evaluating assignments until a fixpoint is reached.
;; However, in this case the fixpoint we reach depends whether we evaluate the
;; assignment for a or b first.  If we evaluate a's assignment first, then both
;; signals become 0, and if we evaluate b's first, both signals become 1.

;; Therefore, for networks of SVEX assignments we use a weaker notion of an
;; neteval.  Namely:

;; A valuation of signals is a neteval if for each signal, its value either
;; is X or is the value of the signal's assignment function applied to an(other)
;; neteval of the signals.

;; A neteval may be a fixpoint, but isn't necessarily.  We can't ensure
;; that there exists a fixpoint neteval; e.g.
;;    assign a = (a === 1'b1) ? 1'b0 : 1'b1;
;; It may be possible to ensure that if there exists a fixpoint network
;; evaluation, then we find one; but at the moment we don't make that
;; guarantee.

;; We can't define a neteval directly because its definition
;; involves a recursion over an existential quantifier.  Instead we define a
;; neteval witness and define a neteval as an assignment
;; for which a neteval witness exists.

;; A neteval witness is a mapping from signals (svars) to neteval
;; witnesses.  If a signal is not mapped, then its value is X.  A neteval
;; witness produces a valuation (svex-env) given a network of assignments
;; (svex-alist) recursively.
(fty::defmap neteval-witness :key-type svar :val-type neteval-witness :true-listp t)


(define svex-network-join-envs ((network svex-alist-p) ;; assignments for internal signals
                                (internal-env svex-env-p)
                                (input-env svex-env-p))
  :returns (env svex-env-p)
  (append (svex-env-extract (svex-alist-keys network) internal-env)
          (svex-env-fix input-env))
  ///
  (defret boundp-of-<fn>
    (iff (svex-env-boundp var env)
         (or (svex-lookup var network)
             (svex-env-boundp var input-env))))

  (defret lookup-of-fn
    (equal (svex-env-lookup var env)
           (if (svex-lookup var network)
               (svex-env-lookup var internal-env)
             (svex-env-lookup var input-env))))

  (defcong svex-envs-equivalent svex-envs-similar
    (svex-network-join-envs network internal-env input-env) 2)

  (defcong svex-envs-equivalent svex-envs-equivalent
    (svex-network-join-envs network internal-env input-env) 3)

  (defcong svex-alist-eval-equiv svex-envs-equivalent
    (svex-network-join-envs network internal-env input-env) 1))



;; (local
;;  (defsection svex-eval-of-append-extract
;;    (local
;;     (defthm svex-env-lookup-when-not-svex-env-boundp
;;       (implies (not (svex-env-boundp k x))
;;                (equal (svex-env-lookup k x)
;;                       (4vec-x)))
;;       :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))


;;    (local
;;     (defthm svex-env-boundp-when-not-intersectp
;;       (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env)) vars))
;;                     (member-equal var vars)
;;                     (svarlist-p vars))
;;                (not (svex-env-boundp var env)))
;;       :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

;;    (local
;;     (defthm svex-env-boundp-when-subsetp
;;       (implies (and (subsetp (alist-keys (svex-env-fix env)) vars)
;;                     (not (member-equal (svar-fix var) vars))
;;                     (svarlist-p vars))
;;                (not (svex-env-boundp var env)))
;;       :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

;;    (local (in-theory (disable acl2::intersectp-equal-commute)))
   

;;    (std::defret-mutual svex-eval-of-append-extract
;;      (defret <fn>-of-append-extract
;;        :pre-bind ((env (append (svex-env-extract vars env1) env2)))
;;        (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env2))
;;                                             (svarlist-fix vars)))
;;                      (subsetp-equal (alist-keys (svex-env-fix env1))
;;                                     (svarlist-fix vars)))
;;                 (equal val
;;                        (svex-eval x (append env1 env2))))
;;        :hints ('(:expand ((:free (env) <call>)))
;;                ;; (and stable-under-simplificationp
;;                ;;      '(:in-theory (enable svex-env-boundp svex-env-lookup)))
;;                )
;;        :fn svex-eval)
;;      (defret <fn>-of-append-extract
;;        :pre-bind ((env (append (svex-env-extract vars env1) env2)))
;;        (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env2))
;;                                             (svarlist-fix vars)))
;;                      (subsetp-equal (alist-keys (svex-env-fix env1))
;;                                     (svarlist-fix vars)))
;;                 (equal vals
;;                        (svexlist-eval x (append env1 env2))))
;;        :hints ('(:expand ((:free (env) <call>))))
;;        :fn svexlist-eval)
;;      :mutual-recursion svex-eval)))



(define neteval-witness->neteval ((x neteval-witness-p)
                                  (network svex-alist-p)
                                  (env svex-env-p))

  ;; Env must only bind primary input signals, not internal ones.
  :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                (svex-alist-keys network)))
  :verify-guards nil
  :measure (neteval-witness-count x)
  :returns (neteval svex-env-p)
  (b* ((x (neteval-witness-fix x))
       ((when (atom x))
        nil)
       ((cons signal witness) (car x))
       (assign (svex-lookup signal network))
       ((unless assign)
        (neteval-witness->neteval (cdr x) network env)))
    (cons (cons signal
                (svex-eval assign
                           (svex-network-join-envs network 
                                                   (neteval-witness->neteval witness network env)
                                                   env)))
          (neteval-witness->neteval (cdr x) network env)))
  ///
  (defret keys-subsetp-of-<fn>
    (subsetp-equal (alist-keys neteval) (svex-alist-keys network))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp key neteval)
         (and (hons-assoc-equal (svar-fix key) (neteval-witness-fix x))
              (svex-lookup key network)))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp)
                                   (hons-assoc-equal-of-neteval-witness-fix)))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key neteval)
           (let* ((look (hons-assoc-equal (svar-fix key) (neteval-witness-fix x)))
                  (witness (cdr look))
                  (assign (svex-lookup key network)))
             (if look
                 (svex-eval assign (svex-network-join-envs network
                                                           (neteval-witness->neteval witness network env)
                                                           env))
               (4vec-x))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup)
                                   (hons-assoc-equal-of-neteval-witness-fix)))))


  (defcong svex-alist-eval-equiv equal (neteval-witness->neteval x network env) 2)

  (verify-guards neteval-witness->neteval))


(defun-sk neteval-p (neteval network env)
  (exists neteval-witness
          (svex-envs-equivalent neteval
                                (neteval-witness->neteval neteval-witness network env))))

(deffixcong svex-env-equiv equal (neteval-p neteval network env) neteval
  :hints (("goal" :use ((:instance neteval-p-suff
                         (neteval (svex-env-fix neteval))
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness (svex-env-fix neteval) network env)))))))


(deffixcong svex-env-equiv equal (neteval-p neteval network env) env
  :hints (("goal" :use ((:instance neteval-p-suff
                         (env (svex-env-fix env))
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness neteval network  (svex-env-fix env))))))))

(deffixcong svex-alist-equiv equal (neteval-p neteval network env) network
  :hints (("goal" :use ((:instance neteval-p-suff
                         (network (svex-alist-fix network))
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness neteval (svex-alist-fix network) env)))))))

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


;; Rephrasing: An env EVAL is a neteval (under network NETWORK, env ENV)
;; iff for each signal bound in EVAL, the signal has an assignment expression
;; ASSIGN in NETWORK, and there exists a neteval SIG-EVAL such that that
;; the evaluation of ASSIGN under the environment mapping signals bound in
;; NETWORK to their values in SIG-EVAL and others to their values in ENV equals
;; the signal's value in EVAL.

;; Note that not all signals bound in NETWORK need be bound in an neteval.
;; Trivially, an empty env is an neteval.  Signals in NETWORK that are not
;; bound in an neteval are implicitly assigned X.  However, this implicit
;; assignment of X is special because it doesn't need to be justified by
;; evaluation of the signal's assignment under another neteval.

(defthm svex-env-boundp-of-nil
  (not (svex-env-boundp k nil))
  :hints(("Goal" :in-theory (enable svex-env-boundp))))


(defthm neteval-p-of-nil
  (neteval-p nil network env)
  :hints(("Goal" :in-theory (enable neteval-p-redef))))

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


(include-book "compose")


(define svex-compose-dfs-memo-correct-p ((memo svex-svex-memo-p)
                                         (assigns svex-alist-p)
                                         (env svex-env-p))
  :verify-guards nil
  (if (atom memo)
      t
    (and (or (atom (car memo))
             (b* ((key (svex-fix (caar memo)))
                  (val (svex-fix (cdar memo))))
               (exists-neteval-for-assign (svex-eval val env) key assigns env)))
         (svex-compose-dfs-memo-correct-p (cdr memo) assigns env)))
  ///
  (local (in-theory (enable svex-svex-memo-fix)))

  (defthm svex-compose-dfs-memo-correct-p-implies
    (implies (and (svex-compose-dfs-memo-correct-p memo assigns env)
                  (hons-assoc-equal (svex-fix key) (svex-svex-memo-fix memo)))
             (exists-neteval-for-assign
              (svex-eval (cdr (hons-assoc-equal (svex-fix key) (svex-svex-memo-fix memo))) env)
              key assigns env)))

  (defthm svex-compose-dfs-memo-correct-p-implies2
    (implies (and (svex-compose-dfs-memo-correct-p memo assigns env)
                  (equal assign-look (hons-assoc-equal (svex-fix key) (svex-svex-memo-fix memo)))
                  assign-look)
             (exists-neteval-for-assign
              (svex-eval (cdr assign-look) env) key assigns env)))

  (defthm svex-compose-dfs-memo-correct-p-of-cons
    (equal (svex-compose-dfs-memo-correct-p (cons (cons key val) memo) assigns env)
           (and (svex-compose-dfs-memo-correct-p memo assigns env)
                (exists-neteval-for-assign
                 (svex-eval val env) key assigns env)))))



(local (include-book "std/lists/sets" :dir :system))

;; Want to show that when DFS on an expression is complete, its internal-signal
;; variables are bound in the updates, except for those that are in the stack.

;; Complication: memoized results may have been recorded when different
;; variables were on the stack.  But either those variables are still on the
;; stack, or else they were added to the updates when they were removed from
;; the stack.  So we have an invariant that all internal-signal variables of
;; svexes bound in the memo table are either on the stack or in the updates.

(std::defret-mutual boundp-preserved-of-svex-compose-dfs
  (defret boundp-preserved-of-<fn>
    (implies (svex-lookup var updates)
             (equal (svex-lookup var updates1)
                    (svex-lookup var updates)))
    :hints ('(:expand (<call>)))
    :fn svex-compose-dfs)
  (defret boundp-preserved-of-<fn>
    (implies (svex-lookup var updates)
             (equal (svex-lookup var updates1)
                    (svex-lookup var updates)))
    :hints ('(:expand (<call>)))
    :fn svexlist-compose-dfs)
  :mutual-recursion svex-compose-dfs)

;; (defun-sk svex-compose-dfs-memo-vars-okp (memo assigns updates stack)
;;   (forall (var svex)
;;           (implies (and (svex-lookup svex memo)
;;                         (member-equal (svar-fix var) (svex-vars svex))
;;                         (not (hons-assoc-equal (svar-fix var) stack))
;;                         (svex-lookup var assigns))
;;                    (svex-lookup var updates)))
;;   :rewrite :direct)

;; (in-theory (Disable svex-compose-dfs-memo-vars-okp
;;                     svex-compose-dfs-memo-vars-okp-necc))

;; (implies (and (not (hons-assoc-equal (svar-fix var) stack))
;;               (svex-lookup var assigns)
;;               (not (svex-lookup var updates)))

;; (defun-sk svex-compose-dfs-memo-var-okp (var memo assigns updates stack)
;;   (forall svex
;;           (implies (svex-lookup svex memo)
;;                    (not (member-equal (svar-fix var) (svex-vars svex)))))
;;   :rewrite :direct)

;; (in-theory (Disable svex-compose-dfs-memo-var-okp
;;                     svex-compose-dfs-memo-var-okp-necc))

(define svex-compose-dfs-memo-var-okp ((var svar-p)
                                       (memo svex-svex-memo-p))
  (if (atom memo)
      t
    (and (or (atom (car memo))
             (not (member-equal (svar-fix var) (svex-vars (caar memo)))))
         (svex-compose-dfs-memo-var-okp var (cdr memo))))
  ///
  ;; (defthm svex-compose-dfs-memo-var-okp-implies
  ;;   (implies (and (svex-compose-dfs-memo-var-okp var memo)
  ;;                 (hons-assoc-equal (svex-fix svex) (svex-svex-memo-fix memo)))
  ;;            (not (member-equal (svar-fix var) (svex-vars svex))))
  ;;   :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

  (defthmd svex-compose-dfs-memo-var-okp-implies
    (implies (and (svex-compose-dfs-memo-var-okp var memo)
                  (hons-assoc-equal (svex-fix svex) (svex-svex-memo-fix memo)))
             (not (member-equal var (svex-vars svex))))
    :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

  (defthmd svex-compose-dfs-memo-var-okp-implies2
    (implies (and (svex-compose-dfs-memo-var-okp var memo)
                  (member-equal (svar-fix var) (svex-vars svex)))
             (not (hons-assoc-equal svex (svex-svex-memo-fix memo))))
    :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))


  (defthm svex-compose-dfs-memo-var-okp-of-acons
    (implies (svex-compose-dfs-memo-var-okp var memo)
             (iff (svex-compose-dfs-memo-var-okp var (cons (cons key val) memo))
                  (not (member-equal (svar-fix var) (svex-vars key))))))


  (local (in-theory (enable svex-svex-memo-fix))))

(local (in-theory (enable svex-compose-dfs-memo-var-okp-implies2
                          svex-compose-dfs-memo-var-okp-implies)))


(std::defret-mutual boundp-of-svex-compose-dfs
  (defret boundp-of-<fn>
    (implies (and (not (hons-assoc-equal (svar-fix var) stack))
                  (svex-lookup var assigns)
                  (svex-compose-dfs-memo-var-okp var memo))
             (and (implies (not (svex-lookup var updates1))
                           (svex-compose-dfs-memo-var-okp var memo1))
                  (implies (member (svar-fix var) (svex-vars x))
                           (svex-lookup var updates1))))
    :hints ('(:expand (<call>
                       (svex-vars x))))
    :fn svex-compose-dfs)
  (defret boundp-of-<fn>
    (implies (and (not (hons-assoc-equal (svar-fix var) stack))
                  (svex-lookup var assigns)
                  (svex-compose-dfs-memo-var-okp var memo))
             (and (implies (not (svex-lookup var updates1))
                           (svex-compose-dfs-memo-var-okp var memo1))
                  (implies (member (svar-fix var) (svexlist-vars x))
                           (svex-lookup var updates1))))
    :hints ('(:expand (<call>
                       (svexlist-vars x))))
    :fn svexlist-compose-dfs)
  :mutual-recursion svex-compose-dfs)

(std::defret-mutual not-boundp-by-stack-of-svex-compose-dfs
  (defret not-boundp-by-stack-of-<fn>
    (implies (and (not (svex-lookup var updates))
                  (hons-assoc-equal (svar-fix var) stack))
             (not (svex-lookup var updates1)))
    :hints ('(:expand (<call>)))
    :fn svex-compose-dfs)
  (defret not-boundp-by-stack-of-<fn>
    (implies (and (not (svex-lookup var updates))
                  (hons-assoc-equal (svar-fix var) stack))
             (not (svex-lookup var updates1)))
    :hints ('(:expand (<call>)))
    :fn svexlist-compose-dfs)
  :mutual-recursion svex-compose-dfs)

(std::defret-mutual not-boundp-by-assigns-of-svex-compose-dfs
  (defret not-boundp-by-assigns-of-<fn>
    (implies (and (not (svex-lookup var updates))
                  (not (svex-lookup var assigns)))
             (not (svex-lookup var updates1)))
    :hints ('(:expand (<call>)))
    :fn svex-compose-dfs)
  (defret not-boundp-by-assigns-of-<fn>
    (implies (and (not (svex-lookup var updates))
                  (not (svex-lookup var assigns)))
             (not (svex-lookup var updates1)))
    :hints ('(:expand (<call>)))
    :fn svexlist-compose-dfs)
  :mutual-recursion svex-compose-dfs)



(local (in-theory (enable svex-env-acons)))

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

(local (include-book "centaur/misc/equal-sets" :dir :system))

(defret update-keys-subsetp-of-assigns-keys-of-<fn>
  (implies (subsetp-equal (svex-alist-keys updates) (svex-alist-keys assigns))
           (subsetp-equal (svex-alist-keys updates1) (svex-alist-keys assigns)))
  :hints ((acl2::set-reasoning))
  :fn svex-compose-dfs)

(defret update-keys-subsetp-of-assigns-keys-of-<fn>
  (implies (subsetp-equal (svex-alist-keys updates) (svex-alist-keys assigns))
           (subsetp-equal (svex-alist-keys updates1) (svex-alist-keys assigns)))
  :hints ((acl2::set-reasoning))
  :fn svexlist-compose-dfs)



(defret vars-subsetp-of-<fn>
  (subsetp-equal (set-difference-equal
                  (intersectp-equal (svex-vars x) (svex-alist-keys assigns))
                  (alist-keys stack))
                 (svex-alist-keys updates1))
  :hints ((acl2::set-reasoning))
  :fn svex-compose-dfs)

(defret vars-subsetp-of-<fn>
  (subsetp-equal (set-difference-equal
                  (intersectp-equal (svexlist-vars x) (svex-alist-keys assigns))
                  (alist-keys stack))
                 (svex-alist-keys updates1))
  :hints ((acl2::set-reasoning))
  :fn svexlist-compose-dfs)

(local (defthm member-alist-keys-is-hons-assoc-equal
         (iff (member-equal k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(defret stack-not-intersectp-of-<fn>
  (implies (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates)))
           (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates1))))
  :hints ((acl2::set-reasoning))
  :fn svex-compose-dfs)

(defret stack-not-intersectp-of-<fn>
  (implies (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates)))
           (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates1))))
  :hints ((acl2::set-reasoning))
  :fn svexlist-compose-dfs)

(defsection svex-eval-of-append-when-reduce-equiv
  (local (defthm consp-of-hons-assoc-equal
           (iff (consp (hons-assoc-equal k x))
                (hons-assoc-equal k x))))

  (local (defthm equal-cons-of-svex-env-reducce
           (implies (not (hons-assoc-equal var envb))
                    (not (equal (cons (cons var val) rest)
                                (svex-env-reduce vars envb))))
           :hints(("Goal" :in-theory (enable svex-env-reduce)))))

  (local (defthm svex-env-boundp-when-equal-svex-env-reduce
           (implies (and (bind-free (and (eq enva 'enva) '((envb . envb))) (envb))
                         (equal (svex-env-reduce vars enva)
                                (svex-env-reduce vars envb))
                         (member-equal (svar-fix var) (svarlist-fix vars)))
                    (iff (svex-env-boundp var enva)
                         (svex-env-boundp var envb)))
           :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-boundp svarlist-fix)))))
  (local (defthm svex-env-lookup-when-equal-svex-env-reduce
           (implies (and (bind-free (and (eq enva 'enva) '((envb . envb))) (envb))
                         (equal (svex-env-reduce vars enva)
                                (svex-env-reduce vars envb))
                         (member-equal (svar-fix var) (svarlist-fix vars)))
                    (equal (svex-env-lookup var enva)
                           (svex-env-lookup var envb)))
           :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-lookup svarlist-fix)))))


  (defthm-svex-eval-flag
    (defthm svex-eval-of-append-when-reduce-equiv
      (implies (and (equal (svex-env-reduce vars enva)
                           (svex-env-reduce vars envb))
                    (subsetp-equal (svex-vars x) (svarlist-fix vars)))
               (equal (svex-eval x (append enva rest))
                      (svex-eval x (append envb rest))))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x))))
      :flag expr)

    (defthm svexlist-eval-of-append-when-reduce-equiv
      (implies (and (equal (svex-env-reduce vars enva)
                           (svex-env-reduce vars envb))
                    (subsetp-equal (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-eval x (append enva rest))
                      (svexlist-eval x (append envb rest))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (defthm-svex-eval-flag
    (defthm svex-eval-of-append-when-reduce-equiv-2
      (implies (and (equal (svex-env-reduce vars enva)
                           (svex-env-reduce vars envb))
                    (subsetp-equal (svex-vars x) (svarlist-fix vars)))
               (equal (svex-eval x (append rest enva))
                      (svex-eval x (append rest envb))))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x))))
      :flag expr)

    (defthm svexlist-eval-of-append-when-reduce-equiv-2
      (implies (and (equal (svex-env-reduce vars enva)
                           (svex-env-reduce vars envb))
                    (subsetp-equal (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-eval x (append rest enva))
                      (svexlist-eval x (append rest envb))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (local (defthm equal-cons-of-svex-alist-reduce
           (implies (not (svex-lookup var envb))
                    (not (equal (cons (cons var val) rest)
                                (svex-alist-reduce vars envb))))
           :hints(("Goal" :in-theory (enable svex-alist-reduce)))))


  (local (defthm svex-lookup-when-equal-svex-alist-reduce
           (implies (and (bind-free (and (eq enva 'enva) '((envb . envb))) (envb))
                         (equal (svex-alist-reduce vars enva)
                                (svex-alist-reduce vars envb))
                         (member-equal (svar-fix var) (svarlist-fix vars)))
                    (equal (svex-lookup var enva)
                           (svex-lookup var envb)))
           :hints(("Goal" :in-theory (enable svex-alist-reduce svarlist-fix)))))

  (defthm-svex-compose*-flag
    (defthm svex-compose*-when-reduce-equiv
      (implies (and (equal (svex-alist-reduce vars enva)
                           (svex-alist-reduce vars envb))
                    (subsetp-equal (svex-vars x) (svarlist-fix vars)))
               (equal (svex-compose* x enva)
                      (svex-compose* x envb)))
      :hints ('(:expand ((:free (env) (svex-compose* x env))
                         (svex-vars x))))
      :flag svex-compose*)

    (defthm svexlist-compose*-when-reduce-equiv
      (implies (and (equal (svex-alist-reduce vars enva)
                           (svex-alist-reduce vars envb))
                    (subsetp-equal (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-compose* x enva)
                      (svexlist-compose* x envb)))
      :hints ('(:expand ((:free (env) (svexlist-compose* x env))
                         (svexlist-vars x))))
      :flag svexlist-compose*)))
  

;; (local (defthmd svex-env-reduce-redef
;;          (equal (svex-env-reduce vars env)
;;                 (if (atom vars)
;;                     nil
;;                   (if (svex-env-boundp (car vars) env)
;;                       (cons (cons (svar-fix (car vars)) (svex-env-lookup (car vars) env))
;;                             (svex-env-reduce (cdr vars) env))
;;                     (svex-env-reduce (cdr vars) env))))
;;          :hints(("Goal" :in-theory (enable svex-env-reduce svex-env-boundp svex-env-lookup)))
;;          :rule-classes :definition))

(defret svex-env-reduce-vars-of-<fn>
  (implies (subsetp-equal (intersection-equal (svarlist-fix vars)
                                              (svex-alist-keys assigns))
                          (append (svex-alist-keys updates)
                                  (alist-keys stack)))
           (equal (svex-env-reduce vars (svex-alist-eval updates1 env))
                  (svex-env-reduce vars (svex-alist-eval updates env))))
  :hints (("goal" :induct (len vars)
           :in-theory (enable svarlist-fix svex-env-reduce-redef intersection-equal)))
  :fn svex-compose-dfs)

(defret svex-env-reduce-vars-of-<fn>
  (implies (subsetp-equal (intersection-equal (svarlist-fix vars)
                                              (svex-alist-keys assigns))
                          (append (svex-alist-keys updates) (alist-keys stack)))
           (equal (svex-env-reduce vars (svex-alist-eval updates1 env))
                  (svex-env-reduce vars (svex-alist-eval updates env))))
  :hints (("goal" :induct (len vars)
           :in-theory (enable svarlist-fix svex-env-reduce-redef intersection-equal)))
  :fn svexlist-compose-dfs)


(define svex-compose-dfs-memo-vars-okp ((memo svex-svex-memo-p)
                                        (assigns svex-alist-p)
                                        (updates svex-alist-p)
                                        (stack alistp))
  (if (atom memo)
      t
    (and (or (atom (car memo))
             (b* ((key (svex-fix (caar memo)))
                  (vars (svex-vars key)))
               (subsetp-equal (intersection-equal vars (svex-alist-keys assigns))
                              (append (svex-alist-keys updates) (alist-keys stack)))))
         (svex-compose-dfs-memo-vars-okp (cdr memo) assigns updates stack)))
  ///
  (local (in-theory (enable svex-svex-memo-fix)))

  (defthm svex-compose-dfs-memo-vars-okp-implies
    (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                  (hons-assoc-equal key (svex-svex-memo-fix memo)))
             (b* ((vars (svex-vars key)))
               (subsetp-equal (intersection-equal vars (svex-alist-keys assigns))
                              (append (svex-alist-keys updates) (alist-keys stack))))))

  (defthm svex-compose-dfs-memo-vars-okp-implies-var
    (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                  (hons-assoc-equal key (svex-svex-memo-fix memo)))
             (b* ((vars (svex-vars key)))
               (implies (and (member-equal (svar-fix var) vars)
                             (svex-lookup var assigns)
                             (not (hons-assoc-equal (svar-fix var) stack)))
                        (svex-lookup var updates))))
    :hints(("Goal" :in-theory (e/d () (svex-compose-dfs-memo-vars-okp-implies
                                       svex-compose-dfs-memo-vars-okp))
            :use svex-compose-dfs-memo-vars-okp-implies)
           (acl2::set-reasoning)))

  (defthm svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp
    (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                  (svex-lookup var assigns)
                  (not (hons-assoc-equal (svar-fix var) stack))
                  (case-split (not (svex-lookup var updates))))
             (svex-compose-dfs-memo-var-okp var memo))
    :hints(("Goal" :in-theory (e/d (svex-compose-dfs-memo-vars-okp
                                    svex-compose-dfs-memo-var-okp))
            :induct (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
           (acl2::set-reasoning))))


(define svex-compose-dfs-memo-vars-okp-badguy ((memo svex-svex-memo-p)
                                               (assigns svex-alist-p)
                                               (updates svex-alist-p)
                                               (stack alistp))
  :returns (mv svex var)
  (if (atom memo)
      (mv nil nil)
    (if (atom (car memo))
        (svex-compose-dfs-memo-vars-okp-badguy (cdr memo) assigns updates stack)
      (b* ((key (svex-fix (caar memo)))
           (vars (svex-vars key)))
        (if (subsetp-equal (intersection-equal vars (svex-alist-keys assigns))
                           (append (svex-alist-keys updates) (alist-keys stack)))
            (svex-compose-dfs-memo-vars-okp-badguy (cdr memo) assigns updates stack)
          (mv key
              (car (set-difference-equal (intersection-equal vars (svex-alist-keys assigns))
                                         (append (svex-alist-keys updates) (alist-keys stack)))))))))
  ///
  (local (defthmd car-set-difference-witnesses-subset
           (iff (subsetp-equal a b)
                (not (let ((k (car (set-difference-equal a b))))
                       (and (member k a)
                            (not (member k b))))))
           :hints(("Goal" :in-theory (enable subsetp set-difference-equal)))))

  (local (in-theory (enable svex-svex-memo-fix)))

  (defret svex-compose-dfs-memo-vars-okp-by-badguy
    (implies (or (not (hons-assoc-equal svex (svex-svex-memo-fix memo)))
                 (not (member-equal (svar-fix var) (svex-vars svex)))
                 (not (svex-lookup var assigns))
                 (hons-assoc-equal (svar-fix var) stack)
                 (svex-lookup var updates))
             (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
    :hints(("Goal" :in-theory (enable svex-compose-dfs-memo-vars-okp)
            :induct <call>)
           (and stable-under-simplificationp
                '(:in-theory (enable car-set-difference-witnesses-subset)))))

  (defthmd svex-compose-dfs-memo-vars-okp-redef
    (equal (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (mv-let (svex var)
             (svex-compose-dfs-memo-vars-okp-badguy memo assigns updates stack)
             (and (or (not (hons-assoc-equal svex (svex-svex-memo-fix memo)))
                      (not (member-equal (svar-fix var) (svex-vars svex)))
                      (not (svex-lookup var assigns))
                      (hons-assoc-equal (svar-fix var) stack)
                      (svex-lookup var updates))
                  t)))
    :hints (("goal" :cases ((svex-compose-dfs-memo-vars-okp memo assigns updates stack))
             :in-theory (disable svex-compose-dfs-memo-vars-okp-badguy)))
    :rule-classes :definition)

  (defthmd svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef
    (equal (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (mv-let (svex var)
             (svex-compose-dfs-memo-vars-okp-badguy memo assigns updates stack)
             (declare (ignore svex))
             (implies (and (svex-lookup var assigns)
                           (not (hons-assoc-equal (svar-fix var) stack))
                           (not (svex-lookup var updates)))
                      (svex-compose-dfs-memo-var-okp var memo))))
    :hints(("Goal" :cases ((svex-compose-dfs-memo-vars-okp memo assigns updates stack))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-compose-dfs-memo-vars-okp-redef))))
    :otf-flg t
    :rule-classes :definition))


(defret svex-compose-dfs-memo-vars-okp-of-<fn>
  (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (svex-compose-dfs-memo-vars-okp memo1 assigns updates1 stack))
  :hints ((and stable-under-simplificationp
               `(:expand ((:with svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef ,(car (last clause))))
                 :do-not-induct t)))
  :fn svex-compose-dfs)

(defret svex-compose-dfs-memo-vars-okp-of-<fn>
  (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (svex-compose-dfs-memo-vars-okp memo1 assigns updates1 stack))
  :hints ((and stable-under-simplificationp
               `(:expand ((:with svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef ,(car (last clause))))
                 :do-not-induct t)))
  :fn svexlist-compose-dfs)


(defret svex-vars-subsetp-of-<fn>
  (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (subsetp-equal (intersection-equal (svex-vars x)
                                              (svex-alist-keys assigns))
                          (append (svex-alist-keys updates1) (alist-keys stack))))
  :hints ((acl2::set-reasoning))
  :fn svex-compose-dfs)

(defret svex-vars-subsetp-of-<fn>
  (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
           (subsetp-equal (intersection-equal (svexlist-vars x)
                                              (svex-alist-keys assigns))
                          (append (svex-alist-keys updates1) (alist-keys stack))))
  :hints ((acl2::set-reasoning))
  :fn svexlist-compose-dfs)


(define svex-compose-dfs-vars-cond ((vars svarlist-p)
                                    (assigns svex-alist-p)
                                    (updates svex-alist-p)
                                    (stack alistp))
  (subsetp-equal (intersection-equal (svarlist-fix vars)
                                     (svex-alist-keys assigns))
                 (append (svex-alist-keys updates) (alist-keys stack)))
  ///
  (local (in-theory (disable acl2::commutativity-of-append-under-set-equiv)))

  (defret svex-compose-dfs-vars-cond-of-<fn>
    (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (svex-compose-dfs-vars-cond (svex-vars x) assigns updates1 stack))
    :fn svex-compose-dfs)

  (defret svex-compose-dfs-vars-cond-of-<fn>
    (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (svex-compose-dfs-vars-cond (svexlist-vars x) assigns updates1 stack))
    :fn svexlist-compose-dfs)

  (defret svex-alist-reduce-vars-of-<fn>when-svex-compose-dfs-vars-cond
    (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
             (equal (svex-alist-reduce vars updates1)
                    (svex-alist-reduce vars updates)))
    :hints(("Goal" :in-theory (enable svex-alist-reduce
                                      intersection-equal)))
    :fn svex-compose-dfs)

  (defret svex-alist-reduce-vars-of-<fn>when-svex-compose-dfs-vars-cond
    (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
             (equal (svex-alist-reduce vars updates1)
                    (svex-alist-reduce vars updates)))
    :hints(("Goal" :in-theory (enable svex-alist-reduce
                                      intersection-equal)))
    :fn svexlist-compose-dfs)

  (defret svex-env-reduce-vars-of-<fn>-when-svex-compose-dfs-vars-cond
    (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
             (equal (svex-env-reduce vars (svex-alist-eval updates1 env))
                    (svex-env-reduce vars (svex-alist-eval updates env))))
    :fn svex-compose-dfs)

  (defret svex-env-reduce-vars-of-<fn>-when-svex-compose-dfs-vars-cond
    (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
             (equal (svex-env-reduce vars (svex-alist-eval updates1 env))
                    (svex-env-reduce vars (svex-alist-eval updates env))))
    :fn svexlist-compose-dfs))


(defret svex-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-compose* y updates1)
                  (svex-compose* y updates)))
  :hints (("goal" :use ((:instance svex-compose*-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svex-compose-dfs)


(defret svex-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-compose* y updates1)
                  (svex-compose* y updates)))
  :hints (("goal" :use ((:instance svex-compose*-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svex-compose-dfs)

(defret svexlist-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svexlist-vars y) assigns updates stack)
           (equal (svexlist-compose* y updates1)
                  (svexlist-compose* y updates)))
  :hints (("goal" :use ((:instance svexlist-compose*-when-reduce-equiv
                         (x y)
                         (vars (svexlist-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svex-compose-dfs)


(defret svex-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-compose* y updates1)
                  (svex-compose* y updates)))
  :hints (("goal" :use ((:instance svex-compose*-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svexlist-compose-dfs)

(defret svexlist-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svexlist-vars y) assigns updates stack)
           (equal (svexlist-compose* y updates1)
                  (svexlist-compose* y updates)))
  :hints (("goal" :use ((:instance svexlist-compose*-when-reduce-equiv
                         (x y)
                         (vars (svexlist-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svexlist-compose-dfs)




(defret svex-eval-of-append-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-eval y (append (svex-alist-eval updates1 env) env1))
                  (svex-eval y (append (svex-alist-eval updates env) env1))))
  :hints (("goal" :use ((:instance svex-eval-of-append-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva (svex-alist-eval updates1 env))
                         (envb (svex-alist-eval updates env))
                         (rest env1)))))
  :fn svex-compose-dfs)

(defret svex-eval-of-append-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-eval y (append (svex-alist-eval updates1 env) env1))
                  (svex-eval y (append (svex-alist-eval updates env) env1))))
  :hints (("goal" :use ((:instance svex-eval-of-append-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva (svex-alist-eval updates1 env))
                         (envb (svex-alist-eval updates env))
                         (rest env1)))))
  :fn svexlist-compose-dfs)


(defret svex-eval-of-append-updates-of-<fn>-2
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-eval y (append env1 (svex-alist-eval updates1 env)))
                  (svex-eval y (append env1 (svex-alist-eval updates env)))))
  :hints (("goal" :use ((:instance svex-eval-of-append-when-reduce-equiv-2
                         (x y)
                         (vars (svex-vars y))
                         (enva (svex-alist-eval updates1 env))
                         (envb (svex-alist-eval updates env))
                         (rest env1)))))
  :fn svex-compose-dfs)

(defret svex-eval-of-append-updates-of-<fn>-2
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-eval y (append env1 (svex-alist-eval updates1 env)))
                  (svex-eval y (append env1 (svex-alist-eval updates env)))))
  :hints (("goal" :use ((:instance svex-eval-of-append-when-reduce-equiv-2
                         (x y)
                         (vars (svex-vars y))
                         (enva (svex-alist-eval updates1 env))
                         (envb (svex-alist-eval updates env))
                         (rest env1)))))
  :fn svexlist-compose-dfs)

(defsection svex-eval-of-append-svex-env-extract-when-no-intersect
  (local (defthm consp-of-hons-assoc-equal
           (iff (consp (hons-assoc-equal k x))
                (hons-assoc-equal k x))))

  (local (defthmd hons-assoc-equal-to-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member k (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthmd svex-env-boundp-redef
           (equal (svex-env-boundp var env)
                  (consp (hons-assoc-equal (svar-fix var) (svex-env-fix env))))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (local (defthmd svex-env-lookup-redef
           (equal (svex-env-lookup var env)
                  (4vec-fix (cdr (hons-assoc-equal (svar-fix var) (svex-env-fix env)))))
           :hints (("goal" :in-theory (enable svex-env-lookup)))))

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append x y))
                  (or (hons-assoc-equal k x)
                      (hons-assoc-equal k y)))))

  (local (in-theory (disable hons-assoc-equal-of-svex-env-fix)))

  (defthm-svex-eval-flag
    (defthm svex-eval-of-append-svex-env-extract-when-no-intersect
      (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svarlist-fix vars)))
                    (subsetp-equal (alist-keys (svex-env-fix env1)) (svarlist-fix vars)))
               (equal (svex-eval x (append (svex-env-extract vars env1) env2))
                      (svex-eval x (append env2 env1))))
      :hints ('(:expand ((:free (env) (svex-eval x env))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-env-lookup-redef svex-env-boundp-redef)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (hons-assoc-equal-to-member-alist-keys)
                                     (member-alist-keys-is-hons-assoc-equal))))
              (acl2::set-reasoning))
      :flag expr)
    (defthm svexlist-eval-of-append-svex-env-extract-when-no-intersect
      (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svarlist-fix vars)))
                    (subsetp-equal (alist-keys (svex-env-fix env1)) (svarlist-fix vars)))
               (equal (svexlist-eval x (append (svex-env-extract vars env1) env2))
                      (svexlist-eval x (append env2 env1))))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :flag list)))




;; (std::defret-mutual eval-of-append-svex-compose-dfs
;;   (defret eval-of-append-<fn>
;;     (implies (subsetp-equal (intersection-equal (svex-vars x)
;;                                                 (svex-alist-vars assigns))
;;                             (set-difference-equal
;;                              (svex-alist-vars updates)
;;                              (alist-keys stack)))
;;              (equal (svex-eval (append (svex-alist-eval
;;                                         (mv-nth 1 (

;; (defun-sk neteval-p-of-svex-compose-dfs-cond (x assigns updates memo stack env)
;;   (forall env1



;; (defthm exists-neteval-for-assign-when-proper-env
;;   (implies (not (intersectp-equal (alist-keys (svex-env-fix env))
;;                                   (svex-alist-keys network)))
;;            (equal (exists-neteval-for-assign value assign network env)
;;                   (let ((eval (exists-neteval-for-assign-witness value assign network env)))
;;                     (and (neteval-p eval network env)
;;                          (equal (4vec-fix value)
;;                                 (svex-eval assign
;;                                            (append env eval)))))))
;;   :hints(("Goal" :in-theory (enable exists-neteval-for-assign))))

(defsection neteval-p-implies-alist-keys-subsetp
  (local (defthm member-alist-keys-is-svex-env-boundp
           (iff (member-equal k (alist-keys (svex-env-fix x)))
                (and (svar-p k) (svex-env-boundp k x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (defthm neteval-p-implies-alist-keys-subsetp
    (implies (neteval-p eval network env)
             (subsetp-equal (alist-keys (svex-env-fix eval))
                            (svex-alist-keys network)))
    :hints (("goal" :in-theory (enable neteval-p-implies))
            (acl2::set-reasoning))))



;; We want to take a composition step applied to some network and show that an
;; evaluation of the composed network produces an evaluation of the original
;; network.  So we take a neteval-witness for the composed network and map it
;; to one for the original network.  We assume here that the composition step
;; is of the form:
;; (cons (cons var (svex-compose (svex-lookup var network)
;;                               (svex-alist-reduce composed-vars network)))
;;       network).


(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(define svex-network-compose-step ((var svar-p)
                                   (composed-vars svarlist-p)
                                   (network svex-alist-p))
  :guard (svex-lookup var network)
  :returns (new-network svex-alist-p)
  (cons (cons (svar-fix var)
              (svex-compose (svex-lookup var network)
                            (svex-alist-reduce composed-vars network)))
        (svex-alist-fix network))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (equal (svar-fix key) (svar-fix var))
               (svex-compose (svex-lookup var network)
                             (svex-alist-reduce composed-vars network))
             (svex-lookup key network)))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret svex-network-join-envs-of-<fn>
    (implies (svex-lookup var network)
             (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
                                   (svex-network-join-envs network env1 env2)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent)))))


(local (defthm neteval-witness-p-of-append
         (implies (and (neteval-witness-p x)
                       (neteval-witness-p y))
                  (neteval-witness-p (append x y)))))

(local (fty::deflist neteval-witnesslist :elt-type neteval-witness :true-listp t))

(local (defthm neteval-witness-p-of-pairlis$
         (implies (and (svarlist-p x)
                       (neteval-witnesslist-p y)
                       (equal (len x) (len y)))
                  (neteval-witness-p (pairlis$ x y)))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(local (deffixcong neteval-witness-equiv neteval-witness-equiv (append x y) x))
(local (deffixcong neteval-witness-equiv neteval-witness-equiv (append x y) y))

(local (include-book "clause-processors/generalize" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))

(define neteval-witness-for-compose-step ((var svar-p)
                                          (composed-vars svarlist-p)
                                          (new-witness neteval-witness-p))
  :returns (witness neteval-witness-p)
  (b* (((when (atom new-witness)) nil)
       ((unless (mbt (and (consp (car new-witness)) (svar-p (caar new-witness)))))
        (neteval-witness-for-compose-step var composed-vars (cdr new-witness)))
       ((cons wit-var sub-witness) (car new-witness))
       (sub-witness2 (neteval-witness-for-compose-step
                      var composed-vars sub-witness))
       ((unless (equal wit-var (svar-fix var)))
        (cons (cons wit-var sub-witness2)
              (neteval-witness-for-compose-step var composed-vars (cdr new-witness))))
       (sub-witness3
        (append (pairlis$ (svarlist-fix composed-vars)
                          (repeat (len composed-vars) sub-witness2))
                sub-witness2)))
    (cons (cons wit-var sub-witness3)
          (neteval-witness-for-compose-step var composed-vars (cdr new-witness))))
  ///
  (local (in-theory (enable neteval-witness-fix)))

  (deffixequiv neteval-witness-for-compose-step)

  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key witness)
           (let ((new-look (hons-assoc-equal key (neteval-witness-fix new-witness))))
             (and new-look
                  (let ((sub-witness2
                         (neteval-witness-for-compose-step
                          var composed-vars (cdr new-look))))
                    (if (equal key (svar-fix var))
                        (cons key (append (pairlis$ (svarlist-fix composed-vars)
                                                    (repeat (len composed-vars) sub-witness2))
                                          sub-witness2))
                      (cons key sub-witness2))))))
    :hints (("goal" :induct (len new-witness)
             :expand (<call>))))

  (local (defthm neteval-witness->neteval-of-append
           (equal (neteval-witness->neteval (append x y) network env)
                  (append (neteval-witness->neteval x network env)
                          (neteval-witness->neteval y network env)))
           :hints(("Goal" 
                   :expand ((:free (x y) (neteval-witness->neteval (cons x y) network env))
                            (append x y)
                            (neteval-witness->neteval x network env))
                   :induct (neteval-witness->neteval x network env)
                   :in-theory (enable (:i neteval-witness->neteval)))
                  (and stable-under-simplificationp
                       '(:expand ((neteval-witness->neteval y network env)))))))

  (local (defthmd neteval-witness->neteval-of-pairlis$-repeat-lemma
           (implies (svarlist-p keys)
                    (equal (neteval-witness->neteval (pairlis$ keys (repeat (len keys) x)) network env)
                           (svex-env-reduce keys
                                            (svex-alist-eval network
                                                             (svex-network-join-envs
                                                              network
                                                              (neteval-witness->neteval x network env)
                                                              env)))))
           :hints(("Goal" :in-theory (enable svex-env-reduce-redef pairlis$)
                   :expand ((:free (x y) (neteval-witness->neteval (cons x y) network env))
                            (neteval-witness->neteval nil network env))
                   :induct (len keys)))))

  (local (defthm neteval-witness->neteval-of-pairlis$-repeat
           (equal (neteval-witness->neteval (pairlis$ (svarlist-fix keys) (repeat (len keys) x)) network env)
                  (svex-env-reduce keys
                                   (svex-alist-eval network
                                                    (svex-network-join-envs
                                                     network
                                                     (neteval-witness->neteval x network env)
                                                     env))))
           :hints (("goal" :use ((:instance neteval-witness->neteval-of-pairlis$-repeat-lemma
                                  (keys (svarlist-fix keys))))))))

  (local (defthm acl2-count-of-hons-assoc-equal
           (<= (acl2-count (hons-assoc-equal k x)) (acl2-count x))
           :rule-classes :linear))


  (local (defun correct-induction (var composed-vars network new-witness env)
           (declare (xargs :measure (acl2-count (neteval-witness-fix new-witness))
                           :hints (("goal" :in-theory (disable hons-assoc-equal-of-neteval-witness-fix)))))
           (b* ((witness (neteval-witness-for-compose-step
                          var composed-vars new-witness))
                (badguy (svex-envs-equivalent-witness
                         (neteval-witness->neteval
                          witness network env)
                         (neteval-witness->neteval
                          new-witness
                          (svex-network-compose-step var composed-vars network)
                          env)))
                (look (hons-assoc-equal (svar-fix badguy) (neteval-witness-fix new-witness)))
                ((unless look) (list witness badguy)))
             (correct-induction var composed-vars network (cdr look) env))))


  (local (defthm svex-env-boundp-of-svex-env-reduce
           (iff (svex-env-boundp key (svex-env-reduce vars x))
                (and (member-equal (svar-fix key) (svarlist-fix vars))
                     (svex-env-boundp key x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-reduce)))))

  (local (defthm lemma
           (svex-envs-equivalent (SVEX-NETWORK-JOIN-ENVS
                                  NETWORK
                                  (APPEND
                                   (SVEX-ENV-REDUCE
                                    COMPOSED-VARS
                                    (SVEX-ALIST-EVAL
                                     NETWORK
                                     neteval1))
                                   neteval)
                                  ENV)
                                 (APPEND
                                  (SVEX-ENV-REDUCE
                                   COMPOSED-VARS
                                   (SVEX-ALIST-EVAL
                                    NETWORK
                                    neteval1))
                                  (SVEX-NETWORK-JOIN-ENVS
                                   NETWORK
                                   neteval
                                   ENV)))
           :hints(("Goal" :in-theory (enable svex-envs-equivalent))
                  (and stable-under-simplificationp
                       (let ((wit (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                         `(:clause-processor (acl2::simple-generalize-cp
                                              clause
                                              '((,wit . badguy-key)))))))))

  

  (defret <fn>-correct
    (implies (svex-lookup var network)
             (svex-envs-equivalent
              (neteval-witness->neteval
               witness network env)
              (neteval-witness->neteval
               new-witness
               (svex-network-compose-step var composed-vars network)
               env)))
    :hints(("Goal" ;; :in-theory (enable svex-envs-equivalent)
            :induct (correct-induction var composed-vars network new-witness env))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                (let ((wit (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                  `(:clause-processor (acl2::simple-generalize-cp
                                       clause
                                       '((,wit . badguy-key))))))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable svex-network-join-envs)))
           )
    :otf-flg t))
       
    



(local (include-book "centaur/misc/dfs-measure" :dir :system))


(deffixcong svex-alist-equiv svex-alist-equiv (append x y) x)
(deffixcong svex-alist-equiv svex-alist-equiv (append x y) y)

(defsection svex-compose-dfs-is-svex-compose*

  (define svex-compose-dfs-memo-correct ((memo svex-svex-memo-p)
                                         (updates svex-alist-p))
    (b* (((when (atom memo)) t)
         ((unless (mbt (consp (car memo))))
          (svex-compose-dfs-memo-correct (cdr memo) updates))
         ((cons x x1) (car memo)))
      (and (svex-equiv x1 (svex-compose* x updates))
           (svex-compose-dfs-memo-correct (cdr memo) updates)))
    ///
    (defthm svex-compose-dfs-memo-correct-implies
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (hons-assoc-equal x (svex-svex-memo-fix memo)))
               (equal (cdr (hons-assoc-equal x (svex-svex-memo-fix memo)))
                      (svex-compose* x updates)))
      :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

    (defthm svex-compose-dfs-memo-correct-of-cons
      (equal (svex-compose-dfs-memo-correct (cons (cons x x1) rest) updates)
             (and (svex-equiv x1 (svex-compose* x updates))
                  (svex-compose-dfs-memo-correct rest updates))))

    (defthm svex-compose-dfs-memo-correct-of-nil
      (svex-compose-dfs-memo-correct nil updates))

    (local
     (defthm-svex-compose*-flag
       (defthm svex-compose*-of-cons-when-subsetp
         (implies (and (subsetp-equal (intersection-equal (svex-vars x)
                                                          vars1)
                                      (append vars2 (svex-alist-keys a)))
                       (member-equal (svar-fix var) vars1)
                       (not (member-equal (svar-fix var) vars2))
                       (not (svex-lookup var a)))
                  (equal (svex-compose* x (cons (cons var val) a))
                         (svex-compose* x a)))
         :hints ('(:expand ((:free (a) (svex-compose* x a))
                            (svex-vars x)))
                 (acl2::set-reasoning))
         :flag svex-compose*)
       (defthm svexlist-compose*-of-cons-when-subsetp
         (implies (and (subsetp-equal (intersection-equal (svexlist-vars x)
                                                          vars1)
                                      (append vars2 (svex-alist-keys a)))
                       (member-equal (svar-fix var) vars1)
                       (not (member-equal (svar-fix var) vars2))
                       (not (svex-lookup var a)))
                  (equal (svexlist-compose* x (cons (cons var val) a))
                         (svexlist-compose* x a)))
         :hints ('(:expand ((:free (a) (svexlist-compose* x a))
                            (svexlist-vars x))))
         :flag svexlist-compose*)))

    (defthm svex-compose-dfs-memo-correct-of-cons-updates
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (bind-free '((stack . stack) (assigns . assigns)) (stack assigns))
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (svex-lookup var assigns)
                    (not (svex-lookup var updates))
                    (not (hons-assoc-equal (svar-fix var) stack)))
               (svex-compose-dfs-memo-correct memo (cons (cons var val) updates)))
      :hints(("Goal" :in-theory (enable svex-compose-dfs-memo-vars-okp))))

    (local (in-theory (enable svex-svex-memo-fix))))

  (std::defret-mutual svex-compose-dfs-redef-memo-invar
    (defret <fn>-memo-invar
      (implies (and (svex-compose-dfs-memo-correct mem updates)
                    (svex-compose-dfs-memo-vars-okp mem assigns updates stack))
               (svex-compose-dfs-memo-correct mem updates1))
      :hints ('(:expand (<call>)
                :in-theory (enable svex-acons)))
      :fn svex-compose-dfs)
    (defret <fn>-memo-invar
      (implies (and (svex-compose-dfs-memo-correct mem updates)
                    (svex-compose-dfs-memo-vars-okp mem assigns updates stack))
               (svex-compose-dfs-memo-correct mem updates1))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)


  (std::defret-mutual svex-compose-dfs-redef
    (defret <fn>-is-svex-compose*
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
               (and (svex-compose-dfs-memo-correct memo1 updates1)
                    (equal x1
                           (svex-compose* x updates1))))
      :hints ('(:expand (<call>
                         (:free (a) (svex-compose* x a)))
                :in-theory (enable svex-acons)))
      :fn svex-compose-dfs)
    (defret <fn>-is-svexlist-compose*
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
               (and (svex-compose-dfs-memo-correct memo1 updates1)
                    (equal x1
                           (svexlist-compose* x updates1))))
      :hints ('(:expand (<call>
                         (:free (a) (svexlist-compose* x a)))))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs))
                    

(defines neteval-witness-for-svex-compose-dfs
  :flag-local nil
  (define neteval-witness-for-svex-compose-dfs ((x svex-p "svex we're traversing")
                                                (assigns svex-alist-p "alist of assign stmts")
                                                (updates svex-alist-p "alist of composed update fns")
                                                (memo svex-svex-memo-p "memo table for internal nodes")
                                                (stack "alist of seen vars"
                                                       alistp)
                                                (witness neteval-witness-p))
    :verify-guards nil
    :returns (new-witness neteval-witness-p)
    :well-founded-relation acl2::nat-list-<
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svex-count x))

    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (memo (svex-svex-memo-fix memo))
         (updates (mbe :logic (svex-alist-fix updates) :exec updates)))
      (svex-case x
        :quote (neteval-witness-fix witness)
        :call (b* ((look (hons-get x memo))
                   ((when look) (neteval-witness-fix witness)))
                (neteval-witness-for-svexlist-compose-dfs x.args assigns updates memo stack witness))
        :var (b* ((update-fn (svex-fastlookup x.name updates))
                  ((when update-fn) (neteval-witness-fix witness))
                  (assign (svex-fastlookup x.name assigns))
                  ((unless assign)
                   (neteval-witness-fix witness))
                  ((when (hons-get x.name stack))
                   (neteval-witness-fix witness))
                  (stack (hons-acons x.name t stack))
                  ((mv & updates1 &)
                   (svex-compose-dfs assign assigns updates nil stack))
                  (witness (neteval-witness-for-compose-step x.name
                                                             ;; (set-difference-equal (svex-vars x.name)
                                                             ;;                       (alist-keys stack))
                                                             (svex-alist-keys updates1)
                                                             witness))
                  (witness
                   (neteval-witness-for-svex-compose-dfs assign assigns updates nil stack witness))
                  (- (acl2::fast-alist-pop stack)))
               witness))))
  (define neteval-witness-for-svexlist-compose-dfs ((x svexlist-p)
                                (assigns svex-alist-p)
                                (updates svex-alist-p)
                                (memo svex-svex-memo-p)
                                (stack alistp)
                                (witness neteval-witness-p))
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svexlist-count x))
    :returns (new-witness neteval-witness-p)
    (b* ((updates (mbe :logic (svex-alist-fix updates) :exec updates))
         (memo (svex-svex-memo-fix memo))
         ((when (atom x)) (neteval-witness-fix witness))
         ;; (witness (neteval-witness-for-svex-compose-dfs
         ;;           (car x) assigns updates memo stack witness))
         ((mv ?first updates1 memo1)
          (svex-compose-dfs (car x) assigns updates memo stack))
         (witness1 (neteval-witness-for-svexlist-compose-dfs
                    (cdr x) assigns updates1 memo1 stack witness)))
      (neteval-witness-for-svex-compose-dfs
       (car x) assigns updates memo stack witness1)))
  ///

  ;; Want to show that we can transform a neteval of the computed updates into
  ;; a neteval of the assigns.  We can't assume we have all the updates
  ;; computed at a given point in the recursion, but we'll join the current
  ;; updates with the assigns to get our "complete" network.

  ;; Let's take 1 step: we start with a network
  ;; c = c(a,b,i)
  ;; b = b(a, i)
  ;; a = a(i)

  ;; and compose it 1 step to get
  ;; c = c(a, b(a, i), i)
  ;; b = b(a, i)
  ;; a = a(i).

  ;; Given a neteval-witness for the latter, we want to produce a
  ;; neteval-witness for the former so that the netevals they produce are the
  ;; same. Since C has been updated we need to do something new to all the
  ;; neteval-witness entries for C recursively to recreate the same neteval in
  ;; the original network.  Namely, for each neteval-witness entry binding c,
  ;; replace that binding for C with a new neteval-witness that adds a binding
  ;; for b based on the original neteval-witness. 


  ;; The latter neteval-witness has some neteval-witness


  ;; So, we assume we have a neteval-witness,
  ;; updates-witness, for the finished updates.  We need to produce a
  ;; neteval-witness, assigns-witness for the input assignments such that
  ;; (svex-envs-equivalent (neteval-witness->neteval updates-witness updates env)
  ;;                       (neteval-witness->neteval assigns-witness assigns env)).

  ;; Suppose we compute the composition for an expression X while some
  ;; variables are on the stack.  The result expression contains some such
  ;; variable Vs.  We store the result expression X1 in the memo table.  At the
  ;; moment that we store it, we think the result-witness we've accumulated satisfies:
  ;; (equal (svex-eval x (svex-network-join-envs
  ;;                      assigns
  ;;                      (neteval-witness->neteval (append assigns-witness updates-witness) assigns env)
  ;;                      env))
  ;;        (svex-eval x1 (svex-network-join-envs
  ;;                      (append updates assigns)
  ;;                      (neteval-witness->neteval updates-witness (append updates assigns) env)
  ;;                      env)))

  ;; Later, we pop Vs off the stack and add its update function to updates and
  ;; its witness to assigns-witness.  So is the above equation still valid with
  ;; this added binding?  First the LHS: Suppose vs is present in x.  Its
  ;; lookup in the envs goes to the neteval since it is an internal signal
  ;; (bound in assigns).  

  ;; The variable vs is assumed to be present in x1.  Its
  ;; lookup in the join-envs will 


  ;; (defun-sk svex-compose-dfs-memo-neteval-witness-correct (memo assigns witness env)
  ;;   (forall svex
  ;;           (let ((memo-val (svex-lookup svex memo)))
  ;;             (implies memo-val
  ;;                      (equal (svex-eval memo-val env)
  ;;                             (svex-eval svex 


  ;; (defun-sk svex-compose-dfs-memo-correct (memo neteval)
  ;;   (forall svex
  ;;           (let ((look (hons-assoc-equal svex (svex-svex-memo-fix memo))))
  ;;             (implies look
  ;;                      (equal (svex-eval (cdr look) neteval)
  ;;                             (svex-eval svex neteval)))))
  ;;   :rewrite :direct)

  ;; (in-theory (disable svex-compose-dfs-memo-correct))

  ;; (defcong svex-envs-equivalent equal
  ;;   (svex-compose-dfs-memo-correct memo neteval) 2
  ;;   :hints (("goal" :cases ((svex-compose-dfs-memo-correct memo neteval))
  ;;            :in-theory (e/d (svex-compose-dfs-memo-correct)
  ;;                            (svex-compose-dfs-memo-correct-necc))
  ;;            :use ((:instance svex-compose-dfs-memo-correct-necc
  ;;                   (neteval neteval-equiv)
  ;;                   (svex (svex-compose-dfs-memo-correct-witness memo neteval)))
  ;;                  (:instance svex-compose-dfs-memo-correct-necc
  ;;                   (neteval neteval)
  ;;                   (svex (svex-compose-dfs-memo-correct-witness memo neteval-equiv)))))))

  ;; (deffixcong svex-svex-memo-equiv equal
  ;;   (svex-compose-dfs-memo-correct memo neteval) memo
  ;;   :hints (("goal" :cases ((svex-compose-dfs-memo-correct memo neteval))
  ;;            :in-theory (e/d (svex-compose-dfs-memo-correct)
  ;;                            (svex-compose-dfs-memo-correct-necc))
  ;;            :use ((:instance svex-compose-dfs-memo-correct-necc
  ;;                   (memo (svex-svex-memo-fix memo))
  ;;                   (svex (svex-compose-dfs-memo-correct-witness memo neteval)))
  ;;                  (:instance svex-compose-dfs-memo-correct-necc
  ;;                   (memo memo)
  ;;                   (svex (svex-compose-dfs-memo-correct-witness (svex-svex-memo-fix memo) neteval)))))))

  (local (defthm alist-keys-of-cons
           (equal (alist-keys (cons (cons a b) c))
                  (cons a (alist-keys c)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append a b))
                  (or (svex-lookup k a)
                      (svex-lookup k b)))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))


  (defthm svex-compose-svex-alist-eval-equiv-congruence
    (implies (svex-alist-eval-equiv a b)
             (svex-eval-equiv (svex-compose x a) (svex-compose x b)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv)))
    :rule-classes :congruence)

  (defthm svex-compose*-svex-alist-eval-equiv-congruence
    (implies (svex-alist-eval-equiv a b)
             (svex-eval-equiv (svex-compose* x a) (svex-compose* x b)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv)))
    :rule-classes :congruence)

  (local (defthm svex-alist-eval-equiv-cons-cons
           (implies (svex-eval-equiv x y)
                    (svex-alist-eval-equiv (cons (cons var x) rest)
                                           (cons (cons var y) rest)))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))
           :rule-classes :congruence))

  (defthm svex-compose-to-svex-compose*
    (svex-eval-equiv (svex-compose x a)
                     (svex-compose* x a))
    :hints(("Goal" :in-theory (enable svex-eval-equiv))))

  (local (defthm svex-alist-reduce-of-svex-alist-keys
           (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys updates)
                                                     (append updates assigns))
                                  updates)
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

  (local (in-theory (disable neteval-witness-for-compose-step-correct)))

  (local
   (defthm neteval-witness-for-compose-step-correct-for-compose-dfs
     (b* ((witness (neteval-witness-for-compose-step var (svex-alist-keys updates) new-witness)))
       (implies (and (svex-lookup var assigns)
                     (not (svex-lookup var updates))
                     (svar-p var))
                (svex-envs-equivalent
                 (neteval-witness->neteval
                  new-witness
                  (cons (cons var (svex-compose*
                                   (svex-lookup var assigns)
                                   updates))
                        (append updates assigns))
                  env)
                 (neteval-witness->neteval
                  witness (append updates assigns) env))))
     :hints(("Goal" :use ((:instance neteval-witness-for-compose-step-correct
                           (composed-vars (svex-alist-keys updates))
                           (network (append updates assigns))))
             :in-theory (enable svex-network-compose-step)
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable svex-network-join-envs)))
            ))))


  (std::defret-mutual neteval-witness-for-svex-compose-dfs-correct
    (defret <fn>-correct
      (b* (((mv ?x1 updates1 ?memo1)
            (svex-compose-dfs x assigns updates memo stack))
           (neteval1 (neteval-witness->neteval new-witness
                                               (append updates assigns)
                                               env))
           (neteval2 (neteval-witness->neteval witness
                                               (append updates1 assigns)
                                               env)))
        (implies (And (svex-compose-dfs-memo-correct memo updates)
                      (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
                 (svex-envs-equivalent neteval1 neteval2)))
      :hints ('(:expand (<call>
                         (svex-compose-dfs x assigns updates memo stack))
                :in-theory (enable svex-acons)))
      :fn neteval-witness-for-svex-compose-dfs)

    (defret <fn>-correct
      (b* (((mv ?x1 updates1 ?memo1)
            (svexlist-compose-dfs x assigns updates memo stack))
           (neteval1 (neteval-witness->neteval new-witness
                                               (append updates assigns)
                                               env))
           (neteval2 (neteval-witness->neteval witness
                                               (append updates1 assigns)
                                               env)))
        (implies (And (svex-compose-dfs-memo-correct memo updates)
                      (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
                 (svex-envs-equivalent neteval1 neteval2)))
      :hints ('(:expand (<call>
                         (svexlist-compose-dfs x assigns updates memo stack))))
      :fn neteval-witness-for-svexlist-compose-dfs)))
    
