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

  (defcong svex-envs-similar svex-envs-similar
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

  (defcong svex-envs-similar equal (neteval-witness->neteval x network env) 3)

  (defthm neteval-witness->neteval-of-nil
    (equal (neteval-witness->neteval nil network env) nil))

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



(defcong svex-envs-equivalent equal (neteval-p neteval network env) 1
  :hints (("goal" :use ((:instance neteval-p-suff
                         (neteval neteval-equiv)
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness neteval-equiv network env)))))))


(defcong svex-envs-similar equal (neteval-p neteval network env) 3
  :hints (("goal" :use ((:instance neteval-p-suff
                         (env env-equiv)
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness neteval network env-equiv))))
           :cases ((neteval-p neteval network env)))))

(defcong svex-alist-eval-equiv equal (neteval-p neteval network env) 2
  :hints (("goal" :use ((:instance neteval-p-suff
                         (network network-equiv)
                         (neteval-witness (neteval-p-witness neteval network env)))
                        (:instance neteval-p-suff
                         (neteval-witness (neteval-p-witness neteval network-equiv env)))))))


(defthm neteval-p-of-nil
  (neteval-p nil network env)
  :hints(("Goal" :use ((:instance neteval-p-suff (neteval-witness nil) (neteval nil))))))
