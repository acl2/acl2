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
(include-book "rewrite-base")
(include-book "alist-equiv")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))


;; Theory for evaluation of not-necessarily-monotonic networks.

;; For networks of monotonic update functions, a least fixpoint is a sensible
;; spec for a complete network evaluation (neteval for short).  E.g., for
;; 4v-sexprs, which had strictly monotonic semantics, we had the half-lattice
;; relation x [ 1, x [ 0, x [ z, we said a complete neteval is a least
;; fixpoint: specifically, a valuation function v (a mapping from signals to
;; values) is a fixpoint if for any signal s, signal s with assignment function
;; f_s, v(s) = f_s(v).  It is a least fixpoint if for every fixpoint v', v [=
;; v' (pointwise).  Because of monotonicity we can show that there is always a
;; least fixpoint for every network of 4v-sexpr assignments.

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

;; We can't define a neteval directly because its definition involves a
;; recursion over an existential quantifier.  Instead we define a "neteval
;; ordering" as a specification for how signals are composed together, and
;; define a neteval as an assignment for which a neteval ordering exists.  In
;; fact, it turns out to be more practical to work with a definition of neteval
;; in terms of an intermediate relation we call a "netcomp" between sets of
;; assignments (svex-alists).  A svex-alist X is a netcomp of a svex-alist Y if
;; it can be derived (up to svex-alist-eval-equiv) from Y by composing signals
;; according to a neteval-ordering.  A valuation of signals is a neteval of a
;; network, then, iff it is an evaluation of a netcomp of that network under an
;; environment where all internal signals are bound to X.  One direction of
;; this iff (the more important one) is proved in neteval-p-of-netcomp-eval,
;; below; the other direction is pending.

;; It is much easier to reason about the netcomp relation than to reason about
;; netevals and neteval-orderings directly, especially once a few properties
;; are established.

;; Reflexivity -- (netcomp-p x x)
;; Transitivity -- (implies (and (netcomp-p x y) (netcomp-p y z)) (netcomp-p x z))
;; Union -- (implies (and (netcomp-p x z) (netcomp-p y z)) (netcomp-p (append x y) z))
;; Reduce -- (implies (netcomp-p x y) (netcomp-p (svex-alist-reduce keys x) y))
;; Compose -- (implies (and (netcomp-p x z) (netcomp-p y z)) (netcomp-p (svex-alist-compose x y) z))

;; With these properties we usually don't need to reason about the existence of
;; neteval-orderings anymore, just express our operations as combinations of
;; the above.
;; --------------------------------------------------------------------


;; A neteval ordering is a mapping from signals (svars) to neteval
;; orderings.  If a signal is not mapped, then its value is X.  A neteval
;; ordering produces a valuation (svex-env) given a network of assignments
;; (svex-alist) recursively.
(fty::defmap neteval-ordering :key-type svar :val-type neteval-ordering :true-listp t)

(fty::deffixcong neteval-ordering-equiv neteval-ordering-equiv (append x y) x)
(fty::deffixcong neteval-ordering-equiv neteval-ordering-equiv (append x y) y)


;; (define svex-network-join-envs ((network svex-alist-p) ;; assignments for internal signals
;;                                 (internal-env svex-env-p)
;;                                 (input-env svex-env-p))
;;   :returns (env svex-env-p)
;;   (append (svex-env-extract (svex-alist-keys network) internal-env)
;;           (svex-env-fix input-env))
;;   ///
;;   (defret boundp-of-<fn>
;;     (iff (svex-env-boundp var env)
;;          (or (svex-lookup var network)
;;              (svex-env-boundp var input-env))))

;;   (defret lookup-of-fn
;;     (equal (svex-env-lookup var env)
;;            (if (svex-lookup var network)
;;                (svex-env-lookup var internal-env)
;;              (svex-env-lookup var input-env))))

;;   (defcong svex-envs-equivalent svex-envs-similar
;;     (svex-network-join-envs network internal-env input-env) 2)

;;   (defcong svex-envs-equivalent svex-envs-equivalent
;;     (svex-network-join-envs network internal-env input-env) 3)

;;   (defcong svex-envs-similar svex-envs-similar
;;     (svex-network-join-envs network internal-env input-env) 3)

;;   (defcong svex-alist-eval-equiv svex-envs-equivalent
;;     (svex-network-join-envs network internal-env input-env) 1))



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

(define pair-keys ((keys true-listp) val)
  :returns (alist alistp)
  (if (atom keys)
      nil
    (cons (cons (car keys) val)
          (pair-keys (cdr keys) val)))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key alist)
           (and (member-equal key keys)
                (cons key val)))))



(define neteval-ordering-eval ((x neteval-ordering-p)
                               (network svex-alist-p)
                               (env svex-env-p))

  ;; Env must only bind primary input signals, not internal ones.
  :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                (svex-alist-keys network)))
  :verify-guards nil
  :measure (neteval-ordering-count x)
  :returns (neteval svex-env-p)
  (b* ((x (neteval-ordering-fix x))
       ((when (atom x))
        nil)
       ((cons signal ordering) (car x))
       (assign (svex-lookup signal network))
       ((unless assign)
        (neteval-ordering-eval (cdr x) network env)))
    (cons (cons signal
                (svex-eval assign
                           ;; (svex-network-join-envs network 
                           (append (neteval-ordering-eval ordering network env)
                                   env)))
          (neteval-ordering-eval (cdr x) network env)))
  ///
  (defret keys-subsetp-of-<fn>
    (subsetp-equal (alist-keys neteval) (svex-alist-keys network))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp key neteval)
         (and (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x))
              (svex-lookup key network)))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp)
                                   (hons-assoc-equal-of-neteval-ordering-fix)))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key neteval)
           (let* ((look (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x)))
                  (ordering (cdr look))
                  (assign (svex-lookup key network)))
             (if look
                 (svex-eval assign ;; (svex-network-join-envs network
                            (append (neteval-ordering-eval ordering network env)
                                    env))
               (4vec-x))))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup)
                                   (hons-assoc-equal-of-neteval-ordering-fix)))))


  (defcong svex-alist-eval-equiv equal (neteval-ordering-eval x network env) 2)

  (defcong svex-envs-similar equal (neteval-ordering-eval x network env) 3)

  (defthm neteval-ordering-eval-of-nil
    (equal (neteval-ordering-eval nil network env) nil))

  (verify-guards neteval-ordering-eval)

  (local (defthmd neteval-ordering-eval-of-append-lemma
           (implies (and (neteval-ordering-p ord1)
                         (neteval-ordering-p ord2))
                    (equal (neteval-ordering-eval (append ord1 ord2) network env)
                           (append (neteval-ordering-eval ord1 network env)
                                   (neteval-ordering-eval ord2 network env))))
           :hints(("Goal" :in-theory (enable neteval-ordering-fix append)))))
  

  (deffixequiv neteval-ordering-eval)


  (defthm neteval-ordering-eval-of-cons
    (equal (neteval-ordering-eval (cons (cons var ord1) ord2) network env)
           (let ((look (svex-lookup var network)))
             (if (and (svar-p var) look)
                 (cons (cons var (svex-eval look
                                            (append (neteval-ordering-eval ord1 network env) env)))
                       (neteval-ordering-eval ord2 network env))
               (neteval-ordering-eval ord2 network env))))
    :hints (("goal" :expand ((neteval-ordering-eval (cons (cons var ord1) ord2) network env)))))

  (defthm neteval-ordering-eval-of-append
    (equal (neteval-ordering-eval (append ord1 ord2) network env)
           (append (neteval-ordering-eval ord1 network env)
                   (neteval-ordering-eval ord2 network env)))
    :hints(("Goal" :use ((:instance neteval-ordering-eval-of-append-lemma
                          (ord1 (neteval-ordering-fix ord1))
                          (ord2 (neteval-ordering-fix ord2)))))))

  (defthm neteval-ordering-eval-of-pair-keys
    (implies (svarlist-p keys)
             (equal (neteval-ordering-eval (pair-keys keys val) network env)
                    (svex-alist-eval (svex-alist-reduce keys network)
                                     (append (neteval-ordering-eval val network env) env))))
    :hints(("Goal" :in-theory (enable pair-keys svex-env-reduce-redef)))))


(local (defthm svex-alist-eval-equiv-of-cons
         (implies (svex-eval-equiv val1 val2)
                  (svex-alist-eval-equiv (cons (cons key val1) rest)
                                         (cons (cons key val2) rest)))
         :hints (("goal" :in-theory (enable svex-alist-eval-equiv
                                            svex-lookup)))
         :rule-classes :congruence))


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

(local (defthm svex-lookup-of-cons
         (equal (svex-lookup k (cons pair rest))
                (if (and (consp pair)
                         (svar-p (car pair))
                         (equal (svar-fix k) (car pair)))
                    (svex-fix (cdr pair))
                  (svex-lookup k rest)))
         :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (cons x y) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


;; (define neteval-ordering->exprs ((x neteval-ordering-p)
;;                                  (network svex-alist-p))
;;   :verify-guards nil
;;   :measure (neteval-ordering-count x)
;;   :returns (compose svex-alist-p)
;;   (b* ((x (neteval-ordering-fix x))
;;        ((when (atom x))
;;         nil)
;;        ((cons signal ordering) (car x))
;;        (assign (svex-lookup signal network))
;;        ((unless assign)
;;         (neteval-ordering->exprs (cdr x) network)))
;;     (cons (cons signal
;;                 (svex-compose assign
;;                               (svex-alist-extract (svex-alist-keys network)
;;                                                   (neteval-ordering->exprs ordering network))))
;;           (neteval-ordering->exprs (cdr x) network)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval compose env)
;;            (neteval-ordering-eval x network env))
;;     :hints(("Goal" :in-theory (enable neteval-ordering-eval
;;                                       svex-alist-eval
;;                                       svex-network-join-envs))))

;;   (defcong svex-alist-eval-equiv svex-alist-eval-equiv (neteval-ordering->exprs x network) 2))


(local (in-theory (disable acl2::intersectp-equal-commute)))

(define neteval-ordering-compile ((x neteval-ordering-p)
                                 (network svex-alist-p))
  ;; :verify-guards nil
  :measure (neteval-ordering-count x)
  :returns (compose svex-alist-p)
  (b* ((x (neteval-ordering-fix x))
       ((when (atom x))
        nil)
       ((cons signal ordering) (car x))
       (assign (svex-lookup signal network))
       ((unless assign)
        (neteval-ordering-compile (cdr x) network)))
    (cons (cons signal
                (svex-compose assign
                              (neteval-ordering-compile ordering network)))
          (neteval-ordering-compile (cdr x) network)))
  ///
  
  ;; (local (defthm svex-env-boundp-when-svex-lookup-and-not-intersectp
  ;;          (implies (and (not (intersectp-equal (alist-keys (svex-env-fix x))
  ;;                                               (svex-alist-keys y)))
  ;;                        (svex-lookup k y))
  ;;                   (not (svex-env-boundp k x)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-boundp svex-alist-keys svex-env-fix alist-keys intersectp-equal)
  ;;                  :induct (svex-env-fix x)))))

  ;; (local (defthm svex-env-boundp-when-svex-lookup-and-subsetp
  ;;          (implies (and (subsetp-equal (alist-keys (svex-env-fix x))
  ;;                                       (svex-alist-keys y))
  ;;                        (not (svex-lookup k y)))
  ;;                   (not (svex-env-boundp k x)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-boundp svex-alist-keys svex-env-fix alist-keys intersectp-equal)
  ;;                  :induct (svex-env-fix x)))))

  ;; (local (defthm svex-env-lookup-when-not-boundp
  ;;          (implies (not (svex-env-boundp k x))
  ;;                   (equal (svex-env-lookup k x) (4vec-x)))
  ;;          :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))


  ;; (defthm svex-network-join-envs-when-env-not-intersectp
  ;;   (implies (and (not (intersectp-equal (alist-keys (svex-env-fix input-env))
  ;;                                        (svex-alist-keys network)))
  ;;                 (subsetp-equal (alist-keys (svex-env-fix internal-env))
  ;;                                (svex-alist-keys network)))
  ;;            (svex-envs-similar (svex-network-join-envs network internal-env input-env)
  ;;                               (append internal-env input-env)))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-similar svex-network-join-envs))))

  (defret eval-of-<fn>
    ;; (implies (not (intersectp-equal (alist-keys (svex-env-fix env))
    ;;                                 (svex-alist-keys network)))
             (equal (svex-alist-eval compose env)
                    (neteval-ordering-eval x network env))
    :hints(("Goal" :in-theory (enable neteval-ordering-eval
                                      svex-alist-eval))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (neteval-ordering-compile x network) 2)

  ;; (local (defthm svex-lookup-when-consp-svex-alist-fix
  ;;        (implies (consp (svex-alist-fix x))
  ;;                 (equal (svex-lookup k x)
  ;;                        (if (equal (svar-fix k) (caar (svex-alist-fix x)))
  ;;                            (cdar (svex-alist-fix x))
  ;;                          (svex-lookup k (cdr (svex-alist-fix x))))))
  ;;        :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

  ;; (local (defthm svex-lookup-when-not-consp-svex-alist-fix
  ;;          (implies (not (consp (svex-alist-fix x)))
  ;;                   (equal (svex-lookup k x) nil))
  ;;        :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key compose)
           (b* ((ord-look (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x)))
                (net-look (svex-lookup key network)))
             (and ord-look net-look
                  (svex-compose net-look (neteval-ordering-compile (cdr ord-look) network)))))
    :hints(("Goal" :in-theory (e/d () (hons-assoc-equal-of-neteval-ordering-fix)))))

  (deffixequiv neteval-ordering-compile)

  (defthm neteval-ordering-compile-of-cons
    (equal (neteval-ordering-compile (cons (cons var ord1) ord2) network)
           (let ((look (svex-lookup var network)))
             (if (and (svar-p var) look)
                 (cons (cons var (svex-compose look (neteval-ordering-compile ord1 network)))
                       (neteval-ordering-compile ord2 network))
               (neteval-ordering-compile ord2 network))))
    :hints (("goal" :expand ((neteval-ordering-compile (cons (cons var ord1) ord2) network)))))

  (defthm neteval-ordering-compile-of-append
    (equal (neteval-ordering-compile (append a b) network)
           (append (neteval-ordering-compile a network)
                   (neteval-ordering-compile b network)))
    :hints (("goal" :induct (neteval-ordering-compile a network)
             :expand ((neteval-ordering-compile a network)
                      (neteval-ordering-compile (append a b) network)))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (neteval-ordering-compile x network) 2
    :hints(("Goal" :in-theory (disable neteval-ordering-compile))
           `(:expand ,(car (last clause)))))

  (defthm neteval-ordering-compile-of-pair-keys
    (implies (svarlist-p keys)
             (equal (neteval-ordering-compile (pair-keys keys val) network)
                    (svex-alist-compose (svex-alist-reduce keys network)
                                        (neteval-ordering-compile val network))))
    :hints(("Goal" :in-theory (enable pair-keys svex-alist-compose svex-alist-reduce svex-acons)))))


(defthm svex-lookup-of-append
  (equal (svex-lookup k (append a b))
         (or (svex-lookup k a)
             (svex-lookup k b)))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

(defthmd svex-alist-eval-equiv-in-terms-of-envs-equivalent
  (equal (svex-alist-eval-equiv x y)
         (LET
          ((ENV (SVEX-ALIST-EVAL-EQUIV-ENVS-EQUIVALENT-WITNESS X Y)))
          (SVEX-ENVS-EQUIVALENT (SVEX-ALIST-EVAL X ENV)
                                (SVEX-ALIST-EVAL Y ENV))))
  :hints (("goal" :cases ((svex-alist-eval-equiv x y))
           :in-theory (enable SVEX-ENVS-EQUIVALENT-IMPLIES-ALIST-EVAL-EQUIV))))


(define neteval-ordering-compose-aux ((x neteval-ordering-p)
                                      (subst neteval-ordering-p))
  :measure (neteval-ordering-count x)
  :returns (composed neteval-ordering-p)
  (b* ((x (neteval-ordering-fix x))
       ((when (atom x)) nil)
       ((cons signal ordering) (car x))
       (new-ordering (neteval-ordering-compose-aux ordering subst))
       (rest (neteval-ordering-compose-aux (cdr x) subst)))
    (cons (cons signal (append new-ordering (neteval-ordering-fix subst)))
          rest))
  ///
  (defret eval-of-<fn>
    (equal (neteval-ordering-eval composed network env)
           (neteval-ordering-eval x network
                                  (append (neteval-ordering-eval subst network env)
                                          env)))
    :hints(("Goal" :in-theory (enable neteval-ordering-eval))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv
     (neteval-ordering-compile composed network)
     (svex-alist-compose (neteval-ordering-compile x network)
                         (neteval-ordering-compile subst network)))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent) (<fn>))
            :do-not-induct t))))

(define neteval-ordering-compose ((x neteval-ordering-p)
                                  (subst neteval-ordering-p))
  :measure (neteval-ordering-count x)
  :returns (composed neteval-ordering-p)
  (b* ((x (neteval-ordering-fix x))
       ((when (atom x)) nil)
       ((cons signal ordering) (car x))
       (new-ordering (neteval-ordering-compose ordering subst))
       (rest (neteval-ordering-compose (cdr x) subst))
       (subst-look (hons-assoc-equal signal (neteval-ordering-fix subst))))
    ;; Ugh.  Honestly, I just reverse-engineered what this expression had to be
    ;; to meet the spec (eval-of-<fn>, below).  Here's an attempt to explain
    ;; it.

    ;; We want to produce an ordering (compose) that reflects an ordering (x)
    ;; applied to the network resulting from applying an ordering (subst) to
    ;; the original network (network).

    ;; For each binding of a signal to an ordering in X, first, if the signal
    ;; isn't bound in subst then it won't be bound in the composed network so
    ;; we skip it.

    ;; Assuming it is bound, then we want its binding to reflect the
    ;; composition of signals from subst

    (if subst-look
        (cons (cons signal (append (neteval-ordering-compose-aux (cdr subst-look) new-ordering)
                                   new-ordering))
              rest)
      rest))
  ///
  (defret eval-of-<fn>
    (equal (neteval-ordering-eval composed network env)
           (neteval-ordering-eval x (neteval-ordering-compile subst network) env))
    :hints(("Goal" :in-theory (enable neteval-ordering-eval))))
  

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile composed network)
                           (neteval-ordering-compile x (neteval-ordering-compile subst network)))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (<fn>))))))


(define neteval-ordering-identity ((keys svarlist-p))
  :returns (ordering neteval-ordering-p)
  :prepwork ((local (defthm neteval-ordering-p-of-pairlis$-nil
                      (implies (svarlist-p keys)
                               (neteval-ordering-p (pairlis$ keys nil)))))
             (local (defthm hons-assoc-equal-of-pairlis$-repeat
                      (equal (hons-assoc-equal key (pairlis$ keys (repeat (len keys) elt)))
                             (and (member-equal key keys)
                                  (cons key elt)))
                      :hints(("Goal" :in-theory (enable repeat pairlis$)))))
             (local (defthm hons-assoc-equal-of-pairlis$-nil
                      (equal (hons-assoc-equal key (pairlis$ keys nil))
                             (and (member-equal key keys)
                                  (list key)))))
             (local (defthm svex-env-boundp-of-pairlis$
                      (implies (and (equal len (len keys))
                                    (svarlist-p keys))
                               (iff (svex-env-boundp key (pairlis$ keys (repeat len elt)))
                                    (member-equal (svar-fix key) keys)))
                      :hints(("Goal" :in-theory (enable svex-env-boundp)))))
             (local (defthm svex-env-lookup-of-pairlis$
                      (implies (and (equal len (len keys))
                                    (svarlist-p keys))
                               (equal (svex-env-lookup key (pairlis$ keys (repeat len elt)))
                                      (if (member-equal (svar-fix key) keys)
                                          (4vec-fix elt)
                                        (4vec-x))))
                      :hints(("Goal" :in-theory (enable svex-env-lookup))))))
  (pairlis$ (svarlist-fix keys) nil)
  ///
  (defret eval-of-<fn>
    (svex-envs-equivalent (neteval-ordering-eval ordering network env)
                          (svex-env-reduce keys (svex-alist-eval network env)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile ordering network)
                           (svex-alist-reduce keys network))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (<fn>))))))


(define neteval-ordering-reduce ((vars svarlist-p) (x neteval-ordering-p))
  :returns (new-ord)
  (if (atom vars)
      nil
    (let ((look (hons-assoc-equal (svar-fix (car vars))
                                  (neteval-ordering-fix x))))
      (if look
          (cons look (neteval-ordering-reduce (cdr vars) x))
        (neteval-ordering-reduce (cdr vars) x))))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key new-ord)
           (and (member-equal key (svarlist-fix vars))
                (hons-assoc-equal key (neteval-ordering-fix x)))))

  (defret eval-of-<fn>
    (equal (neteval-ordering-eval new-ord network env)
           (svex-env-reduce vars (neteval-ordering-eval x network env)))
    :hints(("Goal" :in-theory (enable svex-env-reduce-redef neteval-ordering-eval))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile new-ord network)
                           (svex-alist-reduce vars (neteval-ordering-compile x network)))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv)
                                   (neteval-ordering-reduce))))))

                 

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-reduce keys x) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(local (defthm svex-alist-eval-equiv-of-reduce-keys
         (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys x) x) x)
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-compose x subst) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-compose x subst) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(defsection netcomp-p
  (defun-sk netcomp-p (comp decomp)
    (exists ordering
            (svex-alist-eval-equiv comp (neteval-ordering-compile ordering decomp))))

  (in-theory (disable netcomp-p netcomp-p-suff))

  (deffixcong svex-alist-equiv equal (netcomp-p comp decomp) comp
    :hints (("goal" :cases ((netcomp-p comp decomp))
             :in-theory (enable netcomp-p)
             :use ((:instance netcomp-p-suff
                    (comp (svex-alist-fix comp))
                    (ordering (netcomp-p-witness comp decomp)))
                   (:instance netcomp-p-suff
                    (ordering (netcomp-p-witness (svex-alist-fix comp) decomp)))))))

  (deffixcong svex-alist-equiv equal (netcomp-p comp decomp) decomp
    :hints (("goal" :cases ((netcomp-p comp decomp))
             :in-theory (enable netcomp-p)
             :use ((:instance netcomp-p-suff
                    (decomp (svex-alist-fix decomp))
                    (ordering (netcomp-p-witness comp decomp)))
                   (:instance netcomp-p-suff
                    (ordering (netcomp-p-witness comp (svex-alist-fix decomp))))))))

  (defcong svex-alist-eval-equiv equal (netcomp-p comp decomp) 1
    :hints (("goal" :cases ((netcomp-p comp decomp))
             :in-theory (enable netcomp-p)
             :use ((:instance netcomp-p-suff
                    (comp comp-equiv)
                    (ordering (netcomp-p-witness comp decomp)))
                   (:instance netcomp-p-suff
                    (ordering (netcomp-p-witness comp-equiv decomp)))))))

  (defcong svex-alist-eval-equiv equal (netcomp-p comp decomp) 2
    :hints (("goal" :cases ((netcomp-p comp decomp))
             :in-theory (enable netcomp-p)
             :use ((:instance netcomp-p-suff
                    (decomp decomp-equiv)
                    (ordering (netcomp-p-witness comp decomp)))
                   (:instance netcomp-p-suff
                    (ordering (netcomp-p-witness comp decomp-equiv)))))))


  (defthm netcomp-p-of-append
    (implies (and (netcomp-p x network)
                  (netcomp-p y network))
             (netcomp-p (append x y) network))
    :hints (("goal" :expand ((netcomp-p x network)
                             (netcomp-p y network)
                             (SVEX-ALIST-EVAL-EQUIV
                              (APPEND X Y)
                              (APPEND (NETEVAL-ORDERING-COMPILE (NETCOMP-P-WITNESS X NETWORK)
                                                                NETWORK)
                                      (NETEVAL-ORDERING-COMPILE (NETCOMP-P-WITNESS Y NETWORK)
                                                                NETWORK))))
             :in-theory (disable svex-lookup-of-neteval-ordering-compile)
             :use ((:instance netcomp-p-suff
                    (comp (append x y)) (decomp network)
                    (ordering (append (netcomp-p-witness x network)
                                      (netcomp-p-witness y network))))))))

  (defthmd netcomp-p-transitive
    (implies (and (netcomp-p x y)
                  (netcomp-p y z))
             (netcomp-p x z))
    :hints (("goal" :expand ((netcomp-p x y)
                             (netcomp-p y z))
             :use ((:instance netcomp-p-suff
                    (comp x) (decomp z)
                    (ordering (neteval-ordering-compose (netcomp-p-witness x y)
                                                        (netcomp-p-witness y z))))))))

  (defthmd netcomp-p-transitive2
    (implies (and (netcomp-p y z)
                  (netcomp-p x y))
             (netcomp-p x z))
    :hints(("Goal" :in-theory (enable netcomp-p-transitive))))

  (defthm netcomp-p-reflexive
    (netcomp-p x x)
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp x) (decomp x)
                           (ordering (neteval-ordering-identity (svex-alist-keys x)))))
             :in-theory (enable svex-alist-eval-equiv))))

  (defthm netcomp-p-of-svex-alist-reduce
    (implies (netcomp-p x y)
             (netcomp-p (svex-alist-reduce keys x) y))
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp (svex-alist-reduce keys x))
                           (decomp y)
                           (ordering (neteval-ordering-reduce keys (netcomp-p-witness x y)))))
             :expand ((netcomp-p x y)))))

  (defthm netcomp-p-of-svex-alist-compose
    (implies (and (netcomp-p x network)
                  (netcomp-p subst network))
             (netcomp-p (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-p-witness x network)
                                      (netcomp-p-witness subst network)))))
             :expand ((netcomp-p x network)
                      (netcomp-p subst network))))))


(defcong svex-envs-similar svex-envs-similar (svex-env-removekeys keys env) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong set-equiv svex-envs-equivalent (svex-env-removekeys keys env) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(defsection neteval-p

  (defun-sk neteval-p (neteval network env)
    (exists neteval-ordering
            (svex-envs-equivalent neteval
                                  (neteval-ordering-eval neteval-ordering network
                                                         (svex-env-removekeys
                                                          (svex-alist-keys network) env)))))

  (in-theory (disable neteval-p neteval-p-suff))
  (local (in-theory (enable neteval-p)))


  (deffixcong svex-env-equiv equal (neteval-p neteval network env) neteval
    :hints (("goal" :use ((:instance neteval-p-suff
                           (neteval (svex-env-fix neteval))
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness (svex-env-fix neteval) network env)))))))


  (deffixcong svex-env-equiv equal (neteval-p neteval network env) env
    :hints (("goal" :use ((:instance neteval-p-suff
                           (env (svex-env-fix env))
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness neteval network  (svex-env-fix env))))))))

  (deffixcong svex-alist-equiv equal (neteval-p neteval network env) network
    :hints (("goal" :use ((:instance neteval-p-suff
                           (network (svex-alist-fix network))
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness neteval (svex-alist-fix network) env)))))))



  (defcong svex-envs-equivalent equal (neteval-p neteval network env) 1
    :hints (("goal" :use ((:instance neteval-p-suff
                           (neteval neteval-equiv)
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness neteval-equiv network env)))))))


  (defcong svex-envs-similar equal (neteval-p neteval network env) 3
    :hints (("goal" :use ((:instance neteval-p-suff
                           (env env-equiv)
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness neteval network env-equiv))))
             :cases ((neteval-p neteval network env)))))

  (defcong svex-alist-eval-equiv equal (neteval-p neteval network env) 2
    :hints (("goal" :use ((:instance neteval-p-suff
                           (network network-equiv)
                           (neteval-ordering (neteval-p-witness neteval network env)))
                          (:instance neteval-p-suff
                           (neteval-ordering (neteval-p-witness neteval network-equiv env)))))))


  (defthm neteval-p-of-nil
    (neteval-p nil network env)
    :hints(("Goal" :use ((:instance neteval-p-suff (neteval-ordering nil) (neteval nil)))))))





(defsection neteval-p-of-netcomp-eval
  (local (defthm svex-alist-eval-when-equiv-compile
           (implies (svex-alist-eval-equiv x (neteval-ordering-compile ordering network))
                    (svex-envs-equivalent (svex-alist-eval x env)
                                          (neteval-ordering-eval ordering network env)))))
  (defthm neteval-p-of-netcomp-eval
    (implies (netcomp-p updates network)
             (neteval-p (svex-alist-eval updates (svex-env-removekeys (svex-alist-keys network) env))
                        network env))
    :hints (("goal" :expand ((netcomp-p updates network))
             :use ((:instance neteval-p-suff
                    (neteval (svex-alist-eval updates (svex-env-removekeys (svex-alist-keys network) env)))
                    (neteval-ordering (netcomp-p-witness updates network))))))))


(defthm svex-env-removekeys-under-svex-envs-similar
  (svex-envs-similar (svex-env-removekeys vars x)
                     (append (svarlist-x-env vars) x))
  :hints(("Goal" :in-theory (enable svex-envs-similar))))




