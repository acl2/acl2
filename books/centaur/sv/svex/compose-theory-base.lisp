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
(include-book "rsh-concat")
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "arithmetic/top" :Dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))


;; Theory for evaluation of not-necessarily-monotonic networks.

;; For networks of monotonic update functions, a least fixpoint is a sensible
;; spec for a complete network evaluation (neteval for short).  E.g., for
;; 4v-sexprs, which had strictly monotonic semantics, we had the half-lattice
;; relation x [ 1, x [ 0, x [ z, we said a complete neteval is a least
;; fixpoint: specifically, a valuation function v (a mapping from signals to
;; values) is a fixpoint if for any signal s with assignment function
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

;; A valuation of signals is a neteval if for each signal, each bit of its
;; value either is X or is the value of the corresponding bit of the signal's
;; assignment function applied to an(other) neteval of the signals.

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


;; A neteval ordering is a mapping from signals (svars) to
;; neteval-sigorderings, which are sequences in which all elements except the
;; last are a width and a neteval ordering, and the last is only a neteval
;; ordering.
(fty::deftypes neteval-ordering
  (fty::defmap neteval-ordering :key-type svar :val-type neteval-sigordering :true-listp t
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::deftagsum neteval-sigordering
    (:segment ((width posp :rule-classes :type-prescription)
               (ord neteval-ordering-or-null-p)
               (rest neteval-sigordering-p)))
    (:remainder ((ord neteval-ordering-or-null-p)))
    :measure (two-nats-measure (acl2-count x) 1)
    :base-case-override :remainder)
  (fty::deftagsum neteval-ordering-or-null
    (:null ())
    (:ordering ((ord neteval-ordering-p)))
    :measure (two-nats-measure (acl2-count x) 0)
    :base-case-override :null))

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

(local
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

   (defcong svex-eval-equiv svex-pair-eval-equiv (cons key val) 2)))

(define svex-alist-compextract ((keys svarlist-p)
                            (alist svex-alist-p))
  :returns (sub-alist svex-alist-p)
  (if (atom keys)
      nil
    (let ((look (svex-compose-lookup (car keys) alist)))
      (cons (cons (svar-fix (car keys)) look)
            (svex-alist-compextract (cdr keys) alist))))
  ///

  (defret svex-alist-eval-of-svex-alist-compextract
    (equal (svex-alist-eval sub-alist env)
           (svex-env-extract keys (append (svex-alist-eval alist env)
                                          env)))
    :hints(("Goal" :in-theory (enable svex-env-extract
                                      svex-compose-lookup)
            :induct t
            :expand ((svex-alist-eval nil env)
                     (:free (var) (svex-eval (svex-var var) env))
                     (:free (a b) (svex-alist-eval (cons a b) env))))))

  (defret lookup-in-svex-alist-compextract
    (equal (svex-lookup v sub-alist)
           (and (member (svar-fix v) (svarlist-fix keys))
                (svex-compose-lookup v alist)))
    :hints(("Goal"
            :in-theory
            (e/d (svex-lookup hons-assoc-equal svarlist-fix)
                 (hons-assoc-equal-of-svex-alist-fix)))))

  (defret compose-lookup-in-svex-alist-compextract
    (equal (svex-compose-lookup v sub-alist)
           (if (member (svar-fix v) (svarlist-fix keys))
               (svex-compose-lookup v alist)
             (svex-var v)))
    :hints(("Goal"
            :in-theory
            (e/d (svex-compose-lookup hons-assoc-equal svarlist-fix)
                 (hons-assoc-equal-of-svex-alist-fix)))))

  (defcong svex-alist-compose-equiv svex-alist-eval-equiv (svex-alist-compextract keys alist) 2))


(local (Defthm svex-compose-lookup-when-svex-lookup
         (implies (svex-lookup v x)
                  (equal (svex-compose-lookup v x)
                         (svex-lookup v x)))
         :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

(local (Defthm svex-compose-lookup-when-not-svex-lookup
         (implies (not (svex-lookup v x))
                  (equal (svex-compose-lookup v x)
                         (svex-var v)))
         :hints(("Goal" :in-theory (enable svex-compose-lookup)))))


;; Evaluate a neteval ordering with respect to a network of assignments.
;; Properly speaking, the environment here should not bind internal variables
;; (keys) of the network.  But we do look up internal variables in the env when
;; we come to an end point in the ordering, because we want to allow
;; composition with identity mappings.
(defines neteval-ordering-eval
  (define neteval-ordering-eval ((x neteval-ordering-p)
                                 (network svex-alist-p)
                                 (env svex-env-p))

    ;; ;; Env must only bind primary input signals, not internal ones.
    ;; :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
    ;;                               (svex-alist-keys network)))
    :verify-guards nil
    :measure (neteval-ordering-count x)
    :returns (neteval svex-env-p)
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x))
          nil)
         ((cons signal sigordering) (car x))
         ;; (function (svex-lookup signal network))
         ;; ((unless function)
         ;;  ;; ????  Do we want to bind signal to its env lookup here?  I think
         ;;  ;; no: if this is the "original" network then we don't want to add
         ;;  ;; signals that aren't bound, and if not, it can't hurt to not bind a
         ;;  ;; signal that's already unbound.
         ;;  ;; (cons (cons signal (svex-env-lookup signal env))
         ;;  (neteval-ordering-eval (cdr x) network env))

         ;; New approach: we use svex-compose-lookup everywhere, i.e. if the
         ;; signal is not bound in network it's as though it's bound to
         ;; (svex-var signal).
         )
      (cons (cons signal
                  (neteval-sigordering-eval sigordering
                                            signal 0 network env)
                  ;; (svex-eval assign
                  ;;            ;; (svex-network-join-envs network 
                  ;;            (append (neteval-ordering-eval ordering network env)
                  ;;                    env))
                  )
            (neteval-ordering-eval (cdr x) network env))))
  (define neteval-sigordering-eval ((x neteval-sigordering-p)
                                    (signal svar-p)
                                    (offset natp)
                                    (network svex-alist-p)
                                    (env svex-env-p))
    ;; :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
    ;;                               (svex-alist-keys network)))
    ;; :guard (svex-lookup signal network)
    :measure (neteval-sigordering-count x)
    :returns (val 4vec-p)
    (neteval-sigordering-case x
      ;; Bunch of possible ways to code this:
      ;;  - take the offset as an additional parameter (no; extra parameter
      ;;    seems like it would complicate things)
      ;;  - rightshift the result of the recursion (no, this doesn't work, confusingly)
      ;;  - modify the function when we recur on it
      :segment (4vec-concat (2vec x.width)
                            (4vec-rsh (2vec (lnfix offset))
                                      (neteval-ordering-or-null-eval
                                       x.ord signal network env))
                            ;; (svex-eval function
                            ;;            (append (neteval-ordering-eval x.ord network env)
                            ;;                    env))
                            (neteval-sigordering-eval x.rest signal (+ x.width (lnfix offset)) network env))
      :remainder (4vec-rsh (2vec (lnfix offset))
                           (neteval-ordering-or-null-eval x.ord signal network env))
      ;; (svex-eval function (append (neteval-ordering-eval x.ord network env)
      ;;                                          env))
      ))
  (define neteval-ordering-or-null-eval ((x neteval-ordering-or-null-p)
                                         (signal svar-p)
                                         (network svex-alist-p)
                                         (env svex-env-p))
    ;; :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
    ;;                               (svex-alist-keys network)))
    ;; :guard (svex-lookup signal network)
    :measure (neteval-ordering-or-null-count x)
    :returns (val 4vec-p)
    (neteval-ordering-or-null-case x
      :null (svex-env-lookup signal env)
      :ordering (svex-eval (svex-compose-lookup signal network)
                           (append (neteval-ordering-eval
                                    x.ord network env)
                                   env))))
    
  ///
  (defun neteval-ordering-selfinduct (x)
    (declare (xargs :measure (len (neteval-ordering-fix x))))
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x)) nil))
      (neteval-ordering-selfinduct (cdr x))))

  (defun neteval-sigordering-ind (x)
    (Declare (Xargs :measure (neteval-sigordering-count x)))
    (neteval-sigordering-case x
      :segment (neteval-sigordering-ind x.rest)
      :remainder nil))


  (local (defthm neteval-ordering-eval-induction
           t
           :rule-classes ((:induction :pattern (neteval-ordering-eval x network env)
                           :scheme (neteval-ordering-selfinduct x)))))


  (defcong svex-eval-equiv svex-eval-equiv (svex-rsh n x) 2
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  ;; (defret keys-subsetp-of-<fn>
  ;;   (subsetp-equal (alist-keys neteval) (svex-alist-keys network))
  ;;   :hints(("goal" :in-theory (enable alist-keys)
  ;;           :induct t
  ;;           :expand (<call>)))
  ;;   :fn neteval-ordering-eval)

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp key neteval)
         (and (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x))
              ;; (svex-lookup key network)
              ))
    :hints(("goal" :in-theory (e/d (svex-env-boundp)
                             (hons-assoc-equal-of-neteval-ordering-fix))
            :induct t
             :expand (<call>)))
    :fn neteval-ordering-eval)

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key neteval)
           (let* ((look (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x)))
                  (sigordering (cdr look))
                  ;; (function (svex-lookup key network))
                  )
             (if look ;; (and look function)
                 (neteval-sigordering-eval sigordering (svar-fix key) 0 network env)
               (4vec-x))))
    :hints(("goal" :in-theory (e/d (svex-env-lookup)
                             (hons-assoc-equal-of-neteval-ordering-fix))
            :induct t
            :expand (<call>)))
    :fn neteval-ordering-eval)
      ;; hard to predict which of the two will produce better induction scheme
      ;; but for now will go with rightshifting the result since it seems simpler.

  ;; (defcong svex-eval-equiv equal (neteval-ordering-or-null-eval x function network env) 2
  ;;   :hints(("Goal" :expand ((:free (function)
  ;;                            (neteval-ordering-or-null-eval x function network env))))))

  ;; (local (defun-sk neteval-sigordering-eval-svex-eval-cond (x network env)
  ;;          (forall (function function-equiv)
  ;;                  (implies (and (svex-eval-equiv function-equiv (double-rewrite function))
  ;;                                (syntaxp (not (equal function-equiv function))))
  ;;                           (equal (neteval-sigordering-eval x function network env)
  ;;                                  (neteval-sigordering-eval x function-equiv network env))))
  ;;          :rewrite :direct))

  ;; (local (in-theory (disable neteval-sigordering-eval-svex-eval-cond)))

  ;; (local (defthmd neteval-ordering-eval-svex-eval-thm
  ;;          (neteval-sigordering-eval-svex-eval-cond x network env)
  ;;          :hints (("goal" :induct (neteval-sigordering-ind x))
  ;;                  (and stable-under-simplificationp
  ;;                       `(:expand (,(car (last clause))
  ;;                                  (:free (function) (neteval-sigordering-eval x function network env))))))))


  ;; (defcong svex-eval-equiv equal (neteval-sigordering-eval x function network env) 2
  ;;   :hints (("goal" :use (neteval-ordering-eval-svex-eval-thm
  ;;                         neteval-sigordering-eval-svex-eval-cond-necc)
  ;;            :in-theory (disable neteval-sigordering-eval-svex-eval-cond-necc))))


  ;; (defthm-neteval-ordering-eval
  ;;   (defthm svex-eval-equiv-implies-equal-neteval-sigordering-eval-2
  ;;     (implies (svex-eval-equiv function function-equiv)(neteval-sigordering-eval x function network env) 2
  ;;   :hints (("goal" :induct (neteval-sigordering-ind x)
  ;;            :expand ((:free (function) (neteval-sigordering-eval x function network env))))))
  
  ;; (local
  ;;  (defun-sk svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond
  ;;    (x function network network-equiv env)
  ;;    (forall function-equiv
  ;;            (implies (double-rewrite (svex-eval-equiv function-equiv function))
  ;;                     (equal (neteval-sigordering-eval x function-equiv network-equiv env)
  ;;                            (neteval-sigordering-eval x function network env))))
  ;;    :rewrite :direct))

  ;; (local (in-theory (disable svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond)))

  ;; (local (DEFTHM
  ;;          SVEX-ALIST-EVAL-EQUIV-IMPLIES-SVEX-EVAL-EQUIV-SVEX-LOOKUP-2-rw
  ;;          (IMPLIES (SVEX-ALIST-EVAL-EQUIV ALIST ALIST-EQUIV)
  ;;                   (equal (SVEX-EVAL-EQUIV (SVEX-LOOKUP VAR ALIST)
  ;;                                           (SVEX-LOOKUP VAR ALIST-EQUIV))
  ;;                          t))))

  (defthm-neteval-ordering-eval-flag
    (defthm svex-alist-compose-equiv-implies-equal-neteval-ordering-eval-2
      (implies (svex-alist-compose-equiv network network-equiv)
               (equal (neteval-ordering-eval x network env)
                      (neteval-ordering-eval x network-equiv env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-eval
      :rule-classes :congruence)

    (defthm svex-alist-compose-equiv-implies-equal-neteval-sigordering-eval-4
      (implies (svex-alist-compose-equiv network network-equiv)
               ;; (svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond
               ;;  x function network network-equiv env)
               (equal (neteval-sigordering-eval x signal offset network env)
                      (neteval-sigordering-eval x signal offset network-equiv env))
               )
      :hints ('(:expand (;; (svex-alist-compose-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond
                         ;;  x function network network-equiv env)
                         (:free (network signal offset) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-eval
      :rule-classes :congruence)

    (defthm svex-alist-compose-equiv-implies-equal-neteval-ordering-or-null-eval-3
      (implies (svex-alist-compose-equiv network network-equiv)
               ;; (svex-alist-eval-equiv-implies-equal-neteval-ordering-or-null-eval-2-when-functions-equiv-cond
               ;;  x function network network-equiv env)
               (equal (neteval-ordering-or-null-eval x signal network env)
                      (neteval-ordering-or-null-eval x signal network-equiv env))
               )
      :hints ('(:expand (;; (svex-alist-eval-equiv-implies-equal-neteval-ordering-or-null-eval-2-when-functions-equiv-cond
                         ;;  x function network network-equiv env)
                         (:free (network signal offset) (neteval-ordering-or-null-eval x signal network env)))))
      :flag neteval-ordering-or-null-eval
      :rule-classes :congruence))

  ;; (defcong svex-alist-eval-equiv equal (neteval-ordering-eval x network env) 2)

  (defthm-neteval-ordering-eval-flag
    (DEFTHM SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-NETEVAL-ORDERING-EVAL-3
      (IMPLIES (SVEX-ENVS-SIMILAR ENV ENV-EQUIV)
               (EQUAL (NETEVAL-ORDERING-EVAL X NETWORK ENV)
                      (NETEVAL-ORDERING-EVAL X NETWORK ENV-EQUIV)))
      :flag neteval-ordering-eval
      :hints ('(:expand ((:free (env) (NETEVAL-ORDERING-EVAL X NETWORK ENV)))))
      :RULE-CLASSES (:CONGRUENCE))
    (DEFTHM SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-NETEVAL-sigORDERING-EVAL-5
      (IMPLIES (SVEX-ENVS-SIMILAR ENV ENV-EQUIV)
               (EQUAL (NETEVAL-sigORDERING-EVAL X signal offset NETWORK ENV)
                      (NETEVAL-sigORDERING-EVAL X signal offset NETWORK ENV-EQUIV)))
      :hints ('(:expand ((:free (env) (NETEVAL-sigORDERING-EVAL X signal offset NETWORK ENV)))))
      :flag neteval-sigordering-eval
      :RULE-CLASSES (:CONGRUENCE))
    (DEFTHM SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-NETEVAL-ordering-or-null-EVAL-5
      (IMPLIES (SVEX-ENVS-SIMILAR ENV ENV-EQUIV)
               (EQUAL (NETEVAL-ordering-or-null-EVAL X signal NETWORK ENV)
                      (NETEVAL-ordering-or-null-EVAL X signal NETWORK ENV-EQUIV)))
      :hints ('(:expand ((:free (env) (NETEVAL-ordering-or-null-EVAL X signal NETWORK ENV)))))
      :flag neteval-ordering-or-null-eval
      :RULE-CLASSES (:CONGRUENCE)))

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
    

    (deffixequiv-mutual neteval-ordering-eval)


    (defthm neteval-ordering-eval-of-cons
      (equal (neteval-ordering-eval (cons (cons var ord1) ord2) network env)
             (if (svar-p var)
                 (cons (cons var
                             (neteval-sigordering-eval ord1 var 0 network env))
                       (neteval-ordering-eval ord2 network env))
               (neteval-ordering-eval ord2 network env)))
      :hints (("goal" :expand ((neteval-ordering-eval (cons (cons var ord1) ord2) network env)))))

    (defthm neteval-ordering-eval-of-append
      (equal (neteval-ordering-eval (append ord1 ord2) network env)
             (append (neteval-ordering-eval ord1 network env)
                     (neteval-ordering-eval ord2 network env)))
      :hints(("Goal" :use ((:instance neteval-ordering-eval-of-append-lemma
                            (ord1 (neteval-ordering-fix ord1))
                            (ord2 (neteval-ordering-fix ord2)))))))

    (local (Defthm svex-env-extract-nil
             (equal (svex-env-extract nil x) nil)
             :hints(("Goal" :in-theory (enable svex-env-extract)))))

    (defthm neteval-ordering-eval-of-pair-remainders
      (implies (and (svarlist-p keys)
                    (neteval-sigordering-case val
                      :remainder (neteval-ordering-or-null-case val.ord :ordering)
                      :otherwise nil))
               (equal (neteval-ordering-eval (pair-keys keys val) network env)
                      (svex-alist-eval (svex-alist-compextract keys network)
                                       (append (neteval-ordering-eval
                                                (neteval-ordering-or-null-ordering->ord
                                                 (neteval-sigordering-remainder->ord val))
                                                network env)
                                               env))))
      :hints(("Goal" :in-theory (enable pair-keys svex-env-reduce-redef
                                        svex-alist-eval svex-env-extract
                                        svex-compose-lookup)
              :induct t
              :expand ((:free (signal offset) (neteval-sigordering-eval val signal offset network env))
                       (:free (val signal offset) (neteval-ordering-or-null-eval val signal network env))
                       (:free (var env) (svex-eval (svex-var var) env))))))

    (local (defthm 4vec-concat-identity
             (implies (and (equal y (4vec-rsh width x))
                           (2vec-p width)
                           (natp (2vec->val width)))
                      (equal (4vec-concat width x y)
                             (4vec-fix x)))
             :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-concat 4vec-shift-core)))))


    (defun-sk lookup-signal-not-in-network-cond (x network neteval env)
      (forall signal
              (implies (not (svex-lookup signal network))
                       (equal (svex-env-lookup signal neteval)
                              (if (hons-assoc-equal (svar-fix signal) (neteval-ordering-fix x))
                                  (svex-env-lookup signal env)
                                (4vec-x)))))
      :rewrite :direct)

    (in-theory (disable lookup-signal-not-in-network-cond
                        lookup-signal-not-in-network-cond-necc))
    (local (in-theory (enable lookup-signal-not-in-network-cond-necc)))


    (local (defthm svex-env-lookup-of-cons
             (Equal (svex-env-lookup k (cons (cons key val) a))
                    (if (equal (svar-fix k) key)
                        (4vec-fix val)
                      (svex-env-lookup k a)))
             :hints(("Goal" :in-theory (enable svex-env-lookup)))))

    (std::defret-mutual lookup-signal-not-in-network-of-<fn>-lemma
      (defretd lookup-signal-not-in-network-of-<fn>-lemma
        (lookup-signal-not-in-network-cond x network neteval env)
        :hints ((and stable-under-simplificationp
                     `(:computed-hint-replacement
                       ((let ((sig (acl2::find-call-lst 'lookup-signal-not-in-network-cond-witness clause)))
                          `(:clause-processor (acl2::generalize-with-alist-cp clause '((,sig . sig))))))
                       :expand (,(car (last clause)))
                       :in-theory (disable hons-assoc-equal-of-neteval-ordering-fix)))
                (and stable-under-simplificationp '(:expand (<call>))))
        :fn neteval-ordering-eval)
      (defretd <fn>-when-signal-not-in-network
        (implies (not (svex-lookup signal network))
                 (equal val (4vec-rsh (2vec (nfix offset)) (svex-env-lookup signal env))))
        :hints ('(:expand (<call>)))
        :fn neteval-sigordering-eval)
      (defretd <fn>-when-signal-not-in-network
        (implies (not (svex-lookup signal network))
                 (equal val (svex-env-lookup signal env)))
        :hints ('(:expand (<call>
                           (:free (env) (svex-eval (svex-var signal) env)))
                  :in-theory (disable SVEX-ENV-LOOKUP-OF-NETEVAL-ORDERING-EVAL)))
        :fn neteval-ordering-or-null-eval))

    (defretd lookup-signal-not-in-network-of-<fn>
      (implies (not (svex-lookup signal network))
               (equal (svex-env-lookup signal neteval)
                      (if (hons-assoc-equal (svar-fix signal) (neteval-ordering-fix x))
                          (svex-env-lookup signal env)
                        (4vec-x))))
      :hints (("goal" :use lookup-signal-not-in-network-of-<fn>-lemma
               :in-theory (disable <fn>)))
      :fn neteval-ordering-eval))


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


(defthmd svex-alist-eval-equiv-in-terms-of-envs-equivalent
  (equal (svex-alist-eval-equiv x y)
         (LET
          ((ENV (SVEX-ALIST-EVAL-EQUIV-ENVS-EQUIVALENT-WITNESS X Y)))
          (SVEX-ENVS-EQUIVALENT (SVEX-ALIST-EVAL X ENV)
                                (SVEX-ALIST-EVAL Y ENV))))
  :hints (("goal" :cases ((svex-alist-eval-equiv x y))
           :in-theory (enable SVEX-ENVS-EQUIVALENT-IMPLIES-ALIST-EVAL-EQUIV))))

(defines neteval-ordering-compile
  :flag-local nil
  (define neteval-ordering-compile ((x neteval-ordering-p)
                                    (network svex-alist-p))
    :verify-guards nil
    :measure (neteval-ordering-count x)
    :returns (compose svex-alist-p)
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x))
          nil)
         ((cons signal ordering) (car x))
         ;; (assign (svex-lookup signal network))
         ;; ((unless assign)
         ;;  ;;; ??? Assign signal to self?
         ;;  ;; (cons (cons signal (svex-var signal))
         ;;  (neteval-ordering-compile (cdr x) network))
         )
      (cons (cons signal
                  (neteval-sigordering-compile ordering signal 0 network))
            ;; (svex-compose assign
            ;;               (neteval-ordering-compile ordering network)))
            (neteval-ordering-compile (cdr x) network))))
  (define neteval-sigordering-compile ((x neteval-sigordering-p)
                                       (signal svar-p)
                                       (offset natp)
                                       (network svex-alist-p))
    :measure (neteval-sigordering-count x)
    :returns (compose svex-p)
    ;; :guard (svex-lookup signal network)
    (neteval-sigordering-case x
      :segment (svex-concat x.width
                            (svex-rsh offset (neteval-ordering-or-null-compile x.ord signal network))
                            (neteval-sigordering-compile x.rest signal (+ x.width (lnfix offset)) network))
      :remainder (svex-rsh offset (neteval-ordering-or-null-compile x.ord signal network))
      ;;(svex-compose function (neteval-ordering-compile x.ord network))
      ))
  (define neteval-ordering-or-null-compile ((x neteval-ordering-or-null-p)
                                            (signal svar-p)
                                            (network svex-alist-p))
    :measure (neteval-ordering-or-null-count x)
    :returns (compose svex-p)
    ;; :guard (svex-lookup signal network)
    (neteval-ordering-or-null-case x
      :null (svex-var signal)
      :ordering (svex-compose
                 (svex-compose-lookup signal network)
                 (neteval-ordering-compile x.ord network))))
                                            
  ///

  (local (defthm neteval-ordering-compile-induction
           t
           :rule-classes ((:induction :pattern (neteval-ordering-compile x network)
                           :scheme (neteval-ordering-selfinduct x)))))
  (local (defthm svex-env-boundp-when-svex-lookup-and-not-intersectp
           (implies (and (not (intersectp-equal (alist-keys (svex-env-fix x))
                                                (svex-alist-keys y)))
                         (svex-lookup k y))
                    (not (svex-env-boundp k x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-alist-keys svex-env-fix alist-keys intersectp-equal)
                   :induct (svex-env-fix x)))))

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

  (local (defthm svex-rsh-0
           (svex-eval-equiv (svex-rsh 0 x) x)
           :hints(("Goal" :in-theory (enable svex-eval-equiv
                                             svex-apply)))))

  (local (defthmd svex-env-lookup-when-not-boundp
           (implies (not (svex-env-boundp var x))
                    (equal (svex-env-lookup var x) (4vec-x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

  (local (defthm svex-eval-svex-var-when-lookup-and-not-intersectp
           (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env))
                                                (svex-alist-keys network)))
                         (svex-lookup signal network))
                    (equal (svex-eval (svex-var signal) env)
                           (4vec-x)))
           :hints (("goal" :Expand ((svex-eval (svex-var signal) env))
                    :in-theory (enable svex-env-lookup-when-not-boundp)))))

  (local (defthm 4vec-rsh-of-x
           (implies (and (2vec-p k)
                         (<= 0 (2vec->val k)))
                    (equal (4vec-rsh k (4vec-x)) (4vec-x)))
           :hints(("Goal" :in-theory (e/d (4vec-rsh 4vec-shift-core))))))

  (local (defthm svex-rsh-of-svex-rsh
           (svex-eval-equiv (svex-rsh n (svex-rsh m x))
                            (svex-rsh (+ (nfix n) (nfix m)) x))
           :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))


  (std::defret-mutual eval-of-<fn>
    (defret eval-of-<fn>
      ;; (implies (not (intersectp-equal (alist-keys (svex-env-fix env))
      ;;                                 (svex-alist-keys network)))
      (equal (svex-alist-eval compose env)
             (neteval-ordering-eval x network env))
      :fn neteval-ordering-compile
      :hints('(:in-theory (enable neteval-ordering-eval
                                  svex-alist-eval)
               :expand (<call>
                        (neteval-ordering-eval x network env)
                        (:free (var env) (svex-eval (svex-var var) env))))))
    (defret eval-of-<fn>
      ;; (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env))
      ;;                                      (svex-alist-keys network)))
      ;;               (svex-lookup signal network))
               (equal (svex-eval compose env)
                      (neteval-sigordering-eval
                       x signal offset
                       network env))
      :fn neteval-sigordering-compile
      :hints('(:in-theory (enable svex-alist-eval svex-apply)
               :expand (<call>
                        (:free (signal offset)
                         (neteval-sigordering-eval x signal offset network env))))))
    (defret eval-of-<fn>
      ;; (implies (and (not (intersectp-equal (alist-keys (svex-env-fix env))
      ;;                                      (svex-alist-keys network)))
      ;;               (svex-lookup signal network))
               (equal (svex-eval compose env)
                      (neteval-ordering-or-null-eval
                       x signal
                       network env))
      :fn neteval-ordering-or-null-compile
      :hints('(:in-theory (enable svex-alist-eval svex-apply)
               :expand (<call>
                        (:free (signal offset)
                         (neteval-ordering-or-null-eval
                          x signal network env))
                        (:free (var env) (svex-eval (svex-var var) env)))))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (neteval-ordering-compile x network) 2
    :hints (("goal" :use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                           (x (neteval-ordering-compile x network))
                           (y (neteval-ordering-compile x network-equiv)))))))

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
                ;; (net-look (svex-lookup key network))
                )
             (and ord-look ;; net-look
                  (neteval-sigordering-compile (cdr ord-look) (svar-fix key) 0 network))))
    :hints(("Goal" :in-theory (e/d () (hons-assoc-equal-of-neteval-ordering-fix))
            :induct t :expand (<call>)))
    :fn neteval-ordering-compile)



  (deffixequiv-mutual neteval-ordering-compile)

  (defret neteval-ordering-compile-when-atom-fix
    (implies (not (consp (neteval-ordering-fix x)))
             (equal compose nil))
    :hints (("goal" :expand (<call>)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))
    :fn neteval-ordering-compile)

  (defthm neteval-ordering-compile-of-append
    (equal (neteval-ordering-compile (append a b) network)
           (append (neteval-ordering-compile a network)
                   (neteval-ordering-compile b network)))
    :hints (("goal" :induct t
             :expand ((neteval-ordering-compile a network)
                      (neteval-ordering-compile (append a b) network)))
            (and stable-under-simplificationp
                 '(:expand ((neteval-ordering-compile b network))))))

  (defthm neteval-ordering-compile-of-cons
    (equal (neteval-ordering-compile (cons (cons var ord1) ord2) network)
           (if (and (svar-p var)) ;; look)
               (cons (cons var
                           (neteval-sigordering-compile ord1 var 0 network))
                     (neteval-ordering-compile ord2 network))
             (neteval-ordering-compile ord2 network)))
    :hints (("goal" :expand ((neteval-ordering-compile (cons (cons var ord1) ord2) network)))
            (and stable-under-simplificationp
                 '(:expand ((neteval-ordering-compile ord2 network))))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (neteval-ordering-compile x network) 2
    :hints(("Goal" :in-theory (disable neteval-ordering-compile))
           `(:expand ,(car (last clause)))))

  (defthm neteval-ordering-compile-of-pair-remainders
      (implies (and (svarlist-p keys)
                    (neteval-sigordering-case val
                      :remainder (neteval-ordering-or-null-case val.ord :ordering)
                      :otherwise nil))
               (svex-alist-eval-equiv
                (neteval-ordering-compile (pair-keys keys val) network)
                (svex-alist-compose (svex-alist-compextract keys network)
                                    (neteval-ordering-compile
                                     (neteval-ordering-or-null-ordering->ord
                                      (neteval-sigordering-remainder->ord val))
                                     network))))
      :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv))))

  ;; (defthm neteval-ordering-compile-of-pair-keys
  ;;   (implies (svarlist-p keys)
  ;;            (equal (neteval-ordering-compile (pair-keys keys val) network)
  ;;                   (svex-alist-compose (svex-alist-reduce keys network)
  ;;                                       (neteval-ordering-compile val network))))
  ;;   :hints(("Goal" :in-theory (enable pair-keys svex-alist-compose svex-alist-reduce svex-acons))))
  (verify-guards neteval-ordering-compile)


  (defret eval-lookup-of-neteval-ordering-compile
    (equal (svex-eval (svex-lookup key compose) env)
           (svex-env-lookup key (neteval-ordering-eval x network env)))
    :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                           (k key) (x compose)))
             :in-theory (disable svex-env-lookup-of-svex-alist-eval
                                 <fn>)))
    :fn neteval-ordering-compile)

  (defcong svex-alist-compose-equiv svex-alist-eval-equiv
    (neteval-ordering-compile x network) 2
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))

  (defretd lookup-signal-not-in-network-of-<fn>
    (implies (not (svex-lookup signal network))
             (svex-eval-equiv (svex-lookup signal compose)
                              (if (hons-assoc-equal (svar-fix signal) (neteval-ordering-fix x))
                                  (svex-var signal)
                                (svex-x))))
    :hints (("goal" :in-theory (e/d (svex-eval-equiv
                                     lookup-signal-not-in-network-of-neteval-ordering-eval
                                     svex-eval)
                                    (<fn>
                                     svex-lookup-of-neteval-ordering-compile))))
    :fn neteval-ordering-compile)

  (defretd <fn>-when-signal-not-in-network
    (implies (not (svex-lookup signal network))
             (svex-eval-equiv compose
                              (svex-rsh offset (svex-var signal))))
    :hints (("goal" :in-theory (e/d (svex-eval-equiv
                                     neteval-sigordering-eval-when-signal-not-in-network
                                     svex-eval svex-apply)
                                    (<fn>
                                     svex-lookup-of-neteval-ordering-compile))))
    :fn neteval-sigordering-compile)

  (defretd <fn>-when-signal-not-in-network
    (implies (not (svex-lookup signal network))
             (svex-eval-equiv compose (svex-var signal)))
    :hints (("goal" :in-theory (e/d (svex-eval-equiv
                                     neteval-ordering-or-null-eval-when-signal-not-in-network
                                     svex-eval svex-apply)
                                    (<fn>
                                     svex-lookup-of-neteval-ordering-compile))))
    :fn neteval-ordering-or-null-compile))


(defthm svex-lookup-of-append
  (equal (svex-lookup k (append a b))
         (or (svex-lookup k a)
             (svex-lookup k b)))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))



(define neteval-sigordering-rsh ((n natp)
                                 (x neteval-sigordering-p))
  :returns (new-x neteval-sigordering-p)
               ;; (rem natp :rule-classes :type-prescription))
  (neteval-sigordering-case x
    :segment (if (< (lnfix n) x.width)
                 ;; (mv ;; (neteval-sigordering-fix x)
                     (change-neteval-sigordering-segment
                      x :width (- x.width (lnfix n)))
               ;;0)
               (neteval-sigordering-rsh
                (- (lnfix n) x.width) x.rest))
    :remainder (neteval-sigordering-fix x);; (mv (neteval-sigordering-fix x) (lnfix n))
    )
  ///
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  ;; (defret rem-of-<fn>-bound
  ;;   (<= rem (nfix n))
  ;;   :rule-classes :linear)
  ;; (defretd <fn>-rem-nonzero
  ;;   (implies (not (equal rem 0))
  ;;            (neteval-sigordering-case new-x :remainder)))

  (defret eval-of-<fn>
    (implies (<= (nfix n) (nfix offset))
             (equal ;;(4vec-rsh (2vec rem)
              (neteval-sigordering-eval
               new-x signal offset network env)
              (4vec-rsh (2vec (nfix n))
                        (neteval-sigordering-eval x signal
                                                  (- (nfix offset) (nfix n)) network env))))
    :hints(("Goal" 
            :induct <call>
            :expand ((:free (offset)
                      (neteval-sigordering-eval x signal offset network env))
                     (:free (width ord rest)
                      (neteval-sigordering-eval
                       (neteval-sigordering-segment width ord rest)
                       signal offset network env))
                     (:free (ord)
                      (neteval-sigordering-eval
                       (neteval-sigordering-remainder ord)
                       signal offset network env)))))))


(define neteval-sigordering-concat ((width natp)
                                    (x neteval-sigordering-p)
                                    (y neteval-sigordering-p))
  :returns (concat neteval-sigordering-p)
  :measure (neteval-sigordering-count x)
  :verify-guards :after-returns
  (if (zp width)
      (neteval-sigordering-fix y)
    (neteval-sigordering-case x
      :remainder (make-neteval-sigordering-segment
                  :width width
                  :ord x.ord
                  :rest y)
      :segment (if (<= width x.width)
                   (make-neteval-sigordering-segment
                    :width width
                    :ord x.ord
                    :rest y)
                 (make-neteval-sigordering-segment
                  :width x.width
                  :ord x.ord
                  :rest (neteval-sigordering-concat
                         (- width x.width)
                         x.rest y)))))
  ///
  (local (defun ind (width x offset)
           (declare (xargs :measure (neteval-sigordering-count x)))
           (neteval-sigordering-case x
             :remainder (list width offset)
             :segment (if (<= (nfix width) x.width)
                          offset
                        (ind (- width x.width) x.rest (+ (nfix offset) x.width))))))
  (defret eval-of-<fn>
    (equal (neteval-sigordering-eval
            concat signal offset network env)
           (4vec-concat (2vec (nfix width))
                        (neteval-sigordering-eval
                         x signal offset network env)
                        (neteval-sigordering-eval
                         y signal (+ (lnfix offset) (lnfix width)) network env)))
    :hints (("goal" :induct (ind width x offset)
             :expand (<call>
                      (neteval-sigordering-eval x signal offset network env)
                      (:free (width ord rest offset)
                       (neteval-sigordering-eval
                        (neteval-sigordering-segment width ord rest)
                        signal offset network env)))))))


;; Explanation.  To "compose" two neteval-orderings, what we want is to make an
;; ordering that expresses the process of forming one compiled network using
;; a first ordering (subst), and then compiling that network again using
;; another ordering (x).

;; To make an ordering that expresses this composition is a little tricky.  At
;; the top level, we recur over x and whenever x indicates to compose some
;; signal's function with the compilation of another ordering, we need to
;; instead insert a compound ordering that expresses the composition of that
;; signal's compilation by subst with the composition of that second ordering
;; with subst.  This compound ordering needs to be produced by an aux function
;; that recurs over subst, inserting the composition at the "leaves".

;; That is, we're looking for a new ordering, comp, that satisfies
;;  (neteval-ordering-compile comp network) ===       (svex-alist-eval-equiv)
;;  (neteval-ordering-compile x (neteval-ordering-compile subst network))
;; or (neteval-ordering-eval comp network env) ===    (svex-envs-equivalent)
;;    (neteval-ordering-eval x (neteval-ordering-compile subst network) env).
;; To do this, we need a function that produces a secondary compound ordering
;; aux, such that:
;;    (neteval-ordering-compile aux network) ===
;;      (svex-alist-compose (neteval-ordering-compile x network)
;;                          (neteval-ordering-compile subst network))
;; given orderings x and subst.  But these variable names are a little wrong,
;; because in the top-level composition algorithm the aux function will be
;; composed from a sub-ordering looked up in subst (as x in the equation above)
;; and the composition of the sub-ordering from x with subst (as subst in the
;; equation above).

;; This function produces that secondary compound ordering.

(defines neteval-ordering-compose-aux
  (define neteval-ordering-compose-aux ((x neteval-ordering-p)
                                        (subst neteval-ordering-p))
    :measure (neteval-ordering-count x)
    :verify-guards nil
    :returns (composed neteval-ordering-p)
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x)) nil)
         ((cons signal sigordering) (car x))
         ;; The formula we need this function to satisfy is
         ;; (equal (neteval-ordering-eval (neteval-ordering-compose-aux x subst) network env)
         ;;        (neteval-ordering-eval x network (append (neteval-ordering-eval subst network env) env)))
         ;; Therefore we need for each signal in the ordering
         ;;  (equal (neteval-sigordering-eval compose-sigord function network env)
         ;;         (neteval-sigordering-eval x-sigord function network (append (neteval-ordering-eval subst network env) env)))
         ;; So we make compose-sigord the same shape as x-sigord, and then for each segment we need
         ;; (equal
         ;;  (SVEX-EVAL
         ;;   FUNCTION
         ;;   (APPEND
         ;;    (NETEVAL-ORDERING-EVAL (NETEVAL-SIGORDERING-SEGMENT->ORD COMPOSE-SIGORD)
         ;;                           NETWORK ENV)
         ;;    ENV))
         ;;  (SVEX-EVAL
         ;;   FUNCTION
         ;;   (APPEND
         ;;    (NETEVAL-ORDERING-EVAL (NETEVAL-SIGORDERING-SEGMENT->ORD X-SIGORD)
         ;;                           NETWORK
         ;;                           (APPEND (NETEVAL-ORDERING-EVAL SUBST NETWORK ENV)
         ;;                                   ENV))
         ;;    (NETEVAL-ORDERING-EVAL SUBST NETWORK ENV)
         ;;    ENV)))
         ;; Which is satisfied by letting the ORD field of compose-sigord be
         ;; (append (neteval-ordering-compose-aux x-sigord-ord subst) subst).
         
         (new-sigord (neteval-sigordering-compose-aux sigordering signal 0 subst)))
      (cons (cons signal new-sigord)
            (neteval-ordering-compose-aux (cdr x) subst))))

  (define neteval-sigordering-compose-aux ((x neteval-sigordering-p)
                                           (signal svar-p)
                                           (offset natp)
                                           (subst neteval-ordering-p))
    :measure (neteval-sigordering-count x)
    :returns (composed neteval-sigordering-p)
    (neteval-sigordering-case x
      :segment (neteval-sigordering-concat
                x.width
                ;; :width x.width
                ;; :ord
                (neteval-ordering-or-null-compose-aux x.ord signal offset subst)
                ;; :rest
                (neteval-sigordering-compose-aux x.rest signal (+ (lnfix offset) x.width)subst))
      :remainder ;; (make-neteval-sigordering-remainder
                 ;;  :ord
      (neteval-ordering-or-null-compose-aux x.ord signal offset subst)))

  (define neteval-ordering-or-null-compose-aux ((x neteval-ordering-or-null-p)
                                                (signal svar-p)
                                                (offset natp)
                                                (subst neteval-ordering-p))
    (declare (ignorable signal offset))
    :measure (neteval-ordering-or-null-count x)
    :returns (composed neteval-sigordering-p)
    (neteval-ordering-or-null-case x
      :null (let ((look (hons-assoc-equal (svar-fix signal) (neteval-ordering-fix subst))))
              (if look
                  (neteval-sigordering-rsh offset (cdr look))
                (make-neteval-sigordering-remainder :ord (make-neteval-ordering-or-null-null))))
      ;; (make-neteval-ordering-or-null-null)
      :ordering (make-neteval-sigordering-remainder
                 :ord (make-neteval-ordering-or-null-ordering
                       :ord (append (neteval-ordering-compose-aux x.ord subst) (neteval-ordering-fix subst))))))
  ///

  (defthm-neteval-ordering-compose-aux-flag
    (defthm eval-of-neteval-ordering-compose-aux
      (equal (neteval-ordering-eval (neteval-ordering-compose-aux x subst) network env)
             (neteval-ordering-eval x network (append (neteval-ordering-eval subst network env) env)))
      :hints ('(:expand ((neteval-ordering-compose-aux x subst)
                         (:free (env) (neteval-ordering-eval x network env))
                         (:free (a b) (neteval-ordering-eval (cons a b) network env)))))
      :flag neteval-ordering-compose-aux)
    (defthm eval-of-neteval-sigordering-compose-aux
      ;; (implies (svex-lookup signal network)
      (equal (neteval-sigordering-eval (neteval-sigordering-compose-aux x signal offset subst) signal offset network env)
             (neteval-sigordering-eval x signal offset network
                                       (append (neteval-ordering-eval subst network env) env)))
      :hints ('(:expand ((neteval-sigordering-compose-aux x signal offset subst)
                         (:free (signal offset env) (neteval-sigordering-eval x signal offset network env))
                         (:free (signal offset width ord rest)
                          (neteval-sigordering-eval
                           (neteval-sigordering-segment width ord rest)
                           signal offset network env))
                         (:free (signal offset ord) (neteval-sigordering-eval
                                                     (neteval-sigordering-remainder ord)
                                                     signal offset network env)))))
      :flag neteval-sigordering-compose-aux)
    (defthm eval-of-neteval-ordering-or-null-compose-aux
      ;; (implies (svex-lookup signal network)
      (equal (neteval-sigordering-eval (neteval-ordering-or-null-compose-aux x signal offset subst) signal offset network env)
             (4vec-rsh (2vec (nfix offset))
                       (neteval-ordering-or-null-eval x signal network
                                                      (append (neteval-ordering-eval subst network env) env))))
      :hints ('(:expand ((neteval-ordering-or-null-compose-aux x signal offset subst)
                         (:free (signal offset env) (neteval-ordering-or-null-eval x signal network env))
                         (:free (signal offset ord)
                          (neteval-ordering-or-null-eval
                           (neteval-ordering-or-null-ordering ord)
                           signal network env))
                         (:free (signal offset)
                          (neteval-ordering-or-null-eval
                           '(:null)
                           signal network env))
                         (:free (ord offset)
                          (neteval-sigordering-eval
                           (neteval-sigordering-remainder ord) signal offset network env))
                         (:free (offset)
                          (neteval-sigordering-eval
                           '(:remainder (:null)) signal offset network env)))
                ;; :in-theory (disable svex-env-lookup-of-neteval-ordering-eval)
                ))
      :flag neteval-ordering-or-null-compose-aux))


  (defret compile-of-neteval-ordering-compose-aux
    (svex-alist-eval-equiv (neteval-ordering-compile composed network)
                           (svex-alist-compose (neteval-ordering-compile x network)
                                               (neteval-ordering-compile subst network)))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))
    :fn neteval-ordering-compose-aux)

  (verify-guards neteval-ordering-compose-aux))


;; (verify
;;  (implies (and (consp (neteval-ordering-fix compose))
;;                (consp (neteval-ordering-fix x))
;;                (equal (caar (neteval-ordering-fix compose))
;;                       (caar (neteval-ordering-fix x)))
;;                (hons-assoc-equal (caar (neteval-ordering-fix x))
;;                                  (neteval-ordering-fix subst)))
;;           (equal (neteval-ordering-eval compose network env)
;;                  (neteval-ordering-eval x (neteval-ordering-compile subst network) env))))


;; (verify 
;;  (implies (and (consp (neteval-ordering-fix x))
;;                (consp (neteval-ordering-fix compose))
;;                (equal (caar (neteval-ordering-fix x))
;;                       (caar (neteval-ordering-fix compose)))
;;                (hons-assoc-equal (caar (neteval-ordering-fix x)) subst))
;;           (equal (neteval-ordering-eval compose network env)
;;                  (neteval-ordering-eval x (neteval-ordering-compile subst network) env))))


;; (verify 
;;  (implies (And (neteval-sigordering-case compose-sigord :segment)
;;                (neteval-sigordering-case x-sigord :segment)
;;                (equal (neteval-sigordering-segment->width compose-sigord)
;;                       (neteval-sigordering-segment->width x-sigord)))
;;           (equal (neteval-sigordering-eval compose-sigord function network env)
;;                  (neteval-sigordering-eval x-sigord
;;                                           (neteval-sigordering-compile
;;                                            subst-fn function network)
;;                                           (neteval-ordering-compile subst network)
;;                                           env))))

;; (verify
;;  (implies (And (neteval-sigordering-case compose-sigord :segment)
;;                (neteval-sigordering-case x-sigord :segment)
;;                ;; (equal (neteval-sigordering-segment->width compose-sigord)
;;                ;;        (neteval-sigordering-segment->width x-sigord))
;;                )
;;          (equal (neteval-sigordering-eval compose-sigord function network env)
;;                 (neteval-sigordering-eval x-sigord
;;                                           (neteval-sigordering-compile
;;                                            subst-fn function network)
;;                                           (neteval-ordering-compile subst network)
;;                                           env))))

;; ;; Example of composing a neteval-ordering.
;; ;; Suppose we have 

;; (verify
 
;;  (equal (neteval-ordering-eval compose network env)
;;         (neteval-ordering-eval x (neteval-ordering-compile subst network) env)))



(defcong svex-eval-equiv svex-eval-equiv (svex-concat n x y) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defcong svex-eval-equiv svex-eval-equiv (svex-concat n x y) 3
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(local (defthm svex-compose-of-svex-rsh-under-svex-eval-equiv
         (svex-eval-equiv (svex-compose (svex-rsh n x) a)
                          (svex-rsh n (svex-compose x a)))
         :hints(("Goal" :in-theory (enable svex-eval-equiv)))))


(local (defthm svex-concat-of-svex-rsh-under-svex-eval-equiv
         (svex-eval-equiv (svex-rsh m (svex-concat n x y))
                          (if (< (nfix m) (nfix n))
                              (svex-concat (- (nfix n) (nfix m))
                                           (svex-rsh m x) y)
                            (svex-rsh (- (nfix m) (nfix n)) y)))
         :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))

(local (defthm svex-rsh-of-svex-rsh-under-svex-eval-equiv
         (svex-eval-equiv (svex-rsh m (svex-rsh n x))
                          (svex-rsh (+ (nfix m) (nfix n)) x))
         :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))
                          
  
;; (defcong svex-eval-equiv svex-eval-equiv (neteval-sigordering-compile x function network) 2
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))))

(local (defthm svex-rsh-of-0
         (svex-eval-equiv (svex-rsh 0 x) x)
         :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))


;; (defstub foo (ord) nil)
;; (defaxiom neteval-sigordering-p-foo
;;   (neteval-sigordering-p (foo ord)))


(defines neteval-ordering-compose
  (define neteval-ordering-compose ((x neteval-ordering-p)
                                    (subst neteval-ordering-p))
    :measure (two-nats-measure (neteval-ordering-count x) 0)
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (width ord rest) (neteval-sigordering-count
                                                     (neteval-sigordering-segment width ord rest)))
                            (neteval-sigordering-count x)))))
    :verify-guards nil
    :returns (composed neteval-ordering-p)
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x)) nil)
         ((cons signal sigordering) (car x))
         ;; (subst-look (hons-assoc-equal signal (neteval-ordering-fix subst)))
         ;; ;; We want to produce an ordering (compose) that reflects an ordering (x)
         ;; ;; applied to the network resulting from applying an ordering (subst) to
         ;; ;; the original network (network).
         
         ;; ;; ;; For each binding of a signal to an ordering in X, first, if the signal
         ;; ;; ;; isn't bound in subst then it won't be bound in the composed network so
         ;; ;; ;; we skip it.
         ;; ((unless subst-look)
         ;;  ;; (cons (cons signal (make-neteval-sigordering-remainder
         ;;  ;;                     :ord (make-neteval-ordering-or-null-null)))
         ;;  (neteval-ordering-compose (cdr x) subst))
         
         ;; Assuming it is bound, then we want its binding to reflect the
         ;; composition from x and subst.
         ;; We want the following identity:
         ;; (svex-envs-equiv (neteval-ordering-eval (neteval-ordering-compose x subst) network env)
         ;;                 (neteval-ordering-eval x (neteval-ordering-compile subst network) env))

         ;; Therefore for each signal, we need the following
         ;; need the following
         ;; (equal (neteval-sigordering-eval new-sigord function network env)
         ;;        (neteval-sigordering-eval sigordering
         ;;                                  (neteval-sigordering-compile
         ;;                                   subst-sigord function network)
         ;;                                  (neteval-ordering-compile subst network) env))
        
         ;; which means we need for each segment of new-sigord:
         ;; (equal (select-segment
         ;;           (svex-eval function
         ;;             (append (NETEVAL-ORDERING-EVAL new-sigord-segment-ord
         ;;                                    NETWORK ENV)
         ;;                     ENV))
         ;;        (select-segment
         ;;           (svex-eval function
         ;;               (APPEND
         ;;                (NETEVAL-ORDERING-EVAL
         ;;                 (NETEVAL-SIGORDERING-SEGMENT->ORD SUBST-SIGORD)
         ;;                 NETWORK
         ;;                 (APPEND
         ;;                   (NETEVAL-ORDERING-EVAL (NETEVAL-SIGORDERING-SEGMENT->ORD SIGORDERING)
         ;;                                          (NETEVAL-ORDERING-COMPILE SUBST NETWORK)
         ;;                                          ENV)
         ;;                   ENV))
         ;;                (NETEVAL-ORDERING-EVAL (NETEVAL-SIGORDERING-SEGMENT->ORD SIGORDERING)
         ;;                                       (NETEVAL-ORDERING-COMPILE SUBST NETWORK)
         ;;                                       ENV)
         ;;                ENV))

         ;; So for each segment of new-sigord we need
         ;; (svex-envs-equiv
         ;;             (append 
         ;;                (NETEVAL-ORDERING-EVAL new-sigord-segment-ord
         ;;                                    NETWORK ENV)
         ;;                env)
         ;;              (APPEND
         ;;                (NETEVAL-ORDERING-EVAL
         ;;                 subst-sigord-segment-ord
         ;;                 NETWORK
         ;;                 (APPEND
         ;;                   (NETEVAL-ORDERING-EVAL old-sigord-segment-ord
         ;;                                          (NETEVAL-ORDERING-COMPILE SUBST NETWORK)
         ;;                                          ENV)
         ;;                   ENV))
         ;;                (NETEVAL-ORDERING-EVAL old-sigord-segment-ord
         ;;                                       (NETEVAL-ORDERING-COMPILE SUBST NETWORK)
         ;;                                       ENV)
         ;;                env))
         ;; Inductively using our original desired identity we have
         ;;  (svex-envs-equiv  (NETEVAL-ORDERING-EVAL old-sigord-segment-ord
         ;;                           (NETEVAL-ORDERING-COMPILE SUBST NETWORK)
         ;;                           ENV)
         ;;           (neteval-ordering-eval (neteval-ordering-compose old-sigord-segment-ord subst) network env)
         ;; Call this compose term NEW-ORD1. Restating the above, we need:
         ;; (svex-envs-equiv
         ;;             (append 
         ;;                (NETEVAL-ORDERING-EVAL new-sigord-segment-ord
         ;;                                    NETWORK ENV)
         ;;                env)
         ;;              (APPEND
         ;;                (NETEVAL-ORDERING-EVAL
         ;;                 subst-sigord-segment-ord
         ;;                 NETWORK
         ;;                 (APPEND (neteval-ordering-eval new-ord1 network env) env))
         ;;                (neteval-ordering-eval new-ord1 network env)
         ;;                env))

         ;; Now suppose we have a function neteval-ordering-compose-aux that satisfies
         ;; (equal (neteval-ordering-eval (neteval-ordering-compose-aux x subst) network env)
         ;;        (neteval-ordering-eval x network (append (neteval-ordering-eval subst network env) env)))
         
         ;; Let new-sigord-segment-ord be
         ;;     (append (neteval-ordering-compose-aux subst-sigord-segment-ord new-ord1) new-ord1)
         ;; Substituting in on the LHS above we get
         ;;             (append 
         ;;                (NETEVAL-ORDERING-EVAL
         ;;                 (append (neteval-ordering-compose-aux subst-sigord-segment-ord new-ord1) new-ord1)
         ;;                 NETWORK ENV)
         ;;                env)
         ;;     =       (append
         ;;                (neteval-ordering-eval
         ;;                    (neteval-ordering-compose-aux subst-sigord-segment-ord new-ord1)
         ;;                    network env)
         ;;                (neteval-ordering-eval new-ord1 network env)
         ;;                env)
         ;;     =      (append
         ;;                (neteval-ordering-eval subst-sigord-segment-ord network
         ;;                                      (append (neteval-ordering-eval new-ord1 network env)
         ;;                                              env))
         ;;                (neteval-ordering-eval new-ord1 network env)
         ;;                env).

         ;; So then we need neteval-ordering-compose-aux.

         

         (new-sigord (neteval-sigordering-compose sigordering signal 0 ;; (cdr subst-look)
                                                  subst)))
      (cons (cons signal new-sigord)
            (neteval-ordering-compose (cdr x) subst))))

  (define neteval-sigordering-compose ((x neteval-sigordering-p)
                                       ;; (subst-sigord neteval-sigordering-p)
                                       (signal svar-p)
                                       (offset natp)
                                       (subst neteval-ordering-p))
    :measure (two-nats-measure (neteval-sigordering-count x) 0)
    ;; :guard (hons-assoc-equal signal subst)
    :returns (composed neteval-sigordering-p)
    (neteval-sigordering-case x
      :segment (b* (;; (compose-ord (neteval-ordering-or-null-compose x.ord signal subst))
                    (full-sigord (neteval-ordering-or-null-compose
                                  x.ord signal subst
                                  ;; (cdr (hons-assoc-equal (svar-fix signal)
                                  ;;                        (neteval-ordering-fix subst)))
                                  ;; signal 0 compose-ord
                                  ))
                    (rest (neteval-sigordering-compose x.rest signal (+ x.width (lnfix offset)) subst)))
                 (neteval-sigordering-concat
                  x.width
                  (neteval-sigordering-rsh offset full-sigord)
                  rest))
      :remainder (b* (;; (compose-ord (neteval-ordering-or-null-compose x.ord signal subst))
                      (full-sigord (neteval-ordering-or-null-compose
                                    x.ord signal subst
                                    ;; (cdr (hons-assoc-equal (svar-fix signal)
                                    ;;                        (neteval-ordering-fix subst)))
                                    ;; signal 0 compose-ord
                                    )))
                   (neteval-sigordering-rsh offset full-sigord))))
                                  


    ;; (b* (((mv width x-ord x-rest subst-ord subst-rest)
    ;;       (neteval-sigordering-case x
    ;;         :segment (neteval-sigordering-case subst-sigord
    ;;                    :segment (cond ((< x.width subst-sigord.width)
    ;;                                    (mv x.width x.ord x.rest
    ;;                                        subst-sigord.ord
    ;;                                        (make-neteval-sigordering-segment
    ;;                                         :width (- subst-sigord.width x.width)
    ;;                                         :ord subst-sigord.ord
    ;;                                         :rest subst-sigord.rest)))
    ;;                                   ((eql x.width subst-sigord.width)
    ;;                                    (mv x.width x.ord x.rest subst-sigord.ord subst-sigord.rest))
    ;;                                   (t ;; (< subst-sigord.width x.width)
    ;;                                    (mv subst-sigord.width
    ;;                                        x.ord
    ;;                                        (make-neteval-sigordering-segment
    ;;                                         :width (- x.width subst-sigord.width)
    ;;                                         :ord x.ord
    ;;                                         :rest x.rest)
    ;;                                        subst-sigord.ord
    ;;                                        subst-sigord.rest)))
    ;;                    :remainder (mv x.width x.ord x.rest subst-sigord.ord subst-sigord))
    ;;         :remainder (neteval-sigordering-case subst-sigord
    ;;                      :segment (mv subst-sigord.width x.ord x subst-sigord.ord subst-sigord.rest)
    ;;                      :remainder (mv nil x.ord x subst-sigord.ord subst-sigord))))
    ;;      ;; width is nil means we're done.
    ;;      (new-ord (neteval-ordering-or-null-compose x-ord subst-ord subst))
    ;;      ;; (new-ord1 (neteval-ordering-compose x-ord subst))
    ;;      ;; (new-ord-full
    ;;      ;;  (append (neteval-ordering-or-null-compose-aux subst-ord new-ord1) new-ord1))
    ;;      )
    ;;   (if width
    ;;       (make-neteval-sigordering-segment
    ;;        :width width
    ;;        :ord new-ord
    ;;        :rest (neteval-sigordering-compose x-rest subst-rest subst))
    ;;     (make-neteval-sigordering-remainder :ord new-ord))))
  (define neteval-ordering-or-null-compose ((x neteval-ordering-or-null-p)
                                            (signal svar-p)
                                            ;; (subst-ord neteval-ordering-or-null-p)
                                            (subst neteval-ordering-p))
    (declare (ignorable signal))
    :measure (two-nats-measure (neteval-ordering-or-null-count x)
                               ;; (neteval-ordering-or-null-count subst-ord)
                               0)
    ;; :guard (hons-assoc-equal signal subst)
    :returns (composed neteval-sigordering-p)
    (neteval-ordering-or-null-case x
      :null (make-neteval-sigordering-remainder :ord (make-neteval-ordering-or-null-null))
      :ordering ;; (neteval-ordering-or-null-case x
                ;;   :null (make-neteval-ordering-or-null-null)
                ;;   :ordering
                  ;; (b* ((new-ord1 )
                            ;;      (new-ord-full
                            ;;       (append (neteval-ordering-compose-aux
                            ;;                subst-ord.ord new-ord1)
                            ;;               new-ord1)))
      (b* ((ord (neteval-ordering-compose x.ord subst))
           (look (hons-assoc-equal
                            (svar-fix signal) (neteval-ordering-fix subst)))
           ;; ((unless look)
           ;;  (make-neteval-sigordering-remainder
           ;;                              :ord (make-neteval-ordering-or-null-n )))
           ((unless look)
            (let ((ord-look (hons-assoc-equal (svar-fix signal) ord)))
              (if ord-look
                  (cdr ord-look)
                (make-neteval-sigordering-remainder
                 :ord (make-neteval-ordering-or-null-null)))))
           (sigord ;; (if look (cdr look) (foo ord))
            (cdr look))
           (full-ord (neteval-sigordering-compose-aux
                      sigord signal 0 ord)))
        full-ord)))

  ///
  (local (defthm svex-rsh-of-neteval-sigordering-compile-when-remainder
           (implies (neteval-sigordering-case x :remainder)
                    (svex-eval-equiv
                     (svex-rsh n (neteval-sigordering-compile x signal offset network))
                     (neteval-sigordering-compile x signal (+ (nfix n) (nfix offset)) network)))
           :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)
                   :expand ((:free (signal offset env) (neteval-sigordering-eval x signal offset network env))
                            (:free (x signal offset env) (neteval-ordering-or-null-eval x signal network env)))))))


  ;; (local
  ;;  (defquant eval-of-neteval-sigordering-compose-cond (composed x signal  subst network env)
  ;;    (forall (sig offset)
  ;;            (equal (neteval-sigordering-eval composed sig offset network env)
  ;;                   (neteval-sigordering-eval x sig offset
  ;;                                             (neteval-ordering-compile subst network) env)))
  ;;    :rewrite :direct))

  ;; (local
  ;;  (defquant eval-of-neteval-ordering-or-null-compose-cond (composed x subst-sigord subst network env)
  ;;    (forall (sig offset)
  ;;            (equal (neteval-ordering-or-null-eval composed sig network env)
  ;;                   (neteval-ordering-or-null-eval x sig
  ;;                                             (neteval-ordering-compile subst network) env)))
  ;;    :rewrite :direct))

  ;; (local (in-theory (e/d (eval-of-neteval-sigordering-compose-cond-necc
  ;;                         eval-of-neteval-ordering-or-null-compose-cond-necc)
  ;;                        (eval-of-neteval-sigordering-compose-cond
  ;;                         eval-of-neteval-ordering-or-null-compose-cond))))


  (local
   (std::defret-mutual eval-of-neteval-ordering-compose
     (defret eval-of-neteval-ordering-compose
       (equal (neteval-ordering-eval composed network env)
              (neteval-ordering-eval x (neteval-ordering-compile subst network) env))
       :hints ('(:expand ((neteval-ordering-compose x subst)
                          (:free (network) (neteval-ordering-eval x network env))
                          (:free (a b) (neteval-ordering-eval (cons a b) network env)))))
       :fn neteval-ordering-compose)
     (defret eval-of-neteval-sigordering-compose-lemma
       ;; (eval-of-neteval-sigordering-compose-cond
       ;;  composed x subst-sigord subst network env)
       (implies (and ;; (hons-assoc-equal (svar-fix signal)
                     ;;                   (neteval-ordering-fix subst))
                     ;; (svex-lookup signal network)
                     )
                (equal (neteval-sigordering-eval composed signal offset network env)
                       (neteval-sigordering-eval x signal offset
                                                 (neteval-ordering-compile subst network)
                                                 env)))
       :hints ('(:expand
                 ((:free (net) (neteval-sigordering-eval x signal offset net env))))

;; (acl2::witness :ruleset (eval-of-neteval-sigordering-compose-cond-witnessing))
               
               ;; (and stable-under-simplificationp
               ;;      `(:expand ((neteval-sigordering-compose x subst-sigord subst) ;;,(Car (last clause))
               ;;                 (:free (function network) (neteval-sigordering-eval x function network env))
               ;;                 (:free (function network env)
               ;;                  (neteval-sigordering-eval subst-sigord function network env))
               ;;                 (:free (ord function network env)
               ;;                  (neteval-sigordering-eval
               ;;                   (neteval-sigordering-remainder ord) function network env))
               ;;                 (:free (width ord rest function network env)
               ;;                  (neteval-sigordering-eval
               ;;                   (neteval-sigordering-segment width ord rest) function network env))
               ;;                 (:free (ord function network env)
               ;;                  (neteval-sigordering-compile
               ;;                   (neteval-sigordering-remainder ord) function network))
               ;;                 (:free (width ord rest function network env)
               ;;                  (neteval-sigordering-compile
               ;;                   (neteval-sigordering-segment width ord rest) function network))
               ;;                 )))
               ;; (and stable-under-simplificationp
               ;;      `(:expand ((:free (function network)
               ;;                  (neteval-sigordering-compile subst-sigord function network)))))
               )
       :fn neteval-sigordering-compose)
     (defret eval-of-neteval-ordering-or-null-compose-lemma
       (implies (and ;; (hons-assoc-equal (svar-fix signal)
                     ;;                   (neteval-ordering-fix subst))
                     ;; (svex-lookup signal network)
                     )
                (equal (neteval-sigordering-eval composed signal 0 network env)
                       (neteval-ordering-or-null-eval x signal (neteval-ordering-compile subst network) env)))
       :hints (;; (acl2::witness :ruleset (eval-of-neteval-ordering-or-null-compose-cond-witnessing))
               (and stable-under-simplificationp
                    '(:expand ((:free (sig offset env)
                                (neteval-ordering-or-null-eval
                                 '(:null) sig network env))
                               (:free (env)
                                (neteval-sigordering-eval
                                 '(:remainder (:null)) signal 0 network env))
                               (:free (ord sig offset)
                                (neteval-ordering-or-null-eval
                                 (neteval-ordering-or-null-ordering ord)
                                 sig network env))
                               (:free (sig network env)
                                (neteval-ordering-or-null-eval
                                 x sig network env)))
                      :in-theory (enable svex-compose-lookup)))
               (and stable-under-simplificationp
                    '(:expand ((:Free (var env) (svex-eval (svex-var var) env)))))
               ;; (and stable-under-simplificationp
               ;;      `(:expand ((neteval-ordering-or-null-compose x subst-sigord subst) ;;,(Car (last clause))
               ;;                 (:free (function network) (neteval-ordering-or-null-eval x function network env))
               ;;                 (:free (function network env)
               ;;                  (neteval-ordering-or-null-eval subst-sigord function network env))
               ;;                 (:free (ord function network env)
               ;;                  (neteval-ordering-or-null-eval
               ;;                   (neteval-ordering-or-null-remainder ord) function network env))
               ;;                 (:free (width ord rest function network env)
               ;;                  (neteval-ordering-or-null-eval
               ;;                   (neteval-ordering-or-null-segment width ord rest) function network env))
               ;;                 (:free (ord function network env)
               ;;                  (neteval-ordering-or-null-compile
               ;;                   (neteval-ordering-or-null-remainder ord) function network))
               ;;                 (:free (width ord rest function network env)
               ;;                  (neteval-ordering-or-null-compile
               ;;                   (neteval-ordering-or-null-segment width ord rest) function network))
               ;;                 )))
               ;; (and stable-under-simplificationp
               ;;      `(:expand ((:free (function network)
               ;;                  (neteval-ordering-or-null-compile subst-sigord function network)))))
               )
       :fn neteval-ordering-or-null-compose)))

  (defret eval-of-neteval-ordering-compose
    (equal (neteval-ordering-eval composed network env)
           (neteval-ordering-eval x (neteval-ordering-compile subst network) env))
    :fn neteval-ordering-compose)

  (defret eval-of-neteval-sigordering-compose
    (implies (and ;; (hons-assoc-equal (svar-fix signal)
                  ;;                   (neteval-ordering-fix subst))
                  ;; (svex-lookup signal network)
                  )
             (equal (neteval-sigordering-eval composed signal offset network env)
                    (neteval-sigordering-eval x signal offset
                                              (neteval-ordering-compile subst network) env)))
    :hints (("Goal" :use eval-of-neteval-sigordering-compose-lemma
             :in-theory (disable eval-of-neteval-sigordering-compose-lemma)))
    :fn neteval-sigordering-compose)

  (defret compile-of-neteval-ordering-compose
    (svex-alist-eval-equiv (neteval-ordering-compile composed network)
                           (neteval-ordering-compile x (neteval-ordering-compile subst network)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv)))
    :fn neteval-ordering-compose)

  (verify-guards neteval-sigordering-compose))

(local (defthm neteval-ordering-p-of-pair-keys
         (implies (and (svarlist-p keys)
                       (neteval-sigordering-p ord))
                  (neteval-ordering-p (pair-keys keys ord)))
         :hints(("Goal" :in-theory (enable pair-keys)))))

(define neteval-ordering-null ((keys svarlist-p))
  :returns (ordering neteval-ordering-p)
  (pair-keys (svarlist-fix keys)
             (neteval-sigordering-remainder (neteval-ordering-or-null-null)))
  ///
  (defret eval-of-<fn>
    (svex-envs-equivalent (neteval-ordering-eval ordering network env)
                          (svex-env-extract keys
                                                                ;; (svex-alist-keys network))
                                            env))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent)
            :expand ((:free (signal)
                      (neteval-sigordering-eval '(:remainder (:null)) signal 0 network env))
                     (:free (signal)
                      (neteval-ordering-or-null-eval
                       '(:null) signal network env))))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile ordering network)
                           (svex-identity-subst keys)
                           ;; (intersection-equal (svarlist-fix keys)
                           ;;                                          (svex-alist-keys network))
                           )
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (<fn>))))))
            


(define neteval-ordering-identity ((keys svarlist-p))
  :returns (ordering neteval-ordering-p)
  (pair-keys (svarlist-fix keys)
             (neteval-sigordering-remainder
              (neteval-ordering-or-null-ordering nil)))
  ///
  (defret eval-of-<fn>
    (svex-envs-equivalent (neteval-ordering-eval ordering network env)
                          (SVEX-ENV-extract KEYS (append (SVEX-ALIST-EVAL NETWORK ENV) env)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile ordering network)
                           (svex-alist-compextract keys network))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (<fn>))))))

;; (i-am-here)

(define neteval-ordering-reduce ((vars svarlist-p) (x neteval-ordering-p))
  :returns (new-ord neteval-ordering-p)
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

(define neteval-ordering-extract ((vars svarlist-p) (x neteval-ordering-p))
  :returns (new-ord neteval-ordering-p)
  (if (atom vars)
      nil
    (let ((look (hons-assoc-equal (svar-fix (car vars))
                                  (neteval-ordering-fix x))))
      (if look
          (cons look (neteval-ordering-extract (cdr vars) x))
        (cons (cons (svar-fix (car vars))
                    (neteval-sigordering-remainder
                     (neteval-ordering-or-null-null)))
              (neteval-ordering-extract (cdr vars) x)))))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key new-ord)
           (and (member-equal key (svarlist-fix vars))
                (or (hons-assoc-equal key (neteval-ordering-fix x))
                    (cons key (neteval-sigordering-remainder
                               (neteval-ordering-or-null-null)))))))

  (defret eval-of-<fn>
    (equal (neteval-ordering-eval new-ord network env)
           (svex-env-extract vars (append (neteval-ordering-eval x network env) env)))
    :hints(("Goal" :in-theory (enable svex-env-extract neteval-ordering-eval)
            :expand ((:free (signal offset)
                      (neteval-sigordering-eval '(:remainder (:null)) signal offset network env))
                     (:free (signal)
                      (neteval-ordering-or-null-eval '(:null) signal network env))))))

  (defret compile-of-<fn>
    (svex-alist-eval-equiv (neteval-ordering-compile new-ord network)
                           (svex-alist-compextract vars (neteval-ordering-compile x network)))
    :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv-in-terms-of-envs-equivalent)
                                   (neteval-ordering-extract))
            :do-not-induct t))))

                 

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
            (svex-alist-compose-equiv comp (neteval-ordering-compile ordering decomp))))

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

  (define netcomp-p-eval-equiv-witness ((comp svex-alist-p)
                                        (decomp svex-alist-p))
    :non-executable t
    :returns (ord neteval-ordering-p)
    :verify-guards nil
    ;; Despite only requiring that comp is compose-equiv, netcomp-p actually
    ;; assures that there is an ordering that is eval-equiv.
    (neteval-ordering-extract (svex-alist-keys comp)
                              (netcomp-p-witness (svex-alist-fix comp)
                                                 (svex-alist-fix decomp)))
    ///
    

    (defthm svex-alist-compextract-keys-under-compose-equiv
      (svex-alist-eval-equiv (svex-alist-compextract (svex-alist-keys x) x) x)
      :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))
             (and stable-under-simplificationp
                  '(:in-theory (enable svex-compose-lookup)))))

    (defret netcomp-p-implies-eval-equiv-witness
      (implies (netcomp-p comp decomp)
               (svex-alist-eval-equiv (neteval-ordering-compile ord decomp) comp))
      :hints (("goal" :use ((:instance netcomp-p
                             (comp (svex-alist-fix comp))
                             (decomp (svex-alist-fix decomp)))))))

    (defthmd netcomp-p-redef
      (equal (netcomp-p comp decomp)
             (let ((ordering (netcomp-p-eval-equiv-witness comp decomp)))
               (svex-alist-eval-equiv comp (neteval-ordering-compile ordering decomp))))
      :hints (("goal" :cases ((netcomp-p comp decomp))
               :use ((:instance netcomp-p-suff
                      (ordering (netcomp-p-eval-equiv-witness comp decomp))))
               :in-theory (e/d (netcomp-p-implies-eval-equiv-witness)
                               (netcomp-p-suff
                                netcomp-p-eval-equiv-witness))))
      :rule-classes :definition))


  (local (defthm svex-compose-lookup-of-append
           (equal (Svex-compose-lookup key (append x y))
                  (or (svex-lookup key x)
                      (svex-compose-lookup key y)))
           :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

  (local (defthm svex-eval-equiv-of-svex-lookup-when-compose-equiv
           (implies (and (svex-alist-compose-equiv x y)
                         (svex-lookup k x) (svex-lookup k y))
                    (equal (svex-eval-equiv (svex-lookup k x) (svex-lookup k y)) t))
           :hints (("goal" :use ((:instance svex-alist-compose-equiv-necc
                                  (var k)))
                    :in-theory (e/d (svex-compose-lookup)
                                    (svex-alist-compose-equiv-necc))))))
  


  (defthmd netcomp-p-transitive
    (implies (and (netcomp-p x y)
                  (netcomp-p y z))
             (netcomp-p x z))
    :hints (("goal" :expand ((netcomp-p x y)
                             (netcomp-p y z))
             :use ((:instance netcomp-p-suff
                    (comp x) (decomp z)
                    (ordering (neteval-ordering-compose (netcomp-p-eval-equiv-witness x y)
                                                        (netcomp-p-eval-equiv-witness y z))))))))

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

  (defthm netcomp-p-of-svex-alist-reduce
    (implies (netcomp-p x y)
             (netcomp-p (svex-alist-reduce keys x) y))
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp (svex-alist-reduce keys x))
                           (decomp y)
                           (ordering (neteval-ordering-reduce keys (netcomp-p-eval-equiv-witness x y)))))
             :expand ((netcomp-p x y)))))


  ;; (defcong svex-alist-compose-equiv svex-alist-compose-equiv
  ;;   (svex-alist-compose x subst) 1
  ;;   :hints ((and stable-under-simplificationp
  ;;                (let* ((lit (car (last clause))))
  ;;                  `(:expand (,lit
  ;;                             (:free (var) (svex-compose (Svex-var var) subst)))
  ;;                    :use ((:instance svex-alist-compose-equiv-necc
  ;;                           (var (svex-alist-compose-equiv-witness . ,(cdr lit)))
  ;;                           (y x-equiv)))
  ;;                    :in-theory (e/d (svex-compose-lookup)
  ;;                                    (svex-alist-compose-equiv-necc
  ;;                                     svex-alist-compose-equiv-implies-svex-eval-equiv-svex-compose-lookup-2)))))))
  
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


  (defthm netcomp-p-of-svex-alist-compose
    (implies (and (netcomp-p x network)
                  (netcomp-p subst network))
             (netcomp-p (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-p-eval-equiv-witness x network)
                                      (netcomp-p-eval-equiv-witness subst network)))))
             :expand ((netcomp-p x network)
                      (netcomp-p subst network)))))

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

  (defthm netcomp-p-of-svex-identity-subst
    (implies (subsetp-equal (svarlist-fix vars) (svex-alist-keys network))
             (netcomp-p (svex-identity-subst vars) network))
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp (svex-identity-subst vars))
                           (decomp network)
                           (ordering (neteval-ordering-null vars))))
             :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                svex-envs-equivalent))))


  (defthm netcomp-p-of-append
    (implies (and (netcomp-p x network)
                  (netcomp-p y network))
             (netcomp-p (append x y) network))
    :hints (("goal" :expand ((netcomp-p x network)
                             (netcomp-p y network)
                             (SVEX-ALIST-compose-equiv
                              (APPEND X Y)
                              (APPEND (NETEVAL-ORDERING-COMPILE (NETCOMP-P-EVAL-EQUIV-WITNESS X NETWORK)
                                                                NETWORK)
                                      (NETEVAL-ORDERING-COMPILE (NETCOMP-P-EVAL-EQUIV-WITNESS Y NETWORK)
                                                                NETWORK))))
             :in-theory (disable svex-lookup-of-neteval-ordering-compile)
             :use ((:instance netcomp-p-suff
                    (comp (append x y)) (decomp network)
                    (ordering (append (netcomp-p-eval-equiv-witness x network)
                                      (netcomp-p-eval-equiv-witness y network)))))
             :do-not-induct t))))




;; (define svex-alist-bijection-p ((ab svex-alist-p)
;;                                 (ba svex-alist-p))
;;   :verify-guards nil
;;   (and (svex-alist-eval-equiv
;;         (svex-alist-compose ab ba)
;;         (svex-identity-subst (svex-alist-keys ab)))
;;        (svex-alist-eval-equiv
;;         (svex-alist-compose ba ab)
;;         (svex-identity-subst (svex-alist-keys ba))))
;;   ///
;;   (defthm svex-alist-bijection-p-rewrite
;;     (implies (svex-alist-bijection-p ab ba)
;;              (and (svex-alist-eval-equiv
;;                    (svex-alist-compose ab ba)
;;                    (svex-identity-subst (svex-alist-keys ab)))
;;                   (svex-alist-eval-equiv
;;                    (svex-alist-compose ba ab)
;;                    (svex-identity-subst (svex-alist-keys ba))))))

;;   (defthm svex-alist-bijection-p-eval
;;     (implies (svex-alist-bijection-p ab ba)
;;              (and (svex-envs-equivalent
;;                    (svex-alist-eval ab (append (svex-alist-eval ba env) env))
;;                    (svex-env-extract (svex-alist-keys ab) env))
;;                   (svex-envs-equivalent
;;                    (svex-alist-eval ba (append (svex-alist-eval ab env) env))
;;                    (svex-env-extract (svex-alist-keys ba) env))))
;;     :hints (("goal" :use ((:instance svex-alist-eval-of-svex-compose
;;                            (x ab) (subst ba))
;;                           (:instance svex-alist-eval-of-svex-compose
;;                            (x ba) (subst ab)))
;;              :in-theory (disable svex-alist-eval-of-svex-compose)))))


;; (defines neteval-ordering-transform
;;   (define neteval-ordering-transform ((x neteval-ordering-p)
;;                                       (network svex-alist-p)
;;                                       (ab svex-alist-p)
;;                                       (ba svex-alist-p))
;;     (b* ((x (neteval-ordering-fix x))
;;          ((when (atom x))
;;           nil)
;;          ((cons signal sigordering) (car x))
;;          (function (svex-lookup signal network))
;;          ((unless function)
;;           (neteval-ordering-eval (cdr x) network env)))
;;       (cons (cons signal
;;                   (neteval-sigordering-eval sigordering function network env)
;;                   ;; (svex-eval assign
;;                   ;;            ;; (svex-network-join-envs network 
;;                   ;;            (append (neteval-ordering-eval ordering network env)
;;                   ;;                    env))
;;                   )
;;             (neteval-ordering-eval (cdr x) network env)))




;; (defthm netcomp-p-of-bijective-composition
;;   (implies (and (svex-alist-bijection-p ab ba)
;;                 (netcomp-p x network))
;;            (netcomp-p (svex-alist-compose ba
;;                                           (svex-alist-compose x ab))
;;                       (svex-alist-compose ba
;;                                           (svex-alist-compose network ab)))))


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
                    (neteval-ordering (netcomp-p-eval-equiv-witness updates network))))))))


(defthm svex-env-removekeys-under-svex-envs-similar
  (svex-envs-similar (svex-env-removekeys vars x)
                     (append (svarlist-x-env vars) x))
  :hints(("Goal" :in-theory (enable svex-envs-similar))))




