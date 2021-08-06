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

;; orderings.  If a signal is not mapped, then its value is X.  A neteval
;; ordering produces a valuation (svex-env) given a network of assignments
;; (svex-alist) recursively.
(fty::deftypes neteval-ordering
  (fty::defmap neteval-ordering :key-type svar :val-type neteval-sigordering :true-listp t
    :measure (two-nats-measure (acl2-count x) 0))
  (fty::deftagsum neteval-sigordering
    (:segment ((width posp :rule-classes :type-prescription)
               (ord neteval-ordering-p)
               (rest neteval-sigordering-p)))
    (:remainder ((ord neteval-ordering-p)))
    :measure (two-nats-measure (acl2-count x) 1)
    :base-case-override :remainder))

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



(defines neteval-ordering-eval
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
         ((cons signal sigordering) (car x))
         (function (svex-lookup signal network))
         ((unless function)
          (neteval-ordering-eval (cdr x) network env)))
      (cons (cons signal
                  (neteval-sigordering-eval sigordering function network env)
                  ;; (svex-eval assign
                  ;;            ;; (svex-network-join-envs network 
                  ;;            (append (neteval-ordering-eval ordering network env)
                  ;;                    env))
                  )
            (neteval-ordering-eval (cdr x) network env))))
  (define neteval-sigordering-eval ((x neteval-sigordering-p)
                                    (function svex-p)
                                    (network svex-alist-p)
                                    (env svex-env-p))
    :guard (not (intersectp-equal (alist-keys (svex-env-fix env))
                                  (svex-alist-keys network)))
    :measure (neteval-sigordering-count x)
    :returns (val 4vec-p)
    (neteval-sigordering-case x
      ;; Bunch of possible ways to code this:
      ;;  - take the offset as an additional parameter (no; extra parameter
      ;;    seems like it would complicate things)
      ;;  - rightshift the result of the recursion (no, this doesn't work, confusingly)
      ;;  - modify the function when we recur on it
      :segment (4vec-concat (2vec x.width)
                            (svex-eval function
                                       (append (neteval-ordering-eval x.ord network env)
                                               env))
                            (neteval-sigordering-eval x.rest (svex-rsh x.width function) network env))
      :remainder (svex-eval function (append (neteval-ordering-eval x.ord network env)
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

  (defret keys-subsetp-of-<fn>
    (subsetp-equal (alist-keys neteval) (svex-alist-keys network))
    :hints(("goal" :in-theory (enable alist-keys)
            :induct t
            :expand (<call>)))
    :fn neteval-ordering-eval)

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp key neteval)
         (and (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x))
              (svex-lookup key network)))
    :hints(("goal" :in-theory (e/d (svex-env-boundp)
                             (hons-assoc-equal-of-neteval-ordering-fix))
            :induct t
             :expand (<call>)))
    :fn neteval-ordering-eval)

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key neteval)
           (let* ((look (hons-assoc-equal (svar-fix key) (neteval-ordering-fix x)))
                  (sigordering (cdr look))
                  (function (svex-lookup key network)))
             (if (and look function)
                 (neteval-sigordering-eval sigordering function network env)
               (4vec-x))))
    :hints(("goal" :in-theory (e/d (svex-env-lookup)
                             (hons-assoc-equal-of-neteval-ordering-fix))
            :induct t
            :expand (<call>)))
    :fn neteval-ordering-eval)
      ;; hard to predict which of the two will produce better induction scheme
      ;; but for now will go with rightshifting the result since it seems simpler.

  (local (defun-sk neteval-sigordering-eval-svex-eval-cond (x network env)
           (forall (function function-equiv)
                   (implies (and (svex-eval-equiv function-equiv (double-rewrite function))
                                 (syntaxp (not (equal function-equiv function))))
                            (equal (neteval-sigordering-eval x function network env)
                                   (neteval-sigordering-eval x function-equiv network env))))
           :rewrite :direct))

  (local (in-theory (disable neteval-sigordering-eval-svex-eval-cond)))

  (local (defthmd neteval-ordering-eval-svex-eval-thm
           (neteval-sigordering-eval-svex-eval-cond x network env)
           :hints (("goal" :induct (neteval-sigordering-ind x))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))
                                   (:free (function) (neteval-sigordering-eval x function network env))))))))


  (defcong svex-eval-equiv equal (neteval-sigordering-eval x function network env) 2
    :hints (("goal" :use (neteval-ordering-eval-svex-eval-thm
                          neteval-sigordering-eval-svex-eval-cond-necc)
             :in-theory (disable neteval-sigordering-eval-svex-eval-cond-necc))))


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
    (defthm svex-alist-eval-equiv-implies-equal-neteval-ordering-eval-2
      (implies (svex-alist-eval-equiv network network-equiv)
               (equal (neteval-ordering-eval x network env)
                      (neteval-ordering-eval x network-equiv env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-eval
      :rule-classes :congruence)

    (defthm svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv
      (implies (svex-alist-eval-equiv network network-equiv)
               ;; (svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond
               ;;  x function network network-equiv env)
               (equal (neteval-sigordering-eval x function network env)
                      (neteval-sigordering-eval x function network-equiv env))
               )
      :hints ('(:expand (;; (svex-alist-eval-equiv-implies-equal-neteval-sigordering-eval-2-when-functions-equiv-cond
                         ;;  x function network network-equiv env)
                         (:free (network function) (neteval-sigordering-eval x function network env)))))
      :flag neteval-sigordering-eval
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
    (DEFTHM SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-NETEVAL-sigORDERING-EVAL-4
      (IMPLIES (SVEX-ENVS-SIMILAR ENV ENV-EQUIV)
               (EQUAL (NETEVAL-sigORDERING-EVAL X function NETWORK ENV)
                      (NETEVAL-sigORDERING-EVAL X function NETWORK ENV-EQUIV)))
      :hints ('(:expand ((:free (env) (NETEVAL-sigORDERING-EVAL X function NETWORK ENV)))))
      :flag neteval-sigordering-eval
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
             (let ((look (svex-lookup var network)))
               (if (and (svar-p var) look)
                   (cons (cons var
                               (neteval-sigordering-eval ord1 look network env))
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

    (defthm neteval-ordering-eval-of-pair-remainders
      (implies (and (svarlist-p keys)
                    (neteval-sigordering-case val :remainder))
               (equal (neteval-ordering-eval (pair-keys keys val) network env)
                      (svex-alist-eval (svex-alist-reduce keys network)
                                       (append (neteval-ordering-eval (neteval-sigordering-remainder->ord val)
                                                                         network env)
                                               env))))
      :hints(("Goal" :in-theory (enable pair-keys svex-env-reduce-redef)
              :induct t
              :expand ((:free (function) (neteval-sigordering-eval val function network env))))))
    )


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
         (assign (svex-lookup signal network))
         ((unless assign)
          (neteval-ordering-compile (cdr x) network)))
      (cons (cons signal
                  (neteval-sigordering-compile ordering assign network))
            ;; (svex-compose assign
            ;;               (neteval-ordering-compile ordering network)))
            (neteval-ordering-compile (cdr x) network))))
  (define neteval-sigordering-compile ((x neteval-sigordering-p)
                                       (function svex-p)
                                       (network svex-alist-p))
    :measure (neteval-sigordering-count x)
    :returns (compose svex-p)
    (neteval-sigordering-case x
      :segment (svex-concat x.width
                            (svex-compose function (neteval-ordering-compile x.ord network))
                            (neteval-sigordering-compile x.rest (svex-rsh x.width function) network))
      :remainder (svex-compose function (neteval-ordering-compile x.ord network))))
  ///

  (local (defthm neteval-ordering-compile-induction
           t
           :rule-classes ((:induction :pattern (neteval-ordering-compile x network)
                           :scheme (neteval-ordering-selfinduct x)))))
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
                        (neteval-ordering-eval x network env)))))
    (defret eval-of-<fn>
      ;; (implies (not (intersectp-equal (alist-keys (svex-env-fix env))
      ;;                                 (svex-alist-keys network)))
      (equal (svex-eval compose env)
             (neteval-sigordering-eval x function network env))
      :fn neteval-sigordering-compile
      :hints('(:in-theory (enable svex-alist-eval svex-apply)
               :expand (<call>
                        (neteval-sigordering-eval x function network env))))))

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
                (net-look (svex-lookup key network)))
             (and ord-look net-look
                  (neteval-sigordering-compile (cdr ord-look) net-look network))))
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
           (let ((look (svex-lookup var network)))
             (if (and (svar-p var) look)
                 (cons (cons var (neteval-sigordering-compile ord1 look network))
                       (neteval-ordering-compile ord2 network))
               (neteval-ordering-compile ord2 network))))
    :hints (("goal" :expand ((neteval-ordering-compile (cons (cons var ord1) ord2) network)))
            (and stable-under-simplificationp
                 '(:expand ((neteval-ordering-compile ord2 network))))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (neteval-ordering-compile x network) 2
    :hints(("Goal" :in-theory (disable neteval-ordering-compile))
           `(:expand ,(car (last clause)))))

  (defthm neteval-ordering-compile-of-pair-remainders
      (implies (and (svarlist-p keys)
                    (neteval-sigordering-case val :remainder))
               (equal (neteval-ordering-compile (pair-keys keys val) network)
                      (svex-alist-compose (svex-alist-reduce keys network)
                                          (neteval-ordering-compile (neteval-sigordering-remainder->ord val)
                                                                    network))))
      :hints(("Goal" :in-theory (enable pair-keys svex-alist-reduce svex-alist-compose svex-acons)
              :induct t
              :expand ((:free (function) (neteval-sigordering-compile val function network))
                       (neteval-ordering-compile nil network)))))

  ;; (defthm neteval-ordering-compile-of-pair-keys
  ;;   (implies (svarlist-p keys)
  ;;            (equal (neteval-ordering-compile (pair-keys keys val) network)
  ;;                   (svex-alist-compose (svex-alist-reduce keys network)
  ;;                                       (neteval-ordering-compile val network))))
  ;;   :hints(("Goal" :in-theory (enable pair-keys svex-alist-compose svex-alist-reduce svex-acons))))
  (verify-guards neteval-ordering-compile)
  )


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

;; (verify 
;;  (implies (and (consp (neteval-ordering-fix x))
;;                (consp (neteval-ordering-fix compose))
;;                (equal (caar (neteval-ordering-fix x))
;;                       (caar (neteval-ordering-fix compose))))
;;           (equal (neteval-ordering-eval compose network env)
;;                  (neteval-ordering-eval x network (append (neteval-ordering-eval subst network env) env)))))


;; (verify 
;;  (implies (And (neteval-sigordering-case compose-sigord :segment)
;;                (neteval-sigordering-case x-sigord :segment)
;;                (equal (neteval-sigordering-segment->width compose-sigord)
;;                       (neteval-sigordering-segment->width x-sigord)))
;;           (equal (neteval-sigordering-eval compose-sigord function network env)
;;                  (neteval-sigordering-eval x-sigord function network (append (neteval-ordering-eval subst network env) env)))))




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
         
         (new-sigord (neteval-sigordering-compose-aux sigordering subst)))
      (cons (cons signal new-sigord)
            (neteval-ordering-compose-aux (cdr x) subst))))

  (define neteval-sigordering-compose-aux ((x neteval-sigordering-p)
                                       (subst neteval-ordering-p))
    :measure (neteval-sigordering-count x)
    :returns (composed neteval-sigordering-p)
    (neteval-sigordering-case x
      :segment (make-neteval-sigordering-segment
                :width x.width
                :ord (append (neteval-ordering-compose-aux x.ord subst) (neteval-ordering-fix subst))
                :rest (neteval-sigordering-compose-aux x.rest subst))
      :remainder (make-neteval-sigordering-remainder
                  :ord (append (neteval-ordering-compose-aux x.ord subst) (neteval-ordering-fix subst)))))
  ///

  (defthm-neteval-ordering-compile-flag
    (defthm eval-of-neteval-ordering-compose-aux
      (equal (neteval-ordering-eval (neteval-ordering-compose-aux x subst) network env)
             (neteval-ordering-eval x network (append (neteval-ordering-eval subst network env) env)))
      :hints ('(:expand ((neteval-ordering-compose-aux x subst)
                         (:free (env) (neteval-ordering-eval x network env))
                         (:free (a b) (neteval-ordering-eval (cons a b) network env)))))
      :flag neteval-ordering-compile)
    (defthm eval-of-neteval-sigordering-compose-aux
      (equal (neteval-sigordering-eval (neteval-sigordering-compose-aux x subst) function network env)
             (neteval-sigordering-eval x function network
                                       (append (neteval-ordering-eval subst network env) env)))
      :hints ('(:expand ((neteval-sigordering-compose-aux x subst)
                         (:free (function env) (neteval-sigordering-eval x function network env))
                         (:free (function width ord rest)
                          (neteval-sigordering-eval
                           (neteval-sigordering-segment width ord rest)
                           function network env))
                         (:free (function ord) (neteval-sigordering-eval
                                       (neteval-sigordering-remainder ord)
                                       function network env)))))
      :flag neteval-sigordering-compile))


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
                          
  
(defcong svex-eval-equiv svex-eval-equiv (neteval-sigordering-compile x function network) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(local (defthm svex-rsh-of-0
         (svex-eval-equiv (svex-rsh 0 x) x)
         :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))


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
         (subst-look (hons-assoc-equal signal (neteval-ordering-fix subst)))
         ;; We want to produce an ordering (compose) that reflects an ordering (x)
         ;; applied to the network resulting from applying an ordering (subst) to
         ;; the original network (network).
         
         ;; For each binding of a signal to an ordering in X, first, if the signal
         ;; isn't bound in subst then it won't be bound in the composed network so
         ;; we skip it.
         ((unless subst-look)
          (neteval-ordering-compose (cdr x) subst))
         
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

         

         (new-sigord (neteval-sigordering-compose sigordering (cdr subst-look) subst)))
      (cons (cons signal new-sigord)
            (neteval-ordering-compose (cdr x) subst))))

  (define neteval-sigordering-compose ((x neteval-sigordering-p)
                                       (subst-sigord neteval-sigordering-p)
                                       (subst neteval-ordering-p))
    :measure (two-nats-measure (neteval-sigordering-count x)
                               (neteval-sigordering-count subst-sigord))
    :returns (composed neteval-sigordering-p)
    (b* (((mv width x-ord x-rest subst-ord subst-rest)
          (neteval-sigordering-case x
            :segment (neteval-sigordering-case subst-sigord
                       :segment (cond ((< x.width subst-sigord.width)
                                       (mv x.width x.ord x.rest
                                           subst-sigord.ord
                                           (make-neteval-sigordering-segment
                                            :width (- subst-sigord.width x.width)
                                            :ord subst-sigord.ord
                                            :rest subst-sigord.rest)))
                                      ((eql x.width subst-sigord.width)
                                       (mv x.width x.ord x.rest subst-sigord.ord subst-sigord.rest))
                                      (t ;; (< subst-sigord.width x.width)
                                       (mv subst-sigord.width
                                           x.ord
                                           (make-neteval-sigordering-segment
                                            :width (- x.width subst-sigord.width)
                                            :ord x.ord
                                            :rest x.rest)
                                           subst-sigord.ord
                                           subst-sigord.rest)))
                       :remainder (mv x.width x.ord x.rest subst-sigord.ord subst-sigord))
            :remainder (neteval-sigordering-case subst-sigord
                         :segment (mv subst-sigord.width x.ord x subst-sigord.ord subst-sigord.rest)
                         :remainder (mv nil x.ord x subst-sigord.ord subst-sigord))))
         ;; width is nil means we're done.
         (new-ord1 (neteval-ordering-compose x-ord subst))
         (new-ord-full
          (append (neteval-ordering-compose-aux subst-ord new-ord1) new-ord1)))
      (if width
          (make-neteval-sigordering-segment
           :width width
           :ord new-ord-full
           :rest (neteval-sigordering-compose x-rest subst-rest subst))
        (make-neteval-sigordering-remainder :ord new-ord-full))))

  ///
  (local (defthm svex-rsh-of-neteval-sigordering-compile-when-remainder
           (implies (neteval-sigordering-case x :remainder)
                    (svex-eval-equiv
                     (svex-rsh n (neteval-sigordering-compile x function network))
                     (neteval-sigordering-compile x (svex-rsh n function) network)))
           :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)
                   :expand ((:free (function env) (neteval-sigordering-eval x function network env)))))))


  (local
   (defquant eval-of-neteval-sigordering-compose-cond (composed x subst-sigord subst network env)
     (forall func
             (equal (neteval-sigordering-eval composed func network env)
                    (neteval-sigordering-eval x
                                              (neteval-sigordering-compile subst-sigord func network)
                                              (neteval-ordering-compile subst network) env)))
     :rewrite :direct))

  (local (in-theory (e/d (eval-of-neteval-sigordering-compose-cond-necc)
                         (eval-of-neteval-sigordering-compose-cond))))


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
       (eval-of-neteval-sigordering-compose-cond
        composed x subst-sigord subst network env)
       :hints ((acl2::witness :ruleset (eval-of-neteval-sigordering-compose-cond-witnessing))
               
               (and stable-under-simplificationp
                    `(:expand ((neteval-sigordering-compose x subst-sigord subst) ;;,(Car (last clause))
                               (:free (function network) (neteval-sigordering-eval x function network env))
                               (:free (function network env)
                                (neteval-sigordering-eval subst-sigord function network env))
                               (:free (ord function network env)
                                (neteval-sigordering-eval
                                 (neteval-sigordering-remainder ord) function network env))
                               (:free (width ord rest function network env)
                                (neteval-sigordering-eval
                                 (neteval-sigordering-segment width ord rest) function network env))
                               (:free (ord function network env)
                                (neteval-sigordering-compile
                                 (neteval-sigordering-remainder ord) function network))
                               (:free (width ord rest function network env)
                                (neteval-sigordering-compile
                                 (neteval-sigordering-segment width ord rest) function network))
                               )))
               (and stable-under-simplificationp
                    `(:expand ((:free (function network)
                                (neteval-sigordering-compile subst-sigord function network)))))
               )
       :fn neteval-sigordering-compose)))

  (defret eval-of-neteval-ordering-compose
    (equal (neteval-ordering-eval composed network env)
           (neteval-ordering-eval x (neteval-ordering-compile subst network) env))
    :hints ('(:expand ((neteval-ordering-compose x subst)
                       (:free (network) (neteval-ordering-eval x network env))
                       (:free (a b) (neteval-ordering-eval (cons a b) network env)))))
    :fn neteval-ordering-compose)

  (defret eval-of-neteval-sigordering-compose
    (equal (neteval-sigordering-eval composed func network env)
           (neteval-sigordering-eval x
                                     (neteval-sigordering-compile subst-sigord func network)
                                     (neteval-ordering-compile subst network) env))
    :hints (("Goal" :use eval-of-neteval-sigordering-compose-lemma
             :in-theory (disable eval-of-neteval-sigordering-compose-lemma)))
    :fn neteval-sigordering-compose)

  (defret compile-of-neteval-ordering-compose
    (svex-alist-eval-equiv (neteval-ordering-compile composed network)
                           (neteval-ordering-compile x (neteval-ordering-compile subst network)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv)))
    :fn neteval-ordering-compose)

  (verify-guards neteval-sigordering-compose))




(define neteval-ordering-identity ((keys svarlist-p))
  :returns (ordering neteval-ordering-p)
  :prepwork ((local (defthm neteval-ordering-p-of-pair0keys
                      (implies (and (svarlist-p keys)
                                    (neteval-sigordering-p ord))
                               (neteval-ordering-p (pair-keys keys ord)))
                      :hints(("Goal" :in-theory (enable pair-keys)))))
             ;; (local (defthm hons-assoc-equal-of-pairlis$-repeat
             ;;          (equal (hons-assoc-equal key (pairlis$ keys (repeat (len keys) elt)))
             ;;                 (and (member-equal key keys)
             ;;                      (cons key elt)))
             ;;          :hints(("Goal" :in-theory (enable repeat pairlis$)))))
             ;; (local (defthm hons-assoc-equal-of-pairlis$-nil
             ;;          (equal (hons-assoc-equal key (pairlis$ keys nil))
             ;;                 (and (member-equal key keys)
             ;;                      (list key)))))
             ;; (local (defthm svex-env-boundp-of-pairlis$
             ;;          (implies (and (equal len (len keys))
             ;;                        (svarlist-p keys))
             ;;                   (iff (svex-env-boundp key (pairlis$ keys (repeat len elt)))
             ;;                        (member-equal (svar-fix key) keys)))
             ;;          :hints(("Goal" :in-theory (enable svex-env-boundp)))))
             ;; (local (defthm svex-env-lookup-of-pairlis$
             ;;          (implies (and (equal len (len keys))
             ;;                        (svarlist-p keys))
             ;;                   (equal (svex-env-lookup key (pairlis$ keys (repeat len elt)))
             ;;                          (if (member-equal (svar-fix key) keys)
             ;;                              (4vec-fix elt)
             ;;                            (4vec-x))))
             ;;          :hints(("Goal" :in-theory (enable svex-env-lookup)))))
             )
  (pair-keys (svarlist-fix keys) (neteval-sigordering-remainder nil))
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




