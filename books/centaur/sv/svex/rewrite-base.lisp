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
(include-book "vars")
(include-book "nrev")
(include-book "std/util/defprojection" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (defthm setp-singleton
         (setp (list x))
         :hints(("Goal" :in-theory (enable setp)))))

(defxdoc rewriting
  :parents (expressions)
  :short "We implement a lightweight, mostly unconditional rewriter for
simplifying @(see svex) expressions in provably sound ways.  This is typically
used to reduce expressions before processing them with bit-blasting or other
reasoning tools."

  :long "<p>Our rewriter is only <i>mostly</i> unconditional, because there is
an additional context-determined bitmask that can allow additional
simplifications. For example, suppose we are in a context where only the bottom
4 bits are relevant (the bitmask is 15, say) and we see the expression:</p>

@({ (concat 5 a b) })

<p>This can then be simplified to just @('a'); see @(see 4vmask).</p>

<h5>Interface</h5>
<ul>
<li>@(see svex-rewrite), @(see svexlist-rewrite) recursively rewrites an
expression or list of expressions under a given mask alist</li>
<li>@(see svexlist-rewrite-top), @(see svex-alist-rewrite-top) computes a mask
alist for a list or alist of expressions and rewrites it under that mask
alist</li>
<li>@(see svexlist-rewrite-fixpoint), @(see svex-alist-rewrite-fixpoint)
repeatedly applies @('-rewrite-top') until it reaches a fixpoint (or an
iteration limit runs out).</li>
</ul>")

(local (xdoc::set-default-parents rewriting))

(defines svex-subst
  :verify-guards nil
  (define svex-subst
    :short "Basic substitution operation for @(see svex)es.  Not memoized."
    ((pat svex-p       "Pattern to substitute into.")
     (al  svex-alist-p "Substitution: binds variables to replacement @(see svex)es.
                        Need not be a fast alist."))
    :returns (x svex-p "Rewritten pattern with variables replaced by their bindings.")
    :measure (svex-count pat)
    :long "<p>Any variables that aren't bound get replaced by all Xes.</p>

<p>We expect to use this function when applying rewrite rules, which typically
have only a few variables, so we don't use a fast alist here.</p>

<p>See also @(see svex-subst-memo) for a memoized version.</p>"
    (svex-case pat
      :var (or (svex-lookup pat.name al)
               (svex-quote (4vec-x)))
      :quote (svex-fix pat)
      :call (svex-call pat.fn (svexlist-subst pat.args al))))
  (define svexlist-subst ((pat svexlist-p) (al svex-alist-p))
    :returns (x svexlist-p)
    :measure (svexlist-count pat)
    (if (atom pat)
        nil
      (cons (svex-subst (car pat) al)
            (svexlist-subst (cdr pat) al))))
  ///
  (verify-guards svex-subst)

  (deffixequiv-mutual svex-subst
    :hints (("goal" :expand ((svexlist-fix pat)))))

  (defthm-svex-subst-flag
    (defthm svex-eval-of-svex-subst
      (equal (svex-eval (svex-subst pat al) env)
             (svex-eval pat (svex-alist-eval al env)))
      :hints ('(:expand ((svex-subst pat al)
                         (:free (al) (svex-eval pat al))
                         (svex-eval ''(-1 . 0) env)
                         (:free (f a) (svex-eval (svex-call f a) env)))))
      :flag svex-subst)
    (defthm svexlist-eval-of-svexlist-subst
      (equal (svexlist-eval (svexlist-subst pat al) env)
             (svexlist-eval pat (svex-alist-eval al env)))
      :hints ('(:expand ((svexlist-subst pat al)
                         (:free (al) (svexlist-eval pat al))
                         (:free (a b) (svexlist-eval (cons a b) env)))))
      :flag svexlist-subst))

  (defthm-svex-subst-flag
    (defthm vars-of-svex-subst
      (implies (not (member v (svex-alist-vars al)))
               (not (member v (svex-vars (svex-subst pat al)))))
      :flag svex-subst
      :hints ('(:expand ((svex-subst pat al)))))
    (defthm vars-of-svexlist-subst
      (implies (not (member v (svex-alist-vars al)))
               (not (member v (svexlist-vars (svexlist-subst pat al)))))
      :flag svexlist-subst
      :hints ('(:expand ((svexlist-subst pat al)))))))


(defines svex-subst-memo
  :verify-guards nil
  (define svex-subst-memo
    :parents (svex-subst)
    :short "Substitution for @(see svex)es, identical to @(see svex-subst),
except that we memoize the results."
    ((pat svex-p)
     (al  svex-alist-p "Need not be fast; we still use slow lookups."))
    :returns (x (equal x (svex-subst pat al))
                :hints ((and stable-under-simplificationp
                             '(:expand ((svex-subst pat al))))))
    :measure (svex-count pat)
    (svex-case pat
      :var (or (svex-lookup pat.name al)
               (svex-quote (4vec-x)))
      :quote (svex-fix pat)
      :call (svex-call pat.fn (svexlist-subst-memo pat.args al))))
  (define svexlist-subst-memo ((pat svexlist-p) (al svex-alist-p))
    :returns (x (equal x (svexlist-subst pat al))
                :hints ((and stable-under-simplificationp
                             '(:expand ((svexlist-subst pat al))))))
    :measure (svexlist-count pat)
    (if (atom pat)
        nil
      (cons (svex-subst-memo (car pat) al)
            (svexlist-subst-memo (cdr pat) al))))
  ///
  (verify-guards svex-subst-memo)
  (memoize 'svex-subst-memo :condition '(eq (svex-kind pat) :call)))




(defines svex-unify
  :verify-guards nil
  (define svex-unify
    :short "One-way unification for @(see svex)es."
    ((pat svex-p       "Pattern to match.")
     (x   svex-p       "Target expression to match against.")
     (al  svex-alist-p "Accumulator for bindings so far.  Slow alist."))
    :returns
    (mv (successp booleanp :rule-classes :type-prescription
                  :hints ('(:expand ((svex-unify pat x al)))))
        (al1 svex-alist-p "Updated alist."))
    :long "<p>We expect to use this function when applying rewrite rules, which
typically have only a few variables, so we don't use a fast alist for the
accumulator.</p>"
    :measure (svex-count pat)
    (b* ((x  (svex-fix x))
         (al (svex-alist-fix al)))
      (svex-case pat
        :var (b* ((look (svex-lookup pat.name al))
                  ((when look) (mv (equal look x) al)))
               (mv t (svex-acons pat.name x al)))
        :quote (if (and (eq (svex-kind x) :quote)
                        (equal (svex-quote->val x) pat.val))
                   (mv t al)
                 (mv nil al))
        :call (if (and (eq (svex-kind x) :call)
                       (eq (svex-call->fn x) pat.fn))
                  (svexlist-unify pat.args (svex-call->args x) al)
                (mv nil al)))))

  (define svexlist-unify ((pat svexlist-p)
                          (x   svexlist-p)
                          (al  svex-alist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (al1 svex-alist-p))
    :measure (svexlist-count pat)
    (b* ((al (mbe :logic (svex-alist-fix al) :exec al))
         ((when (atom pat)) (mv (atom x) al))
         ((when (atom x)) (mv nil al))
         ((mv ok al) (svex-unify (car pat) (car x) al))
         ((unless ok) (mv nil al)))
      (svexlist-unify (cdr pat) (cdr x) al)))
  ///
  (verify-guards svex-unify)

  (deffixequiv-mutual svex-unify
    :hints (("goal" :expand ((svexlist-fix pat)
                             (svexlist-fix x)))))

  (defthm-svex-unify-flag
    (defthm svex-unify-lookup-preserved
      (implies (svex-lookup v al)
               (equal (svex-lookup v (mv-nth 1 (svex-unify pat x al)))
                      (svex-lookup v al)))
      :hints ('(:expand ((svex-unify pat x al))))
      :flag svex-unify)
    (defthm svexlist-unify-lookup-preserved
      (implies (svex-lookup v al)
               (equal (svex-lookup v (mv-nth 1 (svexlist-unify pat x al)))
                      (svex-lookup v al)))
      :flag svexlist-unify))

  ;; (defthm svex-alist-keys-of-svex-unify
  ;;   (subsetp-equal (svex-alist-keys al)
  ;;                  (svex-alist-keys (mv-nth 1 (svex-unify pat x al))))
  ;;   :hints ((acl2::set-reasoning)))

  ;; (defthm svex-alist-keys-of-svexlist-unify
  ;;   (subsetp-equal (svex-alist-keys al)
  ;;                  (svex-alist-keys (mv-nth 1 (svexlist-unify pat x al))))
  ;;   :hints ((acl2::set-reasoning)))

  ;; (defthm svex-vars-bound-of-svex-unify-preserved
  ;;   (implies (subsetp vars (svex-alist-keys al))
  ;;            (subsetp vars
  ;;                     (svex-alist-keys
  ;;                      (mv-nth 1 (svex-unify pat y al)))))
  ;;   :hints ((acl2::set-reasoning)))

  (defthm svex-vars-bound-of-svexlist-unify-preserved
    (implies (subsetp vars (svex-alist-keys al))
             (subsetp vars
                      (svex-alist-keys (mv-nth 1 (svexlist-unify pat y al)))))
    :hints ((acl2::set-reasoning)))

  ;; (defthm-svex-vars-flag
  ;;   (defthm svex-vars-bound-of-svex-unify-preserved
  ;;     (b* (((mv ?ok al1) (svex-unify pat y al)))
  ;;       (implies (subsetp (svex-vars x) (alist-keys al))
  ;;                (svex-vars-bound x al1)))
  ;;     :hints ('(:expand ((:free (al) (svex-vars-bound x al)))))
  ;;     :flag svex-vars-bound)
  ;;   (defthm svexlist-vars-bound-of-svex-unify-preserved
  ;;     (b* (((mv ?ok al1) (svex-unify pat y al)))
  ;;       (implies (svexlist-vars-bound x al)
  ;;                (svexlist-vars-bound x al1)))
  ;;     :hints ('(:expand ((:free (al) (svexlist-vars-bound x al)))))
  ;;     :flag svexlist-vars-bound))

  ;; (defthm-svex-vars-bound-flag
  ;;   (defthm svex-vars-bound-of-svexlist-unify-preserved
  ;;     (b* (((mv ?ok al1) (svexlist-unify pat y al)))
  ;;       (implies (svex-vars-bound x al)
  ;;                (svex-vars-bound x al1)))
  ;;     :hints ('(:expand ((:free (al) (svex-vars-bound x al)))))
  ;;     :flag svex-vars-bound)
  ;;   (defthm svexlist-vars-bound-of-svexlist-unify-preserved
  ;;     (b* (((mv ?ok al1) (svexlist-unify pat y al)))
  ;;       (implies (svexlist-vars-bound x al)
  ;;                (svexlist-vars-bound x al1)))
  ;;     :hints ('(:expand ((:free (al) (svexlist-vars-bound x al)))))
  ;;     :flag svexlist-vars-bound))

  (defthm-svex-unify-flag
    (defthm svex-vars-bound-of-svex-unify
      (b* (((mv ok al1) (svex-unify pat x al)))
        (implies ok
                 (subsetp (svex-vars pat) (svex-alist-keys al1))))
      :hints ('(:expand ((svex-vars pat)
                         (svex-unify pat x al))))
      :flag svex-unify)
    (defthm svexlist-vars-bound-of-svexlist-unify
      (b* (((mv ok al1) (svexlist-unify pat x al)))
        (implies ok
                 (subsetp (svexlist-vars pat) (svex-alist-keys al1))))
      :hints ('(:expand ((svexlist-vars pat)
                         (svexlist-unify pat x al))))
      :flag svexlist-unify))

  (defthm-svex-vars-flag
    (defthm svex-unify-preserves-svex-eval-when-vars-bound
      (b* (((mv ?ok al1) (svex-unify pat y al)))
        (implies (subsetp (svex-vars x) (svex-alist-keys al))
                 (equal (svex-eval x (svex-alist-eval al1 env))
                        (svex-eval x (svex-alist-eval al env)))))
      :hints ('(:expand ((svex-vars x)
                         (:free (al) (svex-eval x al)))))
      :flag svex-vars)
    (defthm svex-unify-preserves-svexlist-eval-when-vars-bound
      (b* (((mv ?ok al1) (svex-unify pat y al)))
        (implies (subsetp (svexlist-vars x) (svex-alist-keys al))
                 (equal (svexlist-eval x (svex-alist-eval al1 env))
                        (svexlist-eval x (svex-alist-eval al env)))))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (al) (svexlist-eval x al)))))
      :flag svexlist-vars))

  (defthm-svex-vars-flag
    (defthm svexlist-unify-preserves-svex-eval-when-vars-bound
      (b* (((mv ?ok al1) (svexlist-unify pat y al)))
        (implies (subsetp (svex-vars x) (svex-alist-keys al))
                 (equal (svex-eval x (svex-alist-eval al1 env))
                        (svex-eval x (svex-alist-eval al env)))))
      :hints ('(:expand ((svex-vars x)
                         (:free (al) (svex-eval x al)))))
      :flag svex-vars)
    (defthm svexlist-unify-preserves-svexlist-eval-when-vars-bound
      (b* (((mv ?ok al1) (svexlist-unify pat y al)))
        (implies (subsetp (svexlist-vars x) (svex-alist-keys al))
                 (equal (svexlist-eval x (svex-alist-eval al1 env))
                        (svexlist-eval x (svex-alist-eval al env)))))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (al) (svexlist-eval x al)))))
      :flag svexlist-vars))

  (defthm-svex-unify-flag
    (defthm svex-unify-correct
      (b* (((mv ok al1) (svex-unify pat x al)))
        (implies ok
                 (equal (svex-eval x env)
                        (svex-eval pat (svex-alist-eval al1 env)))))
      :hints ('(:expand ((svex-unify pat x al)
                         (svex-eval x env)
                         (:free (env) (svex-eval pat env)))))
      :flag svex-unify)
    (defthm svexlist-unify-correct
      (b* (((mv ok al1) (svexlist-unify pat x al)))
        (implies ok
                 (equal (svexlist-eval x env)
                        (svexlist-eval pat (svex-alist-eval al1 env)))))
      :hints ('(:expand ((svexlist-unify pat x al)
                         (:free (env) (svexlist-eval pat env))
                         (svexlist-eval x env))))
      :flag svexlist-unify))

  (defthm svex-lookup-in-svexlist-unify
    (b* (((mv ok al1) (svexlist-unify pat x al)))
      (implies (and ok
                    (member (svar-fix k) (svexlist-vars pat)))
               (svex-lookup k al1)))
    :hints (("goal" :use svexlist-vars-bound-of-svexlist-unify
             :in-theory (disable svexlist-vars-bound-of-svexlist-unify))
            (acl2::set-reasoning)))

  (defthm svex-lookup-in-svex-unify
    (b* (((mv ok al1) (svex-unify pat x al)))
      (implies (and ok
                    (member (svar-fix k) (svex-vars pat)))
               (svex-lookup k al1)))
    :hints (("goal" :use svex-vars-bound-of-svex-unify
             :in-theory (disable svex-vars-bound-of-svex-unify))
            (acl2::set-reasoning)))

  (defthm-svex-unify-flag
    (defthm svex-unify-subst-no-new-vars
      (b* (((mv ?ok al1) (svex-unify pat x al)))
        (subsetp (svex-alist-vars al1)
                 (union-equal (svex-vars x)
                              (svex-alist-vars al))))
      :hints ('(:expand ((svex-unify pat x al)
                         (svex-vars x))))
      :flag svex-unify)
    (defthm svexlist-unify-subst-no-new-vars
      (b* (((mv ?ok al1) (svexlist-unify pat x al)))
        (subsetp (svex-alist-vars al1)
                 (union-equal (svexlist-vars x)
                              (svex-alist-vars al))))
      :hints ('(:expand ((svexlist-unify pat x al)
                         (svexlist-vars x))))
      :flag svexlist-unify))

  (defthm svex-unify-subst-no-new-vars-base
    (b* (((mv ?ok al1) (svex-unify pat x nil)))
      (subsetp (svex-alist-vars al1) (svex-vars x)))
    :hints (("goal" :use ((:instance svex-unify-subst-no-new-vars
                           (al nil)))
             :in-theory (disable svex-unify-subst-no-new-vars))))

  (defthm svexlist-unify-subst-no-new-vars-base
    (b* (((mv ?ok al1) (svexlist-unify pat x nil)))
      (subsetp (svex-alist-vars al1) (svexlist-vars x)))
    :hints (("goal" :use ((:instance svexlist-unify-subst-no-new-vars
                           (al nil)))
             :in-theory (disable svexlist-unify-subst-no-new-vars))))

  ;; (defthm svex-unify-ok-rewrite
  ;;   (implies (acl2::rewriting-negative-literal
  ;;             `(mv-nth '0 (svex-unify ,pat ,x ,al)))
  ;;            (equal (mv-nth 0 (svex-unify pat x al))
  ;;                   (and (hide (mv-nth 0 (svex-unify pat x al)))
  ;;                        (svex-eval-equiv
  ;;                         (svex-subst pat (mv-nth 1 (svex-unify pat x al)))
  ;;                         x))))
  ;;   :hints (("goal" :expand ((:free (x) (hide x))))
  ;;           (and stable-under-simplificationp '(:expand nil))
  ;;           (acl2::witness)))

  ;; (defthm svexlist-unify-ok-rewrite
  ;;   (implies (acl2::rewriting-negative-literal
  ;;             `(mv-nth '0 (svexlist-unify ,pat ,x ,al)))
  ;;            (equal (mv-nth 0 (svexlist-unify pat x al))
  ;;                   (and (hide (mv-nth 0 (svexlist-unify pat x al)))
  ;;                        (svexlist-eval-equiv
  ;;                         (svexlist-subst pat (mv-nth 1 (svexlist-unify pat x al)))
  ;;                         x))))
  ;;   :hints (("goal" :expand ((:free (x) (hide x))))
  ;;           (and stable-under-simplificationp '(:expand nil))
  ;;           (acl2::witness)))

  ;; (in-theory (disable svex-unify-correct
  ;;                     svexlist-unify-correct))

  (defthm-svex-unify-flag
    (defthm svex-count-of-unify
      (b* (((mv ok alist) (svex-unify pat x al)))
        (implies (and ok
                      (svex-lookup v alist)
                      (not (svex-lookup v al)))
                 (and (<= (svex-count (svex-lookup v alist))
                          (svex-count x))
                      (implies (svex-case pat :call)
                               (< (svex-count (svex-lookup v alist))
                                  (svex-count x))))))
      :rule-classes :linear
      :flag svex-unify)
    (defthm svex-count-of-unify-list
      (b* (((mv ok alist) (svexlist-unify pat x al)))
        (implies (and ok
                      (svex-lookup v alist)
                      (not (svex-lookup v al)))
                 (and (<= (svex-count (svex-lookup v alist))
                          (svexlist-count x))
                      (implies (svex-case pat :call)
                               (< (svex-count (svex-lookup v alist))
                                  (svexlist-count x))))))
      :rule-classes :linear
      :flag svexlist-unify)))



(defsection rewriter-tracing
  :parents (rewriting)
  :short "Optional support for tracing the application of rewrite rules."

  :long "<p>@(call svex-rewrite-trace) is an attachable function (see @(see
defattach)) for tracing or profiling svex rewrite rules.</p>

<p>This is an advanced feature for SV hackers and is probably only useful if
you are trying to extend or debug the svex rewriters.  You may need to
separately load the following book to use these attachments. (It is not
included by default to avoid trust tags.)</p>

@({
    (include-book \"centaur/sv/svex/rewrite-trace\" :dir :system)
})"

  (encapsulate
    (((svex-rewrite-trace * * * * * *) => *
      :guard t :formals (rule mask args localp rhs subst)))
    (local (defun svex-rewrite-trace (rule mask args localp rhs subst)
             (declare (xargs :guard t))
             (list rule mask args localp rhs subst))))

  (defun svex-rewrite-trace-default (rule mask args localp rhs subst)
    (declare (xargs :guard t)
             (ignorable rule mask args localp rhs subst))
    nil)

  (defattach svex-rewrite-trace svex-rewrite-trace-default))




(defines svex-compose
  :flag-local nil
  :parents (svex-composition)
  :short "Compose an svex with a substitution alist.  Variables not in the
substitution are left in place."
  (define svex-compose ((x svex-p) (a svex-alist-p))
    :verify-guards nil
    :measure (svex-count x)
    :returns (xa svex-p "x composed with a, unbound variables preserved")
    (svex-case x
      :var (or (svex-fastlookup x.name a)
               (mbe :logic (svex-fix x) :exec x))
      :quote (mbe :logic (svex-fix x) :exec x)
      :call (svex-call x.fn
                       (svexlist-compose x.args a))))
  (define svexlist-compose ((x svexlist-p) (a svex-alist-p))
    :measure (svexlist-count x)
    :returns (xa svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose (car x) a)
            (svexlist-compose (cdr x) a))))
  ///
  (verify-guards svex-compose)
  (fty::deffixequiv-mutual svex-compose
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm len-of-svexlist-compose
    (equal (len (svexlist-compose x a))
           (len x)))

  (local (defthm svex-env-lookup-of-append-svex-alist-eval-not-present
           (equal (svex-env-lookup v (append (svex-alist-eval a e) env))
                  (if (svex-lookup v a)
                      (svex-eval (svex-lookup v a) e)
                    (svex-env-lookup v env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup
                                             svex-env-fix
                                             svex-alist-fix
                                             svex-lookup)))))

  (defthm-svex-compose-flag
    (defthm svex-eval-of-svex-compose
      (equal (svex-eval (svex-compose x a) env)
             (svex-eval x (append (svex-alist-eval a env) env)))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :flag svex-compose)
    (defthm svexlist-eval-of-svexlist-compose
      (equal (svexlist-eval (svexlist-compose x a) env)
             (svexlist-eval x (append (svex-alist-eval a env) env)))
      :flag svexlist-compose))

  (defthm-svex-compose-flag
    (defthm vars-of-svex-compose
      (implies (and (not (member v (svex-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svex-vars (svex-compose x a)))))
      :flag svex-compose)
    (defthm vars-of-svexlist-compose
      (implies (and (not (member v (svexlist-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svexlist-vars (svexlist-compose x a)))))
      :hints('(:in-theory (enable svexlist-vars)))
      :flag svexlist-compose))

  (defthm-svex-compose-flag
    ;; Note: The order of the disjuncts is important because sometimes you can
    ;; prove one given not the other but not vice versa.
    (defthm vars-of-svex-compose-strong
      (implies (and (not (member v (svex-alist-vars a)))
                    (or (member v (svex-alist-keys a))
                        (not (member v (svex-vars x)))))
               (not (member v (svex-vars (svex-compose x a)))))
      :flag svex-compose)
    (defthm vars-of-svexlist-compose-strong
      (implies (and (not (member v (svex-alist-vars a)))
                    (or (member v (svex-alist-keys a))
                        (not (member v (svexlist-vars x)))))
               (not (member v (svexlist-vars (svexlist-compose x a)))))
      :hints('(:in-theory (enable svexlist-vars)))
      :flag svexlist-compose))

  (in-theory (disable vars-of-svex-compose-strong
                      vars-of-svexlist-compose-strong))

  (memoize 'svex-compose :condition '(eq (svex-kind x) :call)))



(defines svex-replace-var
  :flag-local nil
  :parents (svex-composition)
  :short "Replace occurrences of a variable within an svex with an svex."
  (define svex-replace-var ((x svex-p) (var svar-p) (repl svex-p))
    :verify-guards nil
    :measure (svex-count x)
    :returns (xa (equal xa (svex-compose x (list (cons (svar-fix var) repl))))
                 :hints ('(:expand ((:free (a) (svex-compose x a)))
                           :in-theory (enable svex-lookup))))
    (svex-case x
      :var (if (svar-equiv x.name var)
               (svex-fix repl)
             (svex-fix x))
      :quote (svex-fix x)
      :call (svex-call x.fn
                       (svexlist-replace-var x.args var repl))))
  (define svexlist-replace-var ((x svexlist-p) (var svar-p) (repl svex-p))
    :measure (svexlist-count x)
    :returns (xa (equal xa (svexlist-compose x (list (cons (svar-fix var) repl))))
                 :hints ('(:expand ((:free (a) (svexlist-compose x a))))))
    (if (atom x)
        nil
      (cons (svex-replace-var (car x) var repl)
            (svexlist-replace-var (cdr x) var repl))))
  ///
  (verify-guards svexlist-replace-var)
  ;; (memoize 'svex-replace-var :condition '(svex-case x :call))
  )

(define svex-alist-compose-nrev ((x svex-alist-p)
                                 (a svex-alist-p)
                                 (nrev))
  :hooks nil
  (if (atom x)
      (acl2::nrev-fix nrev)
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (b* ((nrev (acl2::nrev-push (cons (caar x) (svex-compose (cdar x) a)) nrev)))
          (svex-alist-compose-nrev (cdr x) a nrev))
      (svex-alist-compose-nrev (cdr x) a nrev))))

(define svex-alist-compose ((x svex-alist-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (xx svex-alist-p)
  :verify-guards nil
  (if (atom x)
      nil
    (mbe :logic
         (if (mbt (and (consp (car x)) (svar-p (caar x))))
             (svex-acons (caar x) (svex-compose (cdar x) a)
                         (svex-alist-compose (cdr x) a))
           (svex-alist-compose (cdr x) a))
         :exec
         (acl2::with-local-nrev
           (svex-alist-compose-nrev x a acl2::nrev))))
  ///
  (local (defthm svex-alist-compose-nrev-elim
           (equal (svex-alist-compose-nrev x a nrev)
                  (append nrev (svex-alist-compose x a)))
           :hints(("Goal" :in-theory (enable svex-alist-compose-nrev
                                             svex-acons)))))
  (verify-guards svex-alist-compose)

  (fty::deffixequiv svex-alist-compose
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (defthm svex-alist-eval-of-svex-compose
    (equal (svex-alist-eval (svex-alist-compose x subst) env)
           (svex-alist-eval x (append (svex-alist-eval subst env) env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-acons
                                      svex-alist-compose
                                      svex-env-acons))))

  (defthm vars-of-svex-alist-compose
      (implies (and (not (member v (svex-alist-vars x)))
                    (not (member v (svex-alist-vars a))))
               (not (member v (svex-alist-vars (svex-alist-compose x a)))))
      :hints(("goal" :in-theory (enable svex-alist-vars))))

  (local (defthm svex-compose-under-iff
           (svex-compose x a)
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-COMPOSE.XA
                    :in-theory (disable RETURN-TYPE-OF-SVEX-COMPOSE.XA)))))

  (local (defthm svex-fix-under-iff
           (svex-fix x)
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-FIX.NEW-X
                    :in-theory (disable RETURN-TYPE-OF-SVEX-FIX.NEW-X)))))

  (defthm svex-lookup-of-svex-alist-compose
    (iff (svex-lookup v (svex-alist-compose x a))
         (svex-lookup v x))
    :hints(("Goal" :in-theory (e/d (svex-lookup svex-alist-fix svex-acons)
                                   (svex-alist-p))))))


(define constraintlist-compose ((x constraintlist-p)
                                (a svex-alist-p))
  :returns (new-x constraintlist-p)
  (if (atom x)
      nil
    (cons (change-constraint (car x)
                             :cond (svex-compose (constraint->cond (car x)) a))
          (constraintlist-compose (cdr x) a)))
  ///
  (defret vars-of-constraintlist-compose
    (implies (and (not (member v (constraintlist-vars x)))
                  (not (member v (svex-alist-vars a))))
             (not (member v (constraintlist-vars new-x))))
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))


(defprojection 4veclist-quote ((x 4veclist-p))
  :returns (svexes svexlist-p)
  (svex-quote x)
  ///
  (defret vars-of-4veclist-quote
    (equal (svexlist-vars svexes) nil)
    :hints(("Goal" :in-theory (enable svexlist-vars)))))

