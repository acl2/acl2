; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
(include-book "svex")
(include-book "std/osets/top" :dir :system)
;; [Jared] BOZO fragile, previously included via fty, needed for some reason here
;; want to just include std/util/alist-keys but that doesn't work
(include-book "misc/hons-help" :dir :system)
(include-book "clause-processors/witness-cp" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (std::deflist svarlist-p (x)
         (svar-p x)
         :true-listp t
         :elementp-of-nil nil))

(local (defthm setp-singleton
         (setp (list x))
         :hints(("Goal" :in-theory (enable setp)))))

(defines svex-vars
  :verify-guards nil
  :flag-local nil

  (define svex-vars
    :parents (expressions)
    :short "Collect all of the variables from an @(see svex)."
    ((x svex-p "Expression to collect variables from."))
    :returns
    (vars "An <see topic='@(url acl2::std/osets)'>ordered set</see> of all
           variables in the @('x')."
          (and (svarlist-p vars)
               (setp vars)))
    :long "<p>We collect the set of variables for an @(see svex) by computing
the exact sets of variables for all of its subexpressions, and @(see union)ing
them together.  This is logically nice to reason about and is <i>sometimes</i>
practical to execute.</p>

<p>Although we @(see memoize) this function to take advantage of structure
sharing, constructing the exact set of variables for every subexpression
quickly becomes <b>very</b> memory intensive.  For better performance, it is
often better to use @(see svex-collect-vars) instead.</p>"
    :measure (svex-count x)
    (svex-case x
      :quote nil
      :var (list x.name)
      :call (svexlist-vars x.args)))

  (define svexlist-vars
    :parents (svex-vars)
    :short "Collect all of the variables from an @(see svexlist)."
    ((x svexlist-p "Expression list to collect variables from."))
    :returns
    (vars "An <see topic='@(url acl2::std/osets)'>ordered set</see> of all
           variables used in any expression in @('x')."
          (and (svarlist-p vars)
               (setp vars)))
    :long "<p>See @(see svex-vars).  This just @(see union)s together the @(see
svex-vars) of all of the expressions in @('x').</p>

<p>Like @(see svex-vars), this is logically nice but can be <b>very</b> memory
intensive.  It is often better to use @(see svexlist-collect-vars)
instead.</p>"

    :measure (svexlist-count x)
    (if (atom x)
        nil
      (union (svex-vars (car x))
             (svexlist-vars (cdr x)))))
  ///
  (local (defthm svarlist-p-impl-true-listp
           (implies (svarlist-p x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable svarlist-p)))))
  (verify-guards svex-vars)
  (memoize 'svex-vars)
  ///
  (deffixequiv-mutual svex-vars
    :hints (("Goal" :expand ((svexlist-fix x))))))


(defsection svex-vars-basics
  :parents (svex-vars)
  :short "Very basic rules about @(see svex-vars)"

  (local (in-theory (enable svex-vars svexlist-vars)))

  (defthm svex-vars-when-quote
    (implies (equal (svex-kind x) :quote)
             (equal (svex-vars x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svex-vars-when-var
    (implies (equal (svex-kind x) :var)
             (equal (svex-vars x) (list (svex-var->name x))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svex-vars-when-call
    (implies (equal (svex-kind x) :call)
             (equal (svex-vars x)
                    (svexlist-vars (svex-call->args x))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svex-vars-of-svex-quote
    (equal (svex-vars (svex-quote val))
           nil))

  (defthm svex-vars-of-svex-var
    (equal (svex-vars (svex-var name))
           (list (svar-fix name))))

  (defthm svex-vars-of-svex-call
    (equal (svex-vars (svex-call fn args))
           (svexlist-vars args))
    :hints (("goal" :expand ((svex-vars (svex-call fn args)))))))


(defsection svexlist-vars-basics
  :parents (svexlist-vars)
  :short "Basic theorems about @(see svexlist-vars)."

  (local (in-theory (enable svexlist-vars)))

  (defthm svexlist-vars-of-cons
    (set-equiv (svexlist-vars (cons a b))
               (append (svex-vars a)
                       (svexlist-vars b))))

  (defthm svexlist-vars-of-append
    (equal (svexlist-vars (append x y))
           (union (svexlist-vars x)
                  (svexlist-vars y))))

  "<h3>Set equiv congruence</h3>"

  (defthm svex-vars-subset-of-svexlist-vars-when-member
    (implies (member x y)
             (subsetp (svex-vars x) (svexlist-vars y))))

  (defthm svexlist-vars-of-subset
    (implies (subsetp x y)
             (subsetp (svexlist-vars x) (svexlist-vars y)))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defcong set-equiv equal (svexlist-vars x) 1
    :hints(("Goal" :in-theory (enable double-containment
                                      set::subset-to-subsetp)))))


(define svex-alist-vars
  :parents (svex-vars svex-alist)
  :short "Collect all of the variables from all the expressions in an @(see
          svex-alist)."
  ((x svex-alist-p "Binds variables (not collected!) to their expressions
                    (whose variables <i>are</i> collected)."))
  :returns
  (vars "An <see topic='@(url acl2::std/osets)'>ordered set</see> of all
         variables used in any of the expressions."
        (and (svarlist-p vars)
             (setp vars)))

  :long "<p>This function is based on @(see svex-vars); it is logically nice
to reason about but probably is not what you want to execute.  BOZO where is
the collect- version of this; recommend an alternative.</p>

<p>We collect the variables from all of the expressions that are bound in the
@(see svex-alist).  Note that this does <b>not</b> collect the keys of the
alist, even though they are variables.  It instead collects the variables from
the expressions that the keys are bound to.</p>"
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :verify-guards nil
  (if (atom x)
      nil
    (union (and (mbt (and (consp (car x)) (svar-p (caar x))))
                (svex-vars (cdar x)))
           (svex-alist-vars (cdr x))))
  ///
  (local (defthm svarlist-p-impl-true-listp
           (implies (svarlist-p x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable svarlist-p)))))

  (verify-guards svex-alist-vars)

  (deffixequiv svex-alist-vars
    :hints (("goal" :expand ((Svex-alist-fix x)))))

  (defthm svex-vars-of-svex-alist-lookup
    (subsetp-equal (svex-vars (svex-lookup k x))
                   (svex-alist-vars x))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-vars-of-svex-acons
    (equal (svex-alist-vars (svex-acons k v x))
           (union (svex-vars v)
                  (svex-alist-vars x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm svex-alist-vars-of-append
    (set-equiv (svex-alist-vars (append a b))
               (append (svex-alist-vars a)
                       (svex-alist-vars b))))

  (defthm vars-of-svex-alist-lookup
    (implies (not (member v (svex-alist-vars x)))
             (not (member v (svex-vars (cdr (hons-assoc-equal k (svex-alist-fix x)))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-fix
                                      hons-assoc-equal))))

  (defthm vars-of-fast-alist-fork
    (implies (and (not (member v (svex-alist-vars x)))
                  (not (member v (svex-alist-vars y))))
             (not (member v (svex-alist-vars (fast-alist-fork x y)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      fast-alist-fork)))))



(defines svex-collect-vars1
  :verify-guards nil
  :flag-local nil
  (define svex-collect-vars1 ((x svex-p) (seen) (vars svarlist-p))
    :parents (svex-collect-vars)
    :returns (mv seen1 (vars1 svarlist-p))
    :measure (svex-count x)
    (b* ((x (svex-fix x))
         (vars (svarlist-fix vars)))
      (svex-case x
        :quote (mv seen vars)
        :var (if (hons-get x seen)
                 (mv seen vars)
               (mv (hons-acons x t seen)
                   (cons x.name vars)))
        :call (if (hons-get x seen)
                  (mv seen vars)
                (b* ((seen (hons-acons x t seen)))
                  (svexlist-collect-vars1 x.args seen vars))))))
  (define svexlist-collect-vars1 ((x svexlist-p) (seen) (vars svarlist-p))
    :parents (svex-collect-vars)
    :returns (mv seen1 (vars1 svarlist-p))
    :measure (svexlist-count x)
    (if (atom x)
        (mv seen (svarlist-fix vars))
      (b* (((mv seen vars) (svex-collect-vars1 (car x) seen vars)))
        (svexlist-collect-vars1 (cdr x) seen vars))))
  ///
  (verify-guards svex-collect-vars1)
  (deffixequiv-mutual svex-collect-vars1))

(define svex-collect-vars ((x svex-p))
  :parents (svex-vars)
  :short "Usually faster alternative to @(see svex-vars)."
  :long "<p>We compute a list of variables which occur in the @(see svex)
@('x').  This list is similar to the set of variables returned by @(see
svex-vars), except that it is not necessarily ordered.  More formally:</p>

@(thm svex-collect-vars-correct)

<p>This function is usually more efficient than @(see svex-vars).  It walks
over the @(see svex), gathering variables into an accumulator and keeping track
of which subtrees have already been explored using a seen table.  This avoids
computing exact variable information for each subexpression.</p>

<p>The implementation of this function is ugly and you would not want to reason
about it; instead we typically prefer to reason about @(see svex-vars) and
appeal to @('svex-collect-vars-correct').</p>"
  :returns (vars svarlist-p)
  (b* (((mv seen vars) (svex-collect-vars1 x nil nil)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svex-collect-vars))

(define svexlist-collect-vars ((x svexlist-p))
  :returns (vars svarlist-p)
  :parents (svex-vars)
  :short "Usually faster alternative to @(see svexlist-vars)."
  :long "<p>See @(see svex-collect-vars).  This is just the extension of its
strategy to collect all variables that occur in an expression list.
Correctness is stated in terms of @(see svexlist-vars):</p>

@(thm svexlist-collect-vars-correct)"

  (b* (((mv seen vars) (svexlist-collect-vars1 x nil nil)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svexlist-collect-vars))




; -----------------------------------------------------------------------------
;
;                  Correctness of svex-collect-vars
;
; -----------------------------------------------------------------------------

;; Invariant: svex-collect-vars1 uses a preorder accumulator.  Working off the
;; template in centaur/aig/accumulate-nodes-vars.lisp, the invariant we need
;; is: when recurring on a node a, for every subnode x of a, if x is in the
;; seen list then every subnode of x is in the seen list.

;; we don't collect quotes because svex-collect-vars doesn't either

(defines svex-subnodes
  (define svex-subnodes ((x svex-p))
    :returns (subnodes svexlist-p)
    :measure (svex-count x)
    (svex-case x
      :var (list (svex-fix x))
      :quote nil
      :call (cons (svex-fix x) (svexlist-subnodes x.args))))
  (define svexlist-subnodes ((x svexlist-p))
    :returns (subnodes svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (append (svex-subnodes (car x))
              (svexlist-subnodes (cdr x)))))
  ///
  (deffixequiv-mutual svex-subnodes)


  (defthm-svex-subnodes-flag
    (defthm member-svex-subnodes-transitive
      (implies (and (member z (svex-subnodes y))
                    (member y (svex-subnodes x)))
               (member z (svex-subnodes x)))
      :flag svex-subnodes)
    (defthm member-svexlist-subnodes-transitive
      (implies (and (member z (svex-subnodes y))
                    (member y (svexlist-subnodes x)))
               (member z (svexlist-subnodes x)))
      :flag svexlist-subnodes))

  (defthm-svex-subnodes-flag
    (defthm nonmember-svex-subnodes-by-count
      (implies (< (svex-count x) (svex-count y))
               (not (member y (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm nonmember-svexlist-subnodes-by-count
      (implies (< (svexlist-count x) (svex-count y))
               (not (member y (svexlist-subnodes x))))
      :flag svexlist-subnodes))

  (defthm-svex-subnodes-flag
    (defthm member-var-of-svex-subnodes-transitive
      (implies (and (member v (svex-vars y))
                    (member y (svex-subnodes x)))
               (member v (svex-vars x)))
      :hints ('(:expand ((svex-vars x)
                         (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm member-var-of-svexlist-subnodes-transitive
      (implies (and (member v (svex-vars y))
                    (member y (svexlist-subnodes x)))
               (member v (svexlist-vars x)))
      :hints ('(:expand ((svexlist-vars x)
                         (svexlist-subnodes x))))
      :flag svexlist-subnodes))
  (in-theory (disable member-var-of-svex-subnodes-transitive
                      member-var-of-svexlist-subnodes-transitive))


  (defthm-svex-subnodes-flag
    (defthm member-svex-var-of-subnodes
      (iff (member (svex-var v) (svex-subnodes x))
           (member (svar-fix v) (svex-vars x)))
      :hints ('(:expand ((svex-vars x)
                         (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm member-svexlist-var-of-subnodes
      (iff (member (svex-var v) (svexlist-subnodes x))
           (member (svar-fix v) (svexlist-vars x)))
      :hints ('(:expand ((svexlist-vars x)
                         (svexlist-subnodes x))))
      :flag svexlist-subnodes))

  (defthm-svex-vars-flag
    (defthm svexlist-vars-of-svex-subnodes
      (equal (svexlist-vars (svex-subnodes x))
             (svex-vars x))
      :hints ('(:expand ((svex-subnodes x)
                         (svex-vars x)
                         (:free (a b) (svexlist-vars (cons a b))))))
      :flag svex-vars)
    (defthm svexlist-vars-of-svexlist-subnodes
      (equal (svexlist-vars (svexlist-subnodes x))
             (svexlist-vars x))
      :hints ('(:expand ((svexlist-subnodes x)
                         (svexlist-vars x))))
      :flag svexlist-vars)))

(local (in-theory (enable member-var-of-svex-subnodes-transitive
                          member-var-of-svexlist-subnodes-transitive)))


(local (defthmd member-alist-keys
         (iff (member k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))


(defsection svex-collect-vars1-seenlist-invariant

  (acl2::defquant svex-seenlist-invariant (x seen)
    (forall (y z)
            (implies (and (member y (svex-subnodes x))
                          (member y seen)
                          (not (member z seen)))
                     (not (member z (svex-subnodes y)))))
    :rewrite :direct)

  (acl2::defexample svex-seenlist-invariant-example
    :pattern (member z (svex-subnodes y))
    :templates (y z)
    :instance-rulename svex-seenlist-invariant-instancing)

  (acl2::defquant svexlist-seenlist-invariant (x seen)
    (forall (y z)
            (implies (and (member y (svexlist-subnodes x))
                          (member y seen)
                          (not (member z seen)))
                     (not (member z (svex-subnodes y)))))
    :rewrite :direct)

  (acl2::defexample svexlist-seenlist-invariant-example
    :pattern (member z (svex-subnodes y))
    :templates (y z)
    :instance-rulename svexlist-seenlist-invariant-instancing)

  (defthm svexlist-seenlist-invariant-of-call-args
    (implies (and (svex-seenlist-invariant x seen)
                  (equal (svex-kind x) :call))
             (svexlist-seenlist-invariant (svex-call->args x) seen))
    :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc)
             :expand ((svex-subnodes x)))
            (acl2::witness)))

  (defthm svex-seenlist-invariant-of-car
    (implies (and (svexlist-seenlist-invariant x seen)
                  (consp x))
             (svex-seenlist-invariant (car x) seen))
    :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc)
             :expand ((svexlist-subnodes x)))
            (acl2::witness)))

  (defthm svexlist-seenlist-invariant-of-cdr
    (implies (svexlist-seenlist-invariant x seen)
             (svexlist-seenlist-invariant (cdr x) seen))
    :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc)
             :cases ((consp x))
             :expand ((svexlist-subnodes x)))
            (acl2::witness)))

  (defthm svex-seenlist-invariant-initial
    (svex-seenlist-invariant x nil)
    :hints ((acl2::witness)))

  (defthm svexlist-seenlist-invariant-initial
    (svexlist-seenlist-invariant x nil)
    :hints ((acl2::witness)))


  (local (in-theory (disable set-equiv)))

  (local (defthm member-when-set-equiv-append
           (implies (set-equiv x (append y z))
                    (iff (member k x)
                         (or (member k y) (member k z))))))

  ;; (local (defthm append-cons-under-set-equiv
  ;;          (set-equiv (append (cons b a) c)
  ;;                     (append a (cons b c)))
  ;;          :hints((acl2::set-reasoning))))

  (local (acl2::defexample svex-seenlist-invariant-example-args
           :pattern (member z (svexlist-subnodes (svex-call->args y)))
           :templates ((svex-fix y) z)
           :instance-rulename svex-seenlist-invariant-instancing))


  (defthm svexlist-seenlist-invariant-of-descend
    (implies (and (svex-seenlist-invariant x (alist-keys seen))
                  (equal (svex-kind x) :call))
             (and (svexlist-seenlist-invariant (svex-call->args x)
                                               (alist-keys (cons (cons (svex-fix x) v) seen)))
                  (svexlist-seenlist-invariant (svex-call->args x)
                                               (cons (svex-fix x) (alist-keys seen)))))
    :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc)
             :expand ((:free (a b) (alist-keys (cons a b)))
                      (svex-subnodes x))
             :do-not-induct t)
            (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
            (acl2::Set-reasoning)
            (acl2::witness :ruleset svex-seenlist-invariant-example)
            ))

  (defthm-svex-collect-vars1-flag
    (defthm svex-collect-vars1-seenlist1
      (implies (svex-seenlist-invariant x (alist-keys seen))
               (set-equiv (alist-keys (mv-nth 0 (svex-collect-vars1 x seen vars)))
                          (append (svex-subnodes x) (alist-keys seen))))
      :hints ('(:expand ((svex-collect-vars1 x seen vars)
                         (svex-subnodes x))
                :in-theory (enable svex-seenlist-invariant-necc
                                   member-alist-keys))
              (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
              (acl2::Set-reasoning)
              (acl2::witness :ruleset svex-seenlist-invariant-example-args)
              )
      :flag svex-collect-vars1)
    (defthm svexlist-collect-vars1-seenlist1
      (implies (svexlist-seenlist-invariant x (alist-keys seen))
               (set-equiv (alist-keys (mv-nth 0 (svexlist-collect-vars1 x seen vars)))
                          (append (svexlist-subnodes x) (alist-keys seen))))
      :hints ('(:expand ((svexlist-collect-vars1 x seen vars)
                         (svexlist-subnodes x))
                :in-theory (enable svexlist-seenlist-invariant-necc))
              (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
              ;; (acl2::witness :ruleset svexlist-seenlist-invariant-example)
              )
      :flag svexlist-collect-vars1))


  (defthm svex-collect-vars1-preserves-seenlist-invar
    (implies (and (svex-seenlist-invariant y (alist-keys seen))
                  (svex-seenlist-invariant x (alist-keys seen)))
             (svex-seenlist-invariant
              y (alist-keys
                 (mv-nth 0 (svex-collect-vars1 x seen vars)))))
    :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc))
            (acl2::witness :ruleset svex-seenlist-invariant-witnessing)))

  (defthm svex-collect-vars1-preserves-seenlist-list-invar
    (implies (and (svexlist-seenlist-invariant y (alist-keys seen))
                  (svex-seenlist-invariant x (alist-keys seen)))
             (svexlist-seenlist-invariant
              y (alist-keys
                 (mv-nth 0 (svex-collect-vars1 x seen vars)))))
    :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc))
            (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)))

  (defthm svexlist-collect-vars1-preserves-seenlist-invar
    (implies (and (svex-seenlist-invariant y (alist-keys seen))
                  (svexlist-seenlist-invariant x (alist-keys seen)))
             (svex-seenlist-invariant
              y (alist-keys
                 (mv-nth 0 (svexlist-collect-vars1 x seen vars)))))
    :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc))
            (acl2::witness :ruleset svex-seenlist-invariant-witnessing)))

  (defthm svexlist-collect-vars1-preserves-seenlist-list-invar
    (implies (and (svexlist-seenlist-invariant y (alist-keys seen))
                  (svexlist-seenlist-invariant x (alist-keys seen)))
             (svexlist-seenlist-invariant
              y (alist-keys
                 (mv-nth 0 (svexlist-collect-vars1 x seen vars)))))
    :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc))
            (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)))


  (local (Defthm set-difference-of-append
           (equal (set-difference$ (append x y) z)
                  (append (set-difference$ x z)
                          (set-difference$ y z)))
           :hints(("Goal" :in-theory (enable set-difference$ append)))))

  ;; (local (defthm rewrite-svex-collect-vars-under-set-equiv
  ;;          (implies (and (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars)) y)
  ;;                        (syntaxp (not (case-match y
  ;;                                        (('mv-nth ''1 ('svex-collect-vars1 . &)) t)
  ;;                                        (& nil)))))
  ;;                   (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars)) y))))

  (defthm rewrite-member-of-append-under-set-equiv
    (implies (set-equiv x (append y z))
             (iff (member k x)
                  (or (member k y)
                      (member k z)))))




  (local (defthm set-diff-of-nil
           (equal (set-difference$ nil x)
                  nil)
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (defthm intersection-of-append
    (equal (intersection$ (append a b) c)
           (append (intersection$ a c)
                   (intersection$ b c)))
    :hints(("Goal" :in-theory (enable intersection$))))

  (defthm intersection-of-append-2
    (set-equiv (intersection$ c (append a b))
               (append (intersection$ c a)
                       (intersection$ c b)))
    :hints ((acl2::set-reasoning)))


  (defthm member-svexlist-vars-of-intersection
    (implies (not (member v (svexlist-vars x)))
             (not (member v (svexlist-vars (intersection$ x y)))))
    :hints(("Goal" :in-theory (enable intersection$ svexlist-vars))))

  (defthm member-svexlist-vars-of-intersection-2
    (implies (not (member v (svexlist-vars y)))
             (not (member v (svexlist-vars (intersection$ x y)))))
    :hints(("Goal" :in-theory (enable intersection$ svexlist-vars))))


  (define member-svexlist-vars-witness (k x)
    :verify-guards nil
    (if (atom x)
        nil
      (if (member k (svex-vars (car x)))
          (car x)
        (member-svexlist-vars-witness k (cdr x))))
    ///
    (defthm member-svexlist-vars-witness-when-member-svexlist-vars
      (implies (member k (svexlist-vars x))
               (let ((elt (member-svexlist-vars-witness k x)))
                 (and (member elt x)
                      (member k (svex-vars elt)))))
      :hints(("Goal" :in-theory (enable svexlist-vars)))))

  (defthm svex-var-member-of-intersection-when-member-both
    (implies (and (member (svex-var k) x)
                  (member (svex-var k) y)
                  (svar-p k))
             (member k (svexlist-vars (intersection$ x y))))
    :hints(("Goal" :in-theory (enable intersection$ member))))

  (defthm svar-p-when-member-svex-vars
    (implies (member k (svex-vars x))
             (svar-p k))
    :rule-classes :forward-chaining)

  (defthm svar-p-when-member-svexlist-vars
    (implies (member k (svexlist-vars x))
             (svar-p k))
    :rule-classes :forward-chaining)

  (defthm member-vars-of-svex-intersection-under-svex-invar
    (implies (and (svex-seenlist-invariant x seen)
                  ;; (member k (svex-vars x))
                  )
             (iff (member k (svexlist-vars (intersection$ (svex-subnodes x) seen)))
                  (and (member k (svex-vars x))
                       (member (svex-var k) seen))))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance svex-seenlist-invariant-necc
                          (y (member-svexlist-vars-witness
                              k (intersection$ (svex-subnodes x) seen)))
                          (z (svex-var k)))
                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
                          (x (intersection$ (svex-subnodes x) seen))))
                   :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
                   :do-not-induct t)))
    :otf-flg t)

  (defthm member-vars-of-svexlist-intersection-under-svexlist-invar
    (implies (svexlist-seenlist-invariant x seen)
             (iff (member k (svexlist-vars (intersection$ (svexlist-subnodes x) seen)))
                  (and (member k (svexlist-vars x))
                       (member (svex-var k) seen))))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance svexlist-seenlist-invariant-necc
                          (y (member-svexlist-vars-witness
                              k (intersection$ (svexlist-subnodes x) seen)))
                          (z (svex-var k)))
                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
                          (x (intersection$ (svexlist-subnodes x) seen))))
                   :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
                   :do-not-induct t)))
    :otf-flg t)


  ;; (defthm member-vars-of-svex-intersection-under-svexlist-invar
  ;;   (implies (and (svexlist-seenlist-invariant x seen)
  ;;                 (member y (svexlist-subnodes x))
  ;;                 (member k (svex-vars y)))
  ;;            (iff (member k (svexlist-vars (intersection$ (svex-subnodes y) seen)))
  ;;                 (member (svex-var k) seen)))
  ;;   :hints (("goal" :use ((:instance svexlist-seenlist-invariant-necc
  ;;                          (y (member-svexlist-vars-witness
  ;;                              k (intersection$ (svex-subnodes y) seen)))
  ;;                          (z (svex-var k)))
  ;;                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
  ;;                          (x (intersection$ (svex-subnodes y) seen))))
  ;;            :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
  ;;            :do-not-induct t))
  ;;   :otf-flg t)




  ;; (defthm member-vars-of-svexlist-intersection-under-svexlist-invar
  ;;   (implies (and (svexlist-seenlist-invariant x seen)
  ;;                 (member k (svexlist-vars x)))
  ;;            (iff (member k (svexlist-vars (intersection$ (svexlist-subnodes x) seen)))
  ;;                 (member (svex-var k) seen)))
  ;;   :hints (("goal" :use ((:instance svexlist-seenlist-invariant-necc
  ;;                          (y (member-svexlist-vars-witness
  ;;                              k (intersection$ (svexlist-subnodes x) seen)))
  ;;                          (z (svex-var k)))
  ;;                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
  ;;                          (x (intersection$ (svexlist-subnodes x) seen))))
  ;;            :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
  ;;            :do-not-induct t))
  ;;   :otf-flg t)

  (defthm svexlist-seenlist-invariant-of-svex-subnodes
    (svexlist-seenlist-invariant x (svex-subnodes y))
    :hints ((acl2::witness)))

  (defthm svex-seenlist-invariant-of-svex-subnodes
    (svex-seenlist-invariant x (svex-subnodes y))
    :hints ((acl2::witness)))

  (defthm svexlist-seenlist-invariant-of-svexlist-subnodes
    (svexlist-seenlist-invariant x (svex-subnodes y))
    :hints ((acl2::witness)))

  (defthm svex-seenlist-invariant-of-svexlist-subnodes
    (svex-seenlist-invariant x (svex-subnodes y))
    :hints ((acl2::witness)))

  (defthm member-self-of-svex-subnodes
    (implies (member k (svex-vars x))
             (member (svex-fix x) (svex-subnodes x)))
    :hints (("goal" :expand ((svex-subnodes x)))))

  (defthm seen-invariant-implies-vars-subset
    (implies (and (svex-seenlist-invariant x seen)
                  (member (svex-fix x) seen)
                  (member k (svex-vars x)))
             (member (svex-var k) seen))
    :hints (("goal" :use ((:instance svex-seenlist-invariant-necc
                           (y (svex-fix x)) (z (svex-var k)))))))


  (local (defthmd hons-assoc-equal-iff-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member k (alist-keys x)))
           :hints(("Goal" :in-theory (enable member-alist-keys)))))

  (defthm-svex-collect-vars1-flag
    (defthm svex-collect-vars1-result
      (implies (svex-seenlist-invariant x (alist-keys seen))
               (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars))
                          (append (set-difference$ (svex-vars x)
                                                   (svexlist-vars
                                                    (intersection-equal
                                                     (svex-subnodes x)
                                                     (alist-keys seen))))
                                  (svarlist-fix vars))))
      :hints ('(:expand ((svex-collect-vars1 x seen vars)
                         (svex-vars x)
                         (:free (a b) (alist-keys (cons a b))))
                :in-theory (enable hons-assoc-equal-iff-member-alist-keys))
              (acl2::witness :ruleset (acl2::set-equiv-witnessing
                                       acl2::subsetp-witnessing)))
      :flag svex-collect-vars1)
    (defthm svexlist-collect-vars1-result
      (implies (svexlist-seenlist-invariant x (alist-keys seen))
               (set-equiv (mv-nth 1 (svexlist-collect-vars1 x seen vars))
                          (append (set-difference$ (svexlist-vars x)
                                                   (svexlist-vars
                                                    (intersection-equal
                                                     (svexlist-subnodes x)
                                                     (alist-keys seen))))
                                  (svarlist-fix vars))))
      :hints ('(:expand ((svexlist-collect-vars1 x seen vars)
                         (svexlist-vars x)
                         (svexlist-subnodes x)))
              (acl2::witness :ruleset (acl2::set-equiv-witnessing
                                       acl2::subsetp-witnessing))
              ;; (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
              )
      :flag svexlist-collect-vars1)))




(defsection seenlist-invariant

  (acl2::defquant svex-collect-seen-invariant (seen)
    ;; Seenlist and varlist invariants for all X
    (forall (y z)
            (implies (and (member y seen)
                          (not (member z seen)))
                     (not (member z (svex-subnodes y)))))
    :rewrite :direct)


  ;; (acl2::defquant svex-seenlist-invariant (x seen)
  ;;   (forall (y z)
  ;;           (implies (and (member y (svex-subnodes x))
  ;;                         (member y seen)
  ;;                         (not (member z seen)))
  ;;                    (not (member z (svex-subnodes y)))))
  ;;   :rewrite :direct)

  ;; (acl2::defquant svex-varlist-invariant (a seen vars)
  ;;   (forall (v x)
  ;;           (implies (and (member x (svex-subnodes a))
  ;;                         (member x seen)
  ;;                         (not (member v (svarlist-fix vars))))
  ;;                    (not (member v (svex-vars x)))))
  ;;   :rewrite :direct)



  (local (in-theory (enable svex-collect-seen-invariant-necc)))

  (local
   (progn
     (defthm svex-seenlist-invariant-when-collect-seen-invariant
       (implies (svex-collect-seen-invariant seen)
                (svex-seenlist-invariant x seen))
       :hints ((acl2::witness)))

     (defthm svexlist-seenlist-invariant-when-collect-seen-invariant
       (implies (svex-collect-seen-invariant seen)
                (svexlist-seenlist-invariant x seen))
       :hints ((acl2::witness)))))

  (defthm svex-collect-seen-invariant-of-empty
    (svex-collect-seen-invariant nil)
    :hints(("Goal" :in-theory (enable svex-collect-seen-invariant))))


  (defthm svex-collect-vars1-preserves-svex-collect-seen-invariant
    (b* (((mv seen1 ?vars1) (svex-collect-vars1 x seen vars)))
      (implies (svex-collect-seen-invariant (alist-keys seen))
               (svex-collect-seen-invariant (alist-keys seen1))))
    :hints ((acl2::witness)))

  (defthm svexlist-collect-vars1-preserves-svex-collect-seen-invariant
    (b* (((mv seen1 ?vars1) (svexlist-collect-vars1 x seen vars)))
      (implies (svex-collect-seen-invariant (alist-keys seen))
               (svex-collect-seen-invariant (alist-keys seen1))))
    :hints ((acl2::witness)))


  (defthm svex-collect-vars1-seenlist
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (alist-keys (mv-nth 0 (svex-collect-vars1 x seen vars)))
                        (append (svex-subnodes x) (alist-keys seen)))))


  (defthm svexlist-collect-vars1-seenlist
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (alist-keys (mv-nth 0 (svexlist-collect-vars1 x seen vars)))
                        (append (svexlist-subnodes x) (alist-keys seen)))))


  (local
   (defthm member-svexlist-vars-when-member-svex-var
     (implies (and (member (svex-var k) x)
                   (svar-p k))
              (member k (svexlist-vars x)))
     :hints(("Goal" :induct (len x)
             :expand ((svexlist-vars x))))))

  (local (defthm svex-collect-seen-invariant-implies-member-svex-var
           (implies (svex-collect-seen-invariant seen)
                    (iff (member (svex-var k) seen)
                         (member (svar-fix k) (svexlist-vars seen))))
           :hints (("goal" :use ((:instance svex-collect-seen-invariant-necc
                                  (y (member-svexlist-vars-witness
                                      (svar-fix k) seen))
                                  (z (svex-var k))))
                    :in-theory (disable svex-collect-seen-invariant-necc)))))



  (local
   (defthm svex-collect-correct-lemma
     (IMPLIES
      (SVEX-COLLECT-SEEN-INVARIANT (ALIST-KEYS SEEN))
      (SET-EQUIV
       (SET-DIFFERENCE-EQUAL
        (SVEX-VARS X)
        (SVEXLIST-VARS (INTERSECTION-EQUAL (SVEX-SUBNODES X)
                                           (ALIST-KEYS SEEN))))
       (SET-DIFFERENCE-EQUAL (SVEX-VARS X)
                             (SVEXLIST-VARS (ALIST-KEYS SEEN)))))
     :hints ((acl2::set-reasoning)
             (and stable-under-simplificationp
                  '(:use ((:instance svex-seenlist-invariant-when-collect-seen-invariant
                           (seen (alist-keys seen))))
                    :in-theory (disable svex-seenlist-invariant-when-collect-seen-invariant))))
     :otf-flg t))

  (local
   (defthm svexlist-collect-correct-lemma
     (IMPLIES
      (SVEX-COLLECT-SEEN-INVARIANT (ALIST-KEYS SEEN))
      (SET-EQUIV
       (SET-DIFFERENCE-EQUAL
        (SVEXlist-VARS X)
        (SVEXLIST-VARS (INTERSECTION-EQUAL (SVEXlist-SUBNODES X)
                                           (ALIST-KEYS SEEN))))
       (SET-DIFFERENCE-EQUAL (SVEXlist-VARS X)
                             (SVEXLIST-VARS (ALIST-KEYS SEEN)))))
     :hints ((acl2::set-reasoning)
             (and stable-under-simplificationp
                  '(:use ((:instance svexlist-seenlist-invariant-when-collect-seen-invariant
                           (seen (alist-keys seen))))
                    :in-theory (disable svexlist-seenlist-invariant-when-collect-seen-invariant))))
     :otf-flg t))


  (defthm svex-collect-vars1-correct
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars))
                        (append (set-difference$ (svex-vars x)
                                                 (svexlist-vars (alist-keys seen)))
                                (svarlist-fix vars)))))

  (defthm svexlist-collect-vars1-correct
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (mv-nth 1 (svexlist-collect-vars1 x seen vars))
                        (append (set-difference$ (svexlist-vars x)
                                                 (svexlist-vars (alist-keys seen)))
                                (svarlist-fix vars))))))


(defsection svex-collect-vars-correct
  :extension (svex-collect-vars)

  (defthm svex-collect-vars-correct
    (set-equiv (svex-collect-vars x)
               (svex-vars x))
    :hints(("Goal" :in-theory (enable svex-collect-vars))
           (acl2::set-reasoning))))

(defsection svexlist-collect-vars-correct
  :extension (svexlist-collect-vars)

  (defthm svexlist-collect-vars-correct
    (set-equiv (svexlist-collect-vars x)
               (svexlist-vars x))
    :hints(("Goal" :in-theory (enable svexlist-collect-vars))
           (acl2::set-reasoning))))



(defines svex-opcount1
  :verify-guards nil
  (define svex-opcount1 ((x svex-p) (seen) (count natp))
    :returns (mv seen1 (count1 natp :rule-classes :type-prescription))
    :measure (svex-count x)
    (b* ((x (svex-fix x))
         (count (lnfix count)))
      (svex-case x
        :quote (mv seen count)
        :var (mv seen count)
        :call (if (hons-get x seen)
                  (mv seen count)
                (b* ((seen (hons-acons x t seen)))
                  (svexlist-opcount1 x.args seen (1+ count)))))))
  (define svexlist-opcount1 ((x svexlist-p) (seen) (count natp))
    :returns (mv seen1 (count1 natp :rule-classes :type-prescription))
    :measure (svexlist-count x)
    (if (atom x)
        (mv seen (lnfix count))
      (b* (((mv seen count) (svex-opcount1 (car x) seen count)))
        (svexlist-opcount1 (cdr x) seen count))))
  ///
  (verify-guards svex-opcount1)
  (deffixequiv-mutual svex-opcount1
    :hints ((and stable-under-simplificationp
                 (equal (car id) '(0 1))
                 (b* ((lit (car (last clause))))
                   `(:expand (,(cadr lit)
                              ,(caddr lit))))))))


(define svex-opcount ((x svex-p))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((mv seen vars) (svex-opcount1 x nil 0)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svex-opcount))

(define svexlist-opcount ((x svexlist-p))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((mv seen vars) (svexlist-opcount1 x nil 0)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svexlist-opcount))


(defines svex-opcount1-limit
  :verify-guards nil
  (define svex-opcount1-limit ((x svex-p) (seen) (count natp) (limit natp))
    :returns (mv seen1 (count1 natp :rule-classes :type-prescription))
    :measure (svex-count x)
    (b* ((x (svex-fix x))
         (count (lnfix count))
         ((when (>= count (lnfix limit)))
          (mv seen count)))
      (svex-case x
        :quote (mv seen count)
        :var (mv seen count)
        :call (if (hons-get x seen)
                  (mv seen count)
                (b* ((seen (hons-acons x t seen)))
                  (svexlist-opcount1-limit x.args seen (1+ count) limit))))))
  (define svexlist-opcount1-limit ((x svexlist-p) (seen) (count natp) (limit natp))
    :returns (mv seen1 (count1 natp :rule-classes :type-prescription))
    :measure (svexlist-count x)
    (if (atom x)
        (mv seen (lnfix count))
      (b* (((mv seen count) (svex-opcount1-limit (car x) seen count limit)))
        (svexlist-opcount1-limit (cdr x) seen count limit))))
  ///
  (verify-guards svex-opcount1-limit)
  (deffixequiv-mutual svex-opcount1-limit
    ;; :hints ((and stable-under-simplificationp
    ;;              (equal (car id) '(0 1))
    ;;              (b* ((lit (car (last clause))))
    ;;                `(:expand (,(cadr lit)
    ;;                           ,(caddr lit))))))
    ))


(define svex-opcount-limit ((x svex-p) (limit natp))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((mv seen count) (svex-opcount1-limit x nil 0 limit)))
    (fast-alist-free seen)
    count)
  ///
  (deffixequiv svex-opcount-limit))

(define svexlist-opcount-limit ((x svexlist-p) (limit natp))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((mv seen count) (svexlist-opcount1-limit x nil 0 limit)))
    (fast-alist-free seen)
    count)
  ///
  (deffixequiv svexlist-opcount-limit))




(define constraintlist-vars ((x constraintlist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svex-vars (constraint->cond (car x)))
            (constraintlist-vars (cdr x))))
  ///
  (defthm constraintlist-vars-of-append
    (equal (constraintlist-vars (append a b))
           (append (constraintlist-vars a)
                   (constraintlist-vars b)))))






(define svarlist-non-override-test-p ((x svarlist-p))
  (if (atom x)
      t
    (and (b* (((svar x1) (car x)))
           (not x1.override-test))
         (svarlist-non-override-test-p (cdr x)))))

(define svarlist-non-override-p ((x svarlist-p))
  (if (atom x)
      t
    (and (b* (((svar x1) (car x)))
           (and (not x1.override-test)
                (not x1.override-val)))
         (svarlist-non-override-p (cdr x))))
  ///
  (defthm svarlist-non-override-p-of-append
    (equal (svarlist-non-override-p (append x y))
           (and (svarlist-non-override-p x)
                (svarlist-non-override-p y)))))

(define svarlist->override-tests ((x svarlist-p))
  :returns (new-x svarlist-p)
  (if (atom x)
      nil
    (cons (change-svar (Car x) :override-test t)
          (svarlist->override-tests (cdr x)))))
