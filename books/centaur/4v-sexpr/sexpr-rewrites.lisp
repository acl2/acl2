; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "centaur/aig/base" :dir :system) ;; BOZO for alphorder-sort
(include-book "sexpr-advanced")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "sexpr-vars-1pass")
(local (in-theory (disable sets::double-containment)))


(defxdoc sexpr-rewriting :parents (4v-sexprs))
(defxdoc sexpr-rewriting-internals :parents (sexpr-rewriting))
(defsection sexpr-rewrite-ground
  :parents (sexpr-rewriting-internals)
  :short "Checks whether the given s-expression's arguments are all constants,
and if so, rewrites it to a constant by evaluating it under the empty
environment."

  ;; Suppose (fn arg1 arg2) is a ground term.  We rewrite from the inside out,
  ;; and any ground terms are turned into (t), (f), (x), (z), so after rewriting
  ;; arg1 and arg2 we now have, say, (fn (t) (z)).

  (defun sexpr-ground-args-p (args)
    (declare (xargs :guard t))
    (or (atom args)
        (and (let ((arg (car args)))
               (if (atom arg)
                   (eq arg nil)
                 (atom (cdr arg))))
             (sexpr-ground-args-p (cdr args)))))

  (defun sexpr-rewrite-ground (x)
    (declare (xargs :guard t))
    (if (and (consp x) (sexpr-ground-args-p (cdr x)))
        (hist (4v-sexpr-eval x nil))
      x))

  (defthmd sexpr-eval-of-list-4vp
    (implies (4vp x)
             (equal (4v-sexpr-eval (list x) env) x)))

  (defthm sexpr-eval-list-norm-env-when-ground-args-p
    (implies (and (syntaxp (not (equal env ''nil)))
                  (sexpr-ground-args-p x))
             (equal (4v-sexpr-eval-list x env)
                    (4v-sexpr-eval-list x nil)))
    :hints (("goal" :in-theory (e/d* () ((:ruleset 4v-op-defs))))))

  (defthmd sexpr-eval-norm-env-when-ground-args-p
    (implies (and (syntaxp (not (equal env ''nil)))
                  (consp x)
                  (sexpr-ground-args-p (cdr x)))
             (equal (4v-sexpr-eval x env)
                    (4v-sexpr-eval x nil)))
    :hints (("goal" :in-theory (e/d* () ((:ruleset 4v-op-defs))))))

  (defthm 4vp-4v-sexpr-eval
    (4vp (4v-sexpr-eval x env))
    :hints (("goal" :use 4v-fix-4v-sexpr-eval
             :in-theory (disable 4vp 4v-fix-4v-sexpr-eval))))

  (defthm sexpr-rewrite-ground-correct
    (4v-sexpr-equiv (sexpr-rewrite-ground x)
                    x)
    :hints (("goal" ; :expand ((:free (x) (4v-sexpr-eval x env)))
             :in-theory (e/d** ((:rules-of-class
                                 :executable-counterpart :here)
                                sexpr-eval-norm-env-when-ground-args-p
                                sexpr-rewrite-ground
                                sexpr-ground-args-p
                                nth hons
                                4vp-4v-sexpr-eval
                                sexpr-eval-of-list-4vp
                                sexpr-eval-norm-env-when-ground-args-p
                                minimal-theory)))
            (witness :ruleset 4v-sexpr-equiv-witnessing)))

  (defthm 4v-sexpr-vars-sexpr-rewrite-ground
    (implies (not (member-equal k (4v-sexpr-vars x)))
             (not (member-equal k (4v-sexpr-vars (sexpr-rewrite-ground x))))))

  (in-theory (disable sexpr-rewrite-ground)))



(defsection sexpr-unify
  :parents (sexpr-rewriting-internals)
  :short "Unifies an S-expression with a pattern and returns the resulting
substitution as an alist binding variables to subterms."

  (mutual-recursion
   (defun sexpr-unify (pat term alist)
     (declare (xargs :guard t))
     (if (atom pat)
         (if pat
             ;; Using hons-assoc-equal rather than hons-get here because each
             ;; rewrite rule only has a handful of variables -- presumably not
             ;; worth hashing
             (let ((look (hons-assoc-equal pat alist)))
               (if look
                   (if (hqual term (cdr look))
                       (mv t alist)
                     (mv nil alist))
                 (mv t (cons (cons pat term) alist))))
           (mv (eq term nil) alist))
       (if (and (consp term)
                (equal (car pat) (car term)))
           (sexpr-unify-list (cdr pat) (cdr term) alist)
         (mv nil alist))))
   (defun sexpr-unify-list (pat term alist)
     (declare (xargs :guard t))
     (if (atom pat)
         (mv (and (equal pat nil)
                  (equal term nil)) alist)
       (if (consp term)
           (b* (((mv ok alist) (sexpr-unify (car pat) (car term) alist))
                ((unless ok) (mv nil alist)))
             (sexpr-unify-list (cdr pat) (cdr term) alist))
         (mv nil alist)))))


  (mutual-recursion
   (defun sexpr-unify-ind (pat term alist)
     (declare (xargs :guard t))
     (if (atom pat)
         (if pat
             (let ((look (hons-assoc-equal pat alist)))
               (if look
                   (if (hqual term (cdr look))
                       (mv t alist)
                     (mv nil alist))
                 (mv t (cons (cons pat term) alist))))
           (mv (eq term nil) alist))
       (if (and (consp term)
                (equal (car pat) (car term)))
           (sexpr-unify-list-ind (cdr pat) (cdr term) alist)
         (mv nil alist))))
   (defun sexpr-unify-list-ind (pat term alist)
     (declare (xargs :guard t))
     (if (atom pat)
         (mv (and (equal pat nil)
                  (equal term nil)) alist)
       (if (consp term)
           (b* (((mv & &) (sexpr-unify-ind (car pat) (car term) alist))
                ((mv & alist) (sexpr-unify (car pat) (car term) alist)))
             (sexpr-unify-list-ind (cdr pat) (cdr term) alist))
         (mv nil alist)))))

  (flag::make-flag sexpr-unify-flag sexpr-unify-ind
                   :flag-mapping ((sexpr-unify-ind . sexpr-unify)
                                  (sexpr-unify-list-ind . sexpr-unify-list)))

  ;; SEXPR-UNIFY preserves bindings that already exist in alist
  (defthm-sexpr-unify-flag
    (defthm sexpr-unify-hons-assoc-equal-prev
      (mv-let (ok alist1)
        (sexpr-unify pat term alist)
        (declare (ignore ok))
        (implies (hons-assoc-equal x alist)
                 (equal (hons-assoc-equal x alist1)
                        (hons-assoc-equal x alist))))
      :flag sexpr-unify)
    (defthm sexpr-unify-list-hons-assoc-equal-prev
      (mv-let (ok alist1)
        (sexpr-unify-list pat term alist)
        (declare (ignore ok))
        (implies (hons-assoc-equal x alist)
                 (equal (hons-assoc-equal x alist1)
                        (hons-assoc-equal x alist))))
      :flag sexpr-unify-list)
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  ;; SEXPR-UNIFY produces an alist that binds all variables in pat
  (defthm-sexpr-unify-flag
    (defthm 4v-sexpr-vars-assoc-sexpr-unify
      (mv-let (ok alist)
        (sexpr-unify pat term alist)
        (implies (and ok
                      (member-equal v (4v-sexpr-vars pat)))
                 (hons-assoc-equal v alist)))
      :flag sexpr-unify)

    (defthm 4v-sexpr-vars-list-assoc-sexpr-unify-list
      (mv-let (ok alist)
        (sexpr-unify-list pat term alist)
        (implies (and ok
                      (member-equal v (4v-sexpr-vars-list pat)))
                 (hons-assoc-equal v alist)))
      :flag sexpr-unify-list)
    :hints(("Goal" :in-theory (enable hons-assoc-equal)
            :expand ((sexpr-unify pat term alist)
                     (sexpr-unify-list pat term alist)))))


  ;; If a term's variables are all bound in alist, then composing it with that
  ;; alist gives the same result as with the result of unification
  (defthm-4v-sexpr-flag
    (defthm sexpr-unify-4v-sexpr-compose-tail-vars
      (mv-let (ok alist1)
        (sexpr-unify pat term alist)
        (declare (ignore ok))
        (implies (subsetp-equal (4v-sexpr-vars x) (alist-keys alist))
                 (equal (4v-sexpr-compose x alist1)
                        (4v-sexpr-compose x alist))))
      :flag sexpr)

    (defthm sexpr-unify-4v-sexpr-compose-list-tail-vars
      (mv-let (ok alist1)
        (sexpr-unify pat term alist)
        (declare (ignore ok))
        (implies (subsetp-equal (4v-sexpr-vars-list x) (alist-keys alist))
                 (equal (4v-sexpr-compose-list x alist1)
                        (4v-sexpr-compose-list x alist))))
      :flag sexpr-list)
    :hints(("Goal" :in-theory (enable hons-assoc-equal subsetp-equal))))

  ;; Same for a list of sexprs
  (defthm-4v-sexpr-flag
    (defthm sexpr-unify-list-4v-sexpr-compose-tail-vars
      (mv-let (ok alist1)
        (sexpr-unify-list pat term alist)
        (declare (ignore ok))
        (implies (subsetp-equal (4v-sexpr-vars x) (alist-keys alist))
                 (equal (4v-sexpr-compose x alist1)
                        (4v-sexpr-compose x alist))))
      :flag sexpr)

    (defthm sexpr-unify-list-4v-sexpr-compose-list-tail-vars
      (mv-let (ok alist1)
        (sexpr-unify-list pat term alist)
        (declare (ignore ok))
        (implies (subsetp-equal (4v-sexpr-vars-list x) (alist-keys alist))
                 (equal (4v-sexpr-compose-list x alist1)
                        (4v-sexpr-compose-list x alist))))
      :flag sexpr-list)
    :hints(("Goal" :in-theory (enable hons-assoc-equal subsetp-equal))))


  (defthm sexpr-unify-vars-subset-of-keys
    (mv-let (ok alist1)
      (sexpr-unify pat term alist)
      (implies ok
               (subsetp-equal (4v-sexpr-vars pat)
                              (alist-keys alist1))))
    :hints((set-reasoning)))

  (defthm sexpr-unify-list-vars-subset-of-keys
    (mv-let (ok alist1)
      (sexpr-unify-list pat term alist)
      (implies ok
               (subsetp-equal (4v-sexpr-vars-list pat)
                              (alist-keys alist1))))
    :hints((set-reasoning)))


  ;; Main correctness theorem of sexpr-unify: Sexpr-composing the pattern with
  ;; the unification alist yields the original term.
  (defthm-sexpr-unify-flag
    (defthm sexpr-unify-4v-sexpr-compose
      (mv-let (ok alist)
        (sexpr-unify pat term alist)
        (implies ok
                 (equal (4v-sexpr-compose pat alist)
                        term)))
      :flag sexpr-unify)

    (defthm sexpr-unify-list-4v-sexpr-compose-list
      (mv-let (ok alist)
        (sexpr-unify-list pat term alist)
        (implies ok
                 (equal (4v-sexpr-compose-list pat alist)
                        term)))
      :flag sexpr-unify-list)
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  ;; The variables in the unification alist are a subset of the ones in the term.
  (defthm-sexpr-unify-flag
    (defthm sexpr-unify-alist-vars
      (implies (and (not (member-equal x (4v-sexpr-vars term)))
                    (not (member-equal x (4v-sexpr-vars-list (alist-vals alist)))))
               (not (member-equal
                     x (4v-sexpr-vars-list
                        (alist-vals (mv-nth 1 (sexpr-unify pat term alist)))))))
      :flag sexpr-unify)

    (defthm sexpr-unify-list-alist-vars
      (implies (and (not (member-equal x (4v-sexpr-vars-list term)))
                    (not (member-equal x (4v-sexpr-vars-list (alist-vals alist)))))
               (not (member-equal
                     x (4v-sexpr-vars-list
                        (alist-vals (mv-nth 1 (sexpr-unify-list pat term alist)))))))
      :flag sexpr-unify-list)))


(defsection 4v-sexpr-compose-nofal
  :parents (sexpr-rewriting-internals)
  :short "Identical to 4v-sexpr-compose, but not memoized and does not use fast
alist lookups."
  :long "Used for rewriting because the terms and alists involved are small.
This is called on the RHS of a rewrite rule, which is a small term in common
usage; with an alist that may have large terms in its range, but only has a few
variables bound.  Therefore, it is appropriate to forego memoization and fast
alist lookups, since the overhead will outweigh the benefit."
  ;; Special version of 4v-sexpr-compose used for rewriting.  Because the RHSes of
  ;; the rewrite rules are small and the alists have few variables, we don't
  ;; memoize and we don't use fast alists.
  (mutual-recursion
   (defun 4v-sexpr-compose-nofal (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-assoc-equal x al)))
                  (and look (cdr look))))
       (hons (car x) (4v-sexpr-compose-nofal-list (cdr x) al))))
   (defun 4v-sexpr-compose-nofal-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (hons (4v-sexpr-compose-nofal (car x) al)
             (4v-sexpr-compose-nofal-list (cdr x) al)))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-compose-nofal-is-4v-sexpr-compose
      (equal (4v-sexpr-compose-nofal x al)
             (4v-sexpr-compose x al))
      :flag sexpr)
    (defthm 4v-sexpr-compose-nofal-list-is-4v-sexpr-compose-list
      (equal (4v-sexpr-compose-nofal-list x al)
             (4v-sexpr-compose-list x al))
      :flag sexpr-list)))


(defsection sexpr-rewrite1-args
  :parents (sexpr-rewriting-internals)
  :short "Given the args of a term and a list of possible rewrites for terms
with the same top function symbol, tries each of the rewrites until one
matches."
  :long "Returns (mv new-x changedp), where changedp indicates that there was a
rule that matched, and new-x is the rewritten term according to that rule.
New-x and changedp are both nil if no rule matched."
  ;; returns (mv new-x changedp)
  (defund sexpr-rewrite1-args (args rewrites)
    (declare (xargs :guard t))
    (b* (((when (atom rewrites)) (mv nil nil))
         ((when (atom (car rewrites)))
          (sexpr-rewrite1-args args (cdr rewrites)))
         ((mv ok subst)
          (sexpr-unify-list (caar rewrites) args nil))
         ((when ok)
          (b* ((newx (4v-sexpr-compose-nofal (cdar rewrites) subst)))
            (mv newx t))))
      (sexpr-rewrite1-args args (cdr rewrites))))

  (local (in-theory (enable sexpr-rewrite1-args)))

  ;; This says whether the rewrites are ok, i.e. each LHS is 4v-sexpr-equiv to
  ;; the corresponding RHS.  The LHSes are just lists of arguments, for which FN
  ;; is the top-level function symbol.
  ;; This isn't intended to be run, but to be proven, since 4v-sexpr-equiv is not
  ;; executable.  So we don't bother with a guard.
  (defun 4v-sexpr-fn-rewritesp (fn rewrites)
    (if (atom rewrites)
        t
      (and (consp (car rewrites))
           (4v-sexpr-equiv (cons fn (caar rewrites)) (cdar rewrites))
           (4v-sexpr-fn-rewritesp fn (cdr rewrites)))))

  ;; Variables that appear in the rewritten answer are variables that appear in X.
  (defthm 4v-sexpr-vars-sexpr-rewrite1-args
    (implies (not (member-equal k (4v-sexpr-vars-list x)))
             (not (member-equal
                   k (4v-sexpr-vars
                      (mv-nth 0 (sexpr-rewrite1-args x rewrites)))))))

  ;; If the rewrites are correct with respect to fn, then the result of
  ;; sexpr-rewrite1-args is equivalent to (cons fn args).
  (defthm sexpr-rewrite1-args-correct
    (implies (and (4v-sexpr-fn-rewritesp fn rewrites)
                  (mv-nth 1 (sexpr-rewrite1-args args rewrites)))
             (4v-sexpr-equiv (mv-nth 0 (sexpr-rewrite1-args args rewrites))
                             (cons fn args)))))


(defsection sexpr-rewrite1
  :parents (sexpr-rewriting-internals)
  :short "Performs one rewrite on a term, passed in as a top-level function and
its arguments."
  :long "A thin wrapper around sexpr-rewrite1-args, this looks up the rewrite
rules for a particular top-level function and calls sexpr-rewrite1-args to
apply one of them, if possible."
  ;; returns (mv new-x changedp)
  (defund sexpr-rewrite1 (fn args rewrite-al)
    (declare (xargs :guard t))
    ;; Do we want hons-assoc-equal or hons-get?
    ;; Hons-assoc-equal-seems ok because *sexpr-rewrites* is only 13 long;
    ;; according to profiling the difference (and the time spent in this function
    ;; altogether) is negligible.
    (b* ((rws (cdr (hons-assoc-equal fn rewrite-al))))
      (sexpr-rewrite1-args args rws)))

  (local (in-theory (enable sexpr-rewrite1)))

  ;; The result of rewriting contains only variables that are in the input (args).
  (defthm 4v-sexpr-vars-sexpr-rewrite1
    (implies (not (member-equal k (4v-sexpr-vars-list args)))
             (not (member-equal
                   k (4v-sexpr-vars (mv-nth 0 (sexpr-rewrite1 fn args rewrite-al)))))))

  ;; Predicate that indicates that al is a good alist of rewrite rules, mapping
  ;; function symbols to rewrite lists recognized by 4v-sexpr-fn-rewritesp.
  ;; Since that function is not intended to be executed, neither is this.  An
  ;; alist of rewrite rules must be proven to satisfy this predicate in order
  ;; to be legitimate.
  (defun 4v-sexpr-rewrite-alistp (al)
    ;; This isn't intended to be run, but to be proven.
    (if (atom al)
        t
      (and (consp (car al))
           (4v-sexpr-fn-rewritesp (caar al) (cdar al))
           (4v-sexpr-rewrite-alistp (cdr al)))))

  (defthm 4v-sexpr-fn-rewritesp-lookup-in-4v-sexpr-rewrite-alistp
    (implies (4v-sexpr-rewrite-alistp al)
             (4v-sexpr-fn-rewritesp x (cdr (hons-assoc-equal x al)))))

  ;; If the rewrite rules are OK, then if any rewrite occurred, the result of
  ;; sexpr-rewrite1 is equivalent to the input fn applied to args.
  (defthm sexpr-rewrite1-correct
    (implies (and (4v-sexpr-rewrite-alistp rewrites)
                  (mv-nth 1 (sexpr-rewrite1 fn args rewrites)))
             (4v-sexpr-equiv (mv-nth 0 (sexpr-rewrite1 fn args rewrites))
                             (cons fn args)))
    :hints (("goal" :use ((:instance sexpr-rewrite1-args-correct
                           (rewrites (cdr (hons-assoc-equal fn rewrites)))))
             :in-theory (disable sexpr-rewrite1-args-correct)))))


(defsection sexpr-rewrite-n
  :parents (sexpr-rewriting-internals)
  :short "Repeatedly rewrites a term (expressed as a top-level function and its
args) until it is stable or else a clock runs out."
  :long "Simply calls sexpr-rewrite1 over and over until there is no change, or
the iteration limit is up.  Returns the new term."

  (defund sexpr-rewrite-n (n fn args rewrite-al)
    (declare (xargs :guard (natp n)))
    (b* (((when (zp n))
          (cw "Sexpr-rewrite-n: Limit reached -- looping rewrite rule?~%")
          (cw "Try trace$ing some or all of sexp-rewrite-n, sexpr-rewrite1, sexpr-rewrite1-args.~%")
          (hons fn args))
         ((mv newx changed) (sexpr-rewrite1 fn args rewrite-al))
         ((when (or (not changed)
                    (and (consp newx)
                         (hqual (car newx) fn)
                         (hqual (cdr newx) args))))
          (sexpr-rewrite-ground (hons fn args)))
         (newx (sexpr-rewrite-ground newx))
         ((when (or (atom newx) (atom (cdr newx)))) newx))
      (sexpr-rewrite-n (1- n) (car newx) (cdr newx) rewrite-al)))

  (local (in-theory (enable sexpr-rewrite-n)))

  (local (defthm lemma
           (implies (NOT (MEMBER-EQUAL K (4V-SEXPR-VARS-LIST ARGS)))
                    (NOT (MEMBER-EQUAL K (4V-SEXPR-VARS (SEXPR-REWRITE-GROUND (CONS FN ARGS))))))
           :hints(("Goal" :in-theory (enable sexpr-rewrite-ground)))))

  ;; Variables in the result are in the input.
  (defthm 4v-sexpr-vars-sexpr-rewrite-n
    (implies (not (member-equal k (4v-sexpr-vars-list args)))
             (not (member-equal
                   k (4v-sexpr-vars (sexpr-rewrite-n n fn args rewrite-al)))))
    :hints (("goal" :induct  (sexpr-rewrite-n n fn args rewrite-al)
             :in-theory (disable 4v-sexpr-eval))
            '(:use ((:instance 4v-sexpr-vars-sexpr-rewrite1)
                    (:instance 4v-sexpr-vars-sexpr-rewrite-ground
                               (x (mv-nth 0 (sexpr-rewrite1 fn args rewrite-al)))))
                   :in-theory (e/d ()
                                   (4v-sexpr-vars-sexpr-rewrite1
                                    4v-sexpr-vars-sexpr-rewrite-ground
                                    4v-sexpr-eval)))))

  ;; The result of sexpr-rewrite-n is equivalent to the input (cons fn args), as
  ;; long as the rewrite rules are good.
  (defthm sexpr-rewrite-n-correct
    (implies (4v-sexpr-rewrite-alistp rewrites)
             (4v-sexpr-equiv (sexpr-rewrite-n n fn args rewrites)
                             (cons fn args)))
    :hints(("Goal" :in-theory (e/d ()
                                   (sexpr-rewrite1 4v-sexpr-eval))
            :induct (sexpr-rewrite-n n fn args rewrites))
           (witness :ruleset 4v-sexpr-equiv-witnessing))))


(defsection rewrites-to-al
  ;; Turns a straightforward alist of the form
  ;; ((lhs1  . rhs1)
  ;;  (lhs2  . rhs2)
  ;;  ...)
  ;; to the proper form for the rewriting functions above, namely
  ;; ((fn1 (lhs-args1 . rhs1)
  ;;       (lhs-args2 . rhs2)
  ;;       ...)
  ;;  (fn2 (lhs-args3 . rhs3)
  ;;       ...)
  ;;  ...)
  ;; The former is much more human read/writable, but we run on the latter
  ;; because it is more efficient.

  ;; Note: 4v-sexpr-rewritesp recognizes a proper alist of the form above,
  ;; i.e. one where each lhs is 4v-sexpr-equiv to the corresponding rhs.

  (defun rewrites-to-al (x)
    (declare (xargs :guard t))
    (b* (((when (atom x)) nil)
         (pair (car x))
         ((when (atom pair))
          (rewrites-to-al (cdr x)))
         (lhs (car pair))
         ((when (atom lhs))
          (rewrites-to-al (cdr x)))
         (fn (car lhs))
         (args (cdr lhs))
         (rhs (cdr pair))
         (rest (rewrites-to-al (cdr x)))
         (rest-fn-rewrites (cdr (hons-assoc-equal fn rest))))
      (cons (cons fn (cons (cons args rhs) rest-fn-rewrites)) rest)))

  ;; Reverse of rewrites-to-al, not necessarily very useful.
  (defun al-to-rewrites1 (fn rewrites)
    (declare (xargs :guard t))
    (b* (((when (atom rewrites)) nil)
         (pair (car rewrites))
         ((when (atom pair)) (al-to-rewrites1 fn (cdr rewrites)))
         ((cons lhs-args rhs) (car rewrites)))
      (cons (cons (cons fn lhs-args) rhs)
            (al-to-rewrites1 fn (cdr rewrites)))))

  (defun al-to-rewrites (al)
    (declare (Xargs :guard t))
    (b* (((when (atom al)) nil)
         (pair (car al))
         ((when (atom pair)) (al-to-rewrites (cdr al)))
         ((cons fn rewrites) pair))
      (append (al-to-rewrites1 fn rewrites)
              (al-to-rewrites (cdr al)))))

  ;; Note: This recognizes a straightforward human-read/rewritable alist of the
  ;; form described above, not the form that should be used by the rewriting
  ;; functions.
  (defun 4v-sexpr-rewritesp (al)
    ;; This isn't intended to be run, but to be proven.
    (if (atom al)
        t
      (and (consp (car al))
           (4v-sexpr-equiv (caar al) (cdar al))
           (4v-sexpr-rewritesp (cdr al))))))




(defsection sexpr-rewrite
  :parents (sexpr-rewriting sexpr-rewriting-internals)
  :short "Applies inside-out rewriting to an s-expression using a user-provided
set of rewrite rules."
  :long "A good (?) default set of rules is provided in *sexpr-rewrites*.  It
is a theorem that, if the rewrite rules are recognized by
4v-sexpr-rewrite-alistp, then the result is 4v-sexpr-equiv to the input.  It is
also a theorem that the variables of the result are a subset of those of the
input."
  (mutual-recursion
   (defun sexpr-rewrite (x rewrites)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (b* ((args (sexpr-rewrite-list (cdr x) rewrites)))
         (sexpr-rewrite-n 100 (car x) args rewrites))))

   (defun sexpr-rewrite-list (x rewrites)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (hons (sexpr-rewrite (car x) rewrites)
             (sexpr-rewrite-list (cdr x) rewrites)))))

  (memoize 'sexpr-rewrite :condition '(consp x))


  ;; The variables of the result are a subset of those of the inputs.
  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-vars-sexpr-rewrite
      (implies (not (member-equal k (4v-sexpr-vars x)))
               (not (member-equal k (4v-sexpr-vars (sexpr-rewrite x rewrites)))))
      :flag sexpr)

    (defthm 4v-sexpr-vars-sexpr-rewrite-list
      (implies (not (member-equal k (4v-sexpr-vars-list x)))
               (not (member-equal k (4v-sexpr-vars-list
                                     (sexpr-rewrite-list x rewrites)))))
      :flag sexpr-list))

  (defthm 4v-sexpr-vars-sexpr-rewrite-subset
    (subsetp-equal (4v-sexpr-vars (sexpr-rewrite x rewrites))
                   (4v-sexpr-vars x))
    :hints ((witness)))
  
  ;; If the rules provided are proper, then the result is equivalent to the
  ;; input.
  (defthm-4v-sexpr-flag
    (defthm sexpr-rewrite-correct
      (implies (4v-sexpr-rewrite-alistp rewrites)
               (4v-sexpr-equiv (sexpr-rewrite x rewrites)
                               x))
      :flag sexpr)
    (defthm sexpr-rewrite-list-correct
      (implies (4v-sexpr-rewrite-alistp rewrites)
               (4v-sexpr-list-equiv (sexpr-rewrite-list x rewrites)
                                    x))
      :flag sexpr-list)
    :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing)))

  (defun sexpr-rewrite-alist (x rewrites)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (atom (car x))
          (sexpr-rewrite-alist (cdr x) rewrites)
        (cons (cons (caar x) (sexpr-rewrite (cdar x) rewrites))
              (sexpr-rewrite-alist (cdr x) rewrites))))))

(defsection *sexpr-rewrites*
  :parents (sexpr-rewriting)
  :short "A useful set of 4v-s-expression rewrite rules, proven correct."

  (defconst *sexpr-rewrites*
    (let ((rules 
           '(

             ;; [Jared]: BOZO is this optimization note still true?  I thought
             ;; with the new database scheme the function order doesn't matter.
             ;; (It probably still matters within each function).

             ;; Optimization: Arrange these in order by how common the outermost
             ;; function is expected to be, and then by how common the pattern as a
             ;; whole is expected to be, but order by descending priority if some
             ;; rules can rewrite the same targets.  BOZO We should check how
             ;; common each of these function symbols are and do this on that basis
             ;; rather than by hunch.

             ;; ??? denotes rules of questionable utility.

             ;; Rules where the LHS has no variables are not needed because of the
             ;; separate ground-term elimination, sexpr-rewrite-ground.

             ;; Tristate constant propagation
             ((tristate (t) a)        . (buf a))
             ((tristate (f) a)        . (z))

             ;; [Jared]: some trivial tristate identities seem nice for
             ;; transistors
             ((tristate (buf c) a)        . (tristate c a))
             ((tristate c (tristate c a)) . (tristate c a))

             ;; RES with Z is the identity
             ((res (z) a)           . a)
             ((res a (z))           . a)
             ;; RES with X iS X
             ((res (x) a)           . (x))
             ((res a (x))           . (x))
             ;; RES with self is the identity
             ((res a a)             . a)
             ;; RES with opposite is X
             ((res a (not a))       . (x))
             ((res (not a) a)       . (x))

             ;; [Jared]: I added these to deal with some odd results on
             ;; sc_hldbuf2_5 and so on.  These are a little specialized, but
             ;; seem pretty nice for dealing with transistors that implement
             ;; inverters.  The above rules for handling (tristate (buf c) a)
             ;; and (tristate c (tristate c a)) are also important for these
             ;; to be effective.
             ((res (tristate (not a) (t)) (tristate a (f))) . (not a))
             ((res (tristate a (t)) (tristate (not a) (f))) . (buf a))



             ;; NOT: inputs are buffered
             ((not (buf a))         . (not a))
             ;; cancel NOTs
             ((not (not a))         . (buf a))

             ;; ITE constant propagation
             ((ite (t) a b)         . (buf a))
             ((ite (f) a b)         . (buf b))
             ((ite c (t) a)         . (or c a))
             ((ite c (f) a)         . (and (not c) a))
             ((ite c a (t))         . (or (not c) a))
             ((ite c a (f))         . (and c a))
             ;; ITE remove NOT on condition
             ((ite (not c) a b)     . (ite c b a))
             ;; ITE with identical branches
             ((ite c a a)           . (buf a))
             ;; ITE inputs are buffered
             ((ite (buf c) a b)     . (ite c a b))
             ((ite c (buf a) b)     . (ite c a b))
             ((ite c a (buf b))     . (ite c a b))
             ;; ?? ITE normalize to XOR
             ((ite a b (not b))     . (not (xor a b)))
             ((ite a (not b) b)     . (xor a b))


             ;; AND: constant propagation
             ((and (t) a)           . (buf a))
             ((and a (t))           . (buf a))
             ((and (f) a)           . (f))
             ((and a (f))           . (f))
             ;; AND with self
             ((and a a)             . (buf a))
             ;; ??? "Normalize" false-when-boolean things to (xor a a)
             ((and a (not a))       . (xor a a))
             ((and (not a) a)       . (xor a a))
             ;; AND inputs are buffered
             ((and (buf a) b)       . (and a b))
             ((and a (buf b))       . (and a b))
             ;; ?? pull out negations on args of AND with X
             ((and (not a) (x))     . (not (or a (x))))
             ((and (x) (not a))     . (not (or a (x))))
             ;; ?? normalize and with (x) to have (x) second arg
             ((and (x) a)           . (and a (x)))
             ;; and followed by or with x is x
             ((and (or a (x)) (x))  . (x))
             ;; big nestings of ands with the same thing multiple times seem
             ;; common
             ((and a (and a b))     . (and a b))
             ((and a (and b a))     . (and a b))
             ((and (and a b) a)     . (and a b))
             ((and (and b a) a)     . (and b a))
             ((and a (and b (and a c))) . (and a (and b c)))
             ((and a (and (and a c) b)) . (and a (and c b)))
             ((and a (and b (and c a))) . (and a (and b c)))
             ((and a (and (and c a) b)) . (and a (and c b)))

             ;; Jared: I rearranged these to try to right-associate ands, under
             ;; the probably miguided theory that it might help other rules
             ;; match.  We could do much more powerful and rewriting, i.e.,
             ;; collect up a set of arguments to each AND and then sort them,
             ;; perhaps noticing any contradictory arguments.  Similar
             ;; rewriting could be done for other AC operators.

             ;; ((and (and a b) (and a c)) . (and (and a b) c))
             ;; ((and (and a b) (and c a)) . (and (and a b) c))
             ;; ((and (and b a) (and a c)) . (and (and b a) c))
             ;; ((and (and b a) (and c a)) . (and (and b a) c))
             ;; ((and (and b (and a c)) a) . (and (and b c) a))
             ;; ((and (and (and a c) b) a) . (and (and c b) a))
             ;; ((and (and b (and c a)) a) . (and (and b c) a))
             ;; ((and (and (and c a) b) a) . (and (and c b) a))

             ((and (and a b) (and a c)) . (and a (and b c)))
             ((and (and a b) (and c a)) . (and a (and b c)))
             ((and (and b a) (and a c)) . (and a (and b c)))
             ((and (and b a) (and c a)) . (and a (and b c)))
             ((and (and b (and a c)) a) . (and a (and b c)))
             ((and (and (and a c) b) a) . (and a (and b c)))
             ((and (and b (and c a)) a) . (and a (and b c)))
             ((and (and (and c a) b) a) . (and a (and b c)))


             
             ;; Buf is the identity on anything except z, and the following
             ;; operations never produce z.
             ((buf (buf a))         . (buf a))
             ((buf (ite a b c))     . (ite a b c))
             ((buf (ite* a b c))    . (ite* a b c))
             ((buf (and a b))       . (and a b))
             ((buf (or a b))        . (or a b))
             ((buf (not a))         . (not a))
             ((buf (xor a b))       . (xor a b))
             ;; put this back in if we decide not to normalize iff to xor
             ;; ((buf (iff a b))       . (iff a b))
             ((buf (pullup a))      . (pullup a))


             ;; XOR constant propagation
             ((xor (t) b)           . (not b))
             ((xor (f) b)           . (buf b))
             ((xor a (t))           . (not a))
             ((xor a (f))           . (buf a))
             ;; XOR with X is X
             ((xor (x) b)           . (x))
             ((xor a (x))           . (x))
             ;; XOR inputs are buffered
             ((xor (buf a) b)       . (xor a b))
             ((xor a (buf b))       . (xor a b))

             ;; OR constant propagation
             ((or (t) a)            . (t))
             ((or a (t))            . (t))
             ((or (f) a)            . (buf a))
             ((or a (f))            . (buf a))
             ;; OR with self
             ((or a a)              . (buf a))
             ;; ??? "Normalize" true-when-boolean to (not (xor a a))
             ((or a (not a))        . (not (xor a a)))
             ((or (not a) a)        . (not (xor a a)))
             ;; OR inputs are buffered
             ((or (buf a) b)        . (or a b))
             ((or a (buf b))        . (or a b))
             ;; ?? pull out negations on args of OR with X
             ((or (not a) (x))      . (not (and a (x))))
             ((or (x) (not a))      . (not (and a (x))))
             ;; ?? normalize or with (x) to have (x) second arg
             ((or (x) a)            . (or a (x)))
             ;; or followed by and with x is x
             ((or (and a (x)) (x))  . (x))
             ;; big nestings of ors with the same thing multiple times seem
             ;; common
             ((or a (or a b))     . (or a b))
             ((or a (or b a))     . (or a b))
             ((or (or a b) a)     . (or a b))
             ((or (or b a) a)     . (or b a))

             ((or a (or b (or a c))) . (or a (or b c)))
             ((or a (or (or a c) b)) . (or a (or c b)))
             ((or a (or b (or c a))) . (or a (or b c)))
             ((or a (or (or c a) b)) . (or a (or c b)))

             ;; Jared: changed these to right-associate ORs.
             ;; ((or (or a b) (or a c)) . (or (or a b) c))
             ;; ((or (or a b) (or c a)) . (or (or a b) c))
             ;; ((or (or b a) (or a c)) . (or (or b a) c))
             ;; ((or (or b a) (or c a)) . (or (or b a) c))
             ;; ((or (or b (or a c)) a) . (or (or b c) a))
             ;; ((or (or (or a c) b) a) . (or (or c b) a))
             ;; ((or (or b (or c a)) a) . (or (or b c) a))
             ;; ((or (or (or c a) b) a) . (or (or c b) a))

             ((or (or a b) (or a c)) . (or a (or b c)))
             ((or (or a b) (or c a)) . (or a (or b c)))
             ((or (or b a) (or a c)) . (or a (or b c)))
             ((or (or b a) (or c a)) . (or a (or b c)))
             ((or (or b (or a c)) a) . (or a (or b c)))
             ((or (or (or a c) b) a) . (or a (or b c)))
             ((or (or b (or c a)) a) . (or a (or b c)))
             ((or (or (or c a) b) a) . (or a (or b c)))



             ;; Jared: I found a couple of nice reductions dealing with AND
             ;; and OR.
             ((and a (or a b)) . (buf a))
             ((and a (or b a)) . (buf a))
             ((and (or a b) a) . (buf a))
             ((and (or b a) a) . (buf a))


             ;; (let ((lhs '(and a (or a b)))
             ;;       (rhs '(buf a)))
             ;;   (loop for a in '(t f x z) do
             ;;         (loop for b in '(t f x z) do
             ;;               (b* ((al      (make-fast-alist `((a . ,a) (b . ,b))))
             ;;                    (lhs-res (4v-sexpr-eval lhs al))
             ;;                    (rhs-res (4v-sexpr-eval rhs al)))
             ;;                 (cw "~x0, ~x1 --> ~x2 vs. ~x3 (ok = ~x4)~%"
             ;;                     a b lhs-res rhs-res (equal lhs-res rhs-res))
             ;;                 (fast-alist-free al)))))


             ;; ITE* constant propagation
             ((ite* (t) a b)         . (buf a))
             ((ite* (f) a b)         . (buf b))
             ;; ITE* remove NOT on condition
             ((ite* (not c) a b)     . (ite* c b a))
             ;; ITE* inputs are buffered
             ((ite* (buf c) a b)     . (ite* c a b))
             ((ite* c (buf a) b)     . (ite* c a b))
             ((ite* c a (buf b))     . (ite* c a b))
             ;; ?? ITE* normalize to XOR
             ((ite* a b (not b))     . (not (xor a b)))
             ((ite* a (not b) b)     . (xor a b))

             ;; ??? Normalize IFF to NOT of XOR.
             ;; If we decide not to do this normalization, maybe move IFF up in the
             ;; order.
             ((iff a b)             . (not (xor a b)))
             ;; The rest of these rules for IFF won't be used unless we get rid of
             ;; the normalization to XOR above, but they don't hurt anything.
             ;; IFF constant propagation:
             ((iff (t) b)           . (buf b))
             ((iff (f) b)           . (not b))
             ((iff a (t))           . (buf a))
             ((iff a (f))           . (not a))
             ;; IFF with X is X
             ((iff (x) b)           . (x))
             ((iff a (x))           . (x))
             ;; IFF inputs are buffered.
             ((iff (buf a) b)       . (iff a b))
             ((iff a (buf b))       . (iff a b))


             ;; Pullup, like buf, is the identity on anything except z.
             ((pullup (buf a))         . (buf a))
             ((pullup (ite a b c))     . (ite a b c))
             ((pullup (ite* a b c))    . (ite* a b c))
             ((pullup (and a b))       . (and a b))
             ((pullup (or a b))        . (or a b))
             ((pullup (not a))         . (not a))
             ((pullup (xor a b))       . (xor a b))
             ;; put this back in if we decide not to normalize iff to xor
             ;; ((pullup (iff a b))       . (iff a b))
             ((pullup (pullup a))      . (pullup a))

             ;; ID can always just go away.
             ((id a)                . a))))

      (reverse
       (fast-alist-free
        (hons-shrink-alist (rewrites-to-al rules) nil)))))

  (table evisc-table *sexpr-rewrites* "#.*SEXPR-REWRITES*")

  (defthm nth-4v-sexpr-eval-list
    (equal (nth n (4v-sexpr-eval-list x env))
           (if (< (nfix n) (len x))
               (4v-sexpr-eval (nth n x) env)
             nil))
    :hints(("Goal" :in-theory (disable 4v-fix 4v-sexpr-eval))))

  (set-inhibit-warnings "theory" "disable")

  (defthm 4v-sexpr-rewritesp-sexpr-rewrites
    (4v-sexpr-rewrite-alistp *sexpr-rewrites*)
    :hints(("Goal" :in-theory (disable* (4v-sexpr-rewrite-alistp)
                                        (4v-sexpr-fn-rewritesp)
                                        sets::double-containment
                                        4v-sexpr-eval-list
                                        4v-sexpr-equiv
                                        hons-assoc-equal
                                        default-car
                                        default-cdr
                                        4v-fix-when-4vp
                                        (:rules-of-class :type-prescription :here)
                                        nth))
           (witness :ruleset 4v-sexpr-equiv-witnessing)
           )
    :otf-flg t))



(defsection 4v-shannon-expansion
  :parents (sexpr-rewriting)
  :short "A conservative transformation of an s-expression that pulls a
particular variable out into a top-level if-then-else."

  :long "<p>The shannon expansion of a term M by a Boolean variable V is</p>

<code>
if V then M' else M'',
</code>

<p>where M' is formed from M by substituting true for V and M'' is formed by
subsituting false for V.</p>

<p>For 4-valued terms we need to make a slight adjustment, because in the case
where V is X, this doesn't work.  Instead, the term we get looks like:</p>

<code>
 (XOR (XOR V V) (ITE V M' M'')).
</code>

<p>Here the term (XOR V V) detects the case where V is X or Z, and XORing that
with the if-then-else term makes the whole result X in that case.</p>

<p>This is useful for certain cases where a term may have false dependencies.
Consider</p>

<code>
 (ITE V (ITE (NOT V) A B) C).
</code>

<p>Intuitively, we'd think that the A branch wouldn't have any relevance, since
we can only get there by going through a V and a (NOT V) test, which are
contradictory.  But in fact there is a case where A affects the result: when B
and C are the same Boolean value and V=X.  Then, if A is the same Boolean value
as B and C, then the result is that value, otherwise X.  But we may be willing
to give up this special case and allow the term to evaluate to X whenever V is
X, in exchange for getting rid of the dependency on A.  The Shannon
expansion (if combined with rewriting) accomplishes this: the Shannon-rewritten
version of the term above looks like:</p>

<code>
 (XOR (XOR V V)
      (ITE (T) (ITE (NOT (T)) A B) C)
      (ITE (F) (ITE (NOT (F)) A B) C))
</code>

which rewrites to

<code>
 (XOR (XOR V V) B C).
</code>"

; [Jared] I now memoize the true/false alists for each variable to improve the
; memoization of 4v-sexpr-restrict as we shannon-expand several different sexprs,
; i.e., the sexprs for the update functions of a module.  This "leaks" fast
; alists, but that's not so scary since the FAL table is weak and they can be
; garbage collected.

  (defun 4v-shannon-expansion-true-al (var)
    (declare (xargs :guard t))
    (hons-acons var *4vt-sexpr* nil))

  (defun 4v-shannon-expansion-false-al (var)
    (declare (xargs :guard t))
    (hons-acons var *4vf-sexpr* nil))

  (memoize '4v-shannon-expansion-true-al)
  (memoize '4v-shannon-expansion-false-al)

; [Jared]: There are now two versions of shannon expansion, named -few and
; -many.  They are the same except that they have different performance
; characteristics.  The -few function should probably be used if you are just
; shannon expanding a few variables, whereas the -many function should be used
; if you are shannon expanding many (i.e., more than just a couple of
; variables).

  (defun 4v-shannon-expansion-few (var x)
    ;; [Jared]: this is almost the original version of 4v-shannon-expansion,
    ;; except that it now uses the memoized functions above to generate the
    ;; alists.  The good thing about this function is that it doesn't call
    ;; 4v-sexpr-vars, which can be very expensive.  The downside is that it has to
    ;; rewrite X at least once, even if VAR isn't mentioned in X, which can be
    ;; very expensive if you are shannon-expanding lots of variables that are
    ;; only in a few expressions.
    (declare (xargs :guard t))
    (b* ((true-al   (4v-shannon-expansion-true-al var))
         (true-br   (4v-sexpr-restrict x true-al))
         ((when (hons-equal true-br x))
          x)
         (false-al  (4v-shannon-expansion-false-al var))
         (false-br  (4v-sexpr-restrict x false-al)))
      `(xor (xor ,var ,var)
            (ite ,var ,true-br ,false-br))))

  (defun 4v-shannon-expansion-many (var x)
    ;; [Jared]: this is a new version of shannon-expansion that bites the
    ;; bullet and calls 4v-sexpr-vars, which can be very expensive, but hopefully
    ;; is only expensive once.  We then avoid rewriting the expression for this
    ;; variable unless we really need to.  In IU, where I'm shannon-expanding
    ;; hundreds of variables, this drastically outperforms the -few function.
    (declare (xargs :guard t))
    (b* ((vars (4v-sexpr-vars x))
         ((unless (gentle-member var vars))
          x)
         (true-al   (4v-shannon-expansion-true-al var))
         (true-br   (4v-sexpr-restrict x true-al))
         (false-al  (4v-shannon-expansion-false-al var))
         (false-br  (4v-sexpr-restrict x false-al)))
      `(xor (xor ,var ,var)
            (ite ,var ,true-br ,false-br))))



  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-with-redundant-cons
      (implies (equal (cdr (hons-assoc-equal v env)) val)
               (equal (4v-sexpr-eval x (cons (cons v val) env))
                      (4v-sexpr-eval x env)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-list-with-redundant-cons
      (implies (equal (cdr (hons-assoc-equal v env)) val)
               (equal (4v-sexpr-eval-list x (cons (cons v val) env))
                      (4v-sexpr-eval-list x env)))
      :flag sexpr-list)
    :hints (("goal" :expand ((:free (env) (4v-sexpr-eval x env))
                             (:free (env) (4v-sexpr-eval-list x env)))
             :in-theory (disable* (:ruleset 4v-op-defs)
                                  4v-sexpr-eval 4v-sexpr-eval-list))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-with-non-variable-cons
      (implies (consp v)
               (equal (4v-sexpr-eval x (cons (cons v val) env))
                      (4v-sexpr-eval x env)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-list-with-non-variable-cons
      (implies (consp v)
               (equal (4v-sexpr-eval-list x (cons (cons v val) env))
                      (4v-sexpr-eval-list x env)))
      :flag sexpr-list)
    :hints (("goal" :expand ((:free (env) (4v-sexpr-eval x env))
                             (:free (env) (4v-sexpr-eval-list x env)))
             :in-theory (disable* (:ruleset 4v-op-defs)
                                  4v-sexpr-eval 4v-sexpr-eval-list))))



  (defthm rewrite-ite-by-var-ok-simpl
    (4v-<= (4v-xor (4v-xor (4v-sexpr-eval v env) (4v-sexpr-eval v env))
                   (4v-ite (4v-sexpr-eval v env)
                           (4v-sexpr-eval a (cons (cons v t) env))
                           (4v-sexpr-eval b (cons (cons v 'f) env))))
           (4v-ite (4v-sexpr-eval v env)
                   (4v-sexpr-eval a env)
                   (4v-sexpr-eval b env)))
    :hints(("Goal" :in-theory (e/d* ()
                                    ((:ruleset 4v-op-defs)
                                     hons-assoc-equal nth)
                                    (4v-ite 4v-unfloat 4v-xor 4v-fix))
            :cases ((consp v) (not v)))))


  (defthm rewrite-ite-by-var-ok
    (4v-<= (4v-sexpr-eval
            `(xor (xor ,v ,v)
                  (ite ,v
                       ,(4v-sexpr-restrict a `((,v t)))
                       ,(4v-sexpr-restrict b `((,v f)))))
            env)
           (4v-sexpr-eval `(ite ,v ,a ,b) env))
    :hints(("Goal" :in-theory (e/d* ()
                                    ((:ruleset 4v-op-defs)
                                     hons-assoc-equal
                                     nth 4v-<=
                                     4v-sexpr-eval))
            :expand ((:free (a b env)
                            (4v-sexpr-eval (cons a b) env))))))





  (encapsulate nil
    (local
     (defthm-4v-sexpr-flag
       (defthm 4v-sexpr-restrict-unequal-when-member-4v-sexpr-vars
         (implies (not (member-equal k (4v-sexpr-vars x)))
                  (equal (4v-sexpr-restrict x `((,k t))) x))
         :flag sexpr)
       (defthm 4v-sexpr-restrict-list-unequal-when-member-4v-sexpr-vars
         (implies (not (member-equal k (4v-sexpr-vars-list x)))
                  (equal (4v-sexpr-restrict-list x `((,k t))) x))
         :flag sexpr-list)))

    (defthm 4v-sexpr-vars-4v-shannon-expansion-few
      (implies (and (not (member-equal k (4v-sexpr-vars x)))
                    (atom var))
               (not (member-equal k (4v-sexpr-vars (4v-shannon-expansion-few var x)))))))

  (defthm 4v-shannon-expansion-few-correct
    (4v-<= (4v-sexpr-eval (4v-shannon-expansion-few var x) env)
           (4v-sexpr-eval x env))
    :hints(("Goal" :in-theory (e/d* ()
                                    ((:ruleset 4v-op-defs)
                                     hons-assoc-equal nth
                                     4v-sexpr-restrict 4v-sexpr-eval
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here))
                                    (4v-ite 4v-unfloat 4v-xor 4v-fix))
            :expand ((:free (x y env) (4v-sexpr-eval (cons x y) env)))
            :cases ((consp var) (not var)))
           (and stable-under-simplificationp
                '(:expand ((4v-sexpr-eval var env))))))


  (defthm 4v-shannon-expansion-many-correct
    (4v-<= (4v-sexpr-eval (4v-shannon-expansion-many var x) env)
           (4v-sexpr-eval x env))
    :hints(("Goal" :in-theory (e/d* ()
                                    ((:ruleset 4v-op-defs)
                                     hons-assoc-equal nth
                                     4v-sexpr-restrict 4v-sexpr-eval
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here))
                                    (4v-ite 4v-unfloat 4v-xor 4v-fix))
            :expand ((:free (x y env) (4v-sexpr-eval (cons x y) env)))
            :cases ((consp var) (not var)))
           (and stable-under-simplificationp
                '(:expand ((4v-sexpr-eval var env))))))



  (defun 4v-shannon-expansion-mode-p (x)
    (declare (xargs :guard t))
    (or (eq x :few-vars)
        (eq x :many-vars)))

  (defun 4v-shannon-expansion-list (sigs x mode)
    (declare (xargs :guard (4v-shannon-expansion-mode-p mode)))
    (b* (((when (atom sigs))
          x)
         (x (4v-shannon-expansion-list (cdr sigs) x mode)))
      (if (eq mode :few-vars)
          (4v-shannon-expansion-few (car sigs) x)
        (4v-shannon-expansion-many (car sigs) x))))

  (defthm 4v-sexpr-vars-4v-shannon-expansion-list
    (implies (and (atom-listp sigs)
                  (not (member-equal k (4v-sexpr-vars x))))
             (not (member-equal k (4v-sexpr-vars (4v-shannon-expansion-list sigs x mode)))))
    :hints(("Goal" :in-theory (disable 4v-shannon-expansion-few))))

  (defthm 4v-shannon-expansion-list-correct
    (4v-<= (4v-sexpr-eval (4v-shannon-expansion-list vars x mode) env)
           (4v-sexpr-eval x env))
    :hints(("Goal" :in-theory (e/d* (4v-<=-trans2)
                                    ((:ruleset 4v-op-defs)
                                     hons-assoc-equal nth
                                     4v-shannon-expansion-few
                                     4v-shannon-expansion-many
                                     4v-<=
                                     4v-sexpr-restrict 4v-sexpr-eval
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here))
                                    (4v-ite 4v-unfloat 4v-xor 4v-fix)))))

  (defthm 4v-shannon-expansion-list-conservative
    (4v-sexpr-<= (4v-shannon-expansion-list vars x mode) x)
    :hints (("goal" :in-theory (disable 4v-<=))
            (witness)))


  (defun rewrite-with-shannon-expansion (vars x mode)
    (declare (xargs :guard (4v-shannon-expansion-mode-p mode)))
    (b* ((x (4v-shannon-expansion-list vars x mode)))
      (sexpr-rewrite x *sexpr-rewrites*)))

  (defthm rewrite-with-shannon-expansion-conservative
    (4v-sexpr-<= (rewrite-with-shannon-expansion vars x mode)
                 x))

  (defthm 4v-sexpr-vars-rewrite-with-shannon-expansion
    (implies (and (atom-listp vars)
                  (not (member-equal k (4v-sexpr-vars x))))
             (not (member-equal k (4v-sexpr-vars (rewrite-with-shannon-expansion vars x mode))))))



  (defun rewrite-with-shannon-expansion-alist-main (vars x mode)
    (declare (xargs :guard (4v-shannon-expansion-mode-p mode)))
    (b* (((when (atom x)) nil)
         ((when (atom (car x)))
          (rewrite-with-shannon-expansion-alist-main vars (cdr x) mode)))
      (cons (cons (caar x) (rewrite-with-shannon-expansion vars (cdar x) mode))
            (rewrite-with-shannon-expansion-alist-main vars (cdr x) mode))))

  (defthm 4v-sexpr-vars-rewrite-with-shannon-expansion-alist-main
    (implies (and (atom-listp vars)
                  (not (member-equal k (4v-sexpr-vars-list (alist-vals x)))))
             (not (member-equal
                   k (4v-sexpr-vars-list
                      (alist-vals (rewrite-with-shannon-expansion-alist-main
                                   vars x mode))))))
    :hints(("Goal" :in-theory (disable rewrite-with-shannon-expansion))))

  (defthm rewrite-with-shannon-expansion-alist-main-conservative
    (4v-sexpr-alist-<= (rewrite-with-shannon-expansion-alist-main vars x mode) x)
    :hints(("Goal"
            :in-theory (disable rewrite-with-shannon-expansion)
            :induct (rewrite-with-shannon-expansion-alist-main vars x mode))
           (witness :ruleset 4v-sexpr-alist-<=-witnessing)))

  (defthm alist-keys-rewrite-with-shannon-expansion-alist-main
    (equal (alist-keys (rewrite-with-shannon-expansion-alist-main vars x mode))
           (alist-keys x)))

  (defun rewrite-with-shannon-expansion-alist (vars x mode)
    (declare (xargs :guard (4v-shannon-expansion-mode-p mode)))
    (mbe :logic (rewrite-with-shannon-expansion-alist-main vars x mode)
         :exec
         (b* ((ans (rewrite-with-shannon-expansion-alist-main vars x mode)))
           (clear-memoize-table '4v-shannon-expansion-true-al)
           (clear-memoize-table '4v-shannon-expansion-false-al)
           (clear-memoize-table '4v-sexpr-restrict)
           (clear-memoize-table 'sexpr-rewrite)
           ans))))



; Jared: eliminated rewrite-its-with-var, which isn't used anywhere.
; Rewrite-with-shannon-expansion is better.  Note that previously we had
; proved this lemma in support of it:

  ;; (defthm 4v-<=-nths
  ;;   (implies (4v-list-<= (4v-sexpr-eval-list a env)
  ;;                        (4v-sexpr-eval-list b env))
  ;;            (4v-<= (4v-sexpr-eval (nth n a) env)
  ;;                   (4v-sexpr-eval (nth n b) env)))
  ;;   :hints(("Goal" :in-theory (disable 4v-sexpr-eval))))

;; Well, it doesn't belong here, at any rate.




(defsection sexpr-rewrite-default
  :parents (sexpr-rewriting)
  :short "Rewrite an s-expression with the default rewrite rules, *sexpr-rewrites*."
  :long "May be a bit faster than using sexpr-rewrite, because there is only
one argument to be memoized."

  (mutual-recursion
   (defun sexpr-rewrite-default (x)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (b* ((args (sexpr-rewrite-default-list (cdr x))))
         (sexpr-rewrite-n 100 (car x) args *sexpr-rewrites*))))

   (defun sexpr-rewrite-default-list (x)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (hons (sexpr-rewrite-default (car x))
             (sexpr-rewrite-default-list (cdr x))))))

  (memoize 'sexpr-rewrite-default :condition '(consp x))

  (defthm-4v-sexpr-flag
    (defthm sexpr-rewrite-default-is-sexpr-rewrite
      (equal (sexpr-rewrite-default x)
             (sexpr-rewrite x *sexpr-rewrites*))
      :flag sexpr)
    (defthm sexpr-rewrite-default-list-is-sexpr-rewrite-list
      (equal (sexpr-rewrite-default-list x)
             (sexpr-rewrite-list x *sexpr-rewrites*))
      :flag sexpr-list))





  (defun sexpr-rewrite-default-alist (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (atom (car x))
          (sexpr-rewrite-default-alist (cdr x))
        (cons (cons (caar x) (sexpr-rewrite-default (cdar x)))
              (sexpr-rewrite-default-alist (cdr x))))))

  (defthm sexpr-rewrite-default-alist-is-sexpr-rewrite-alist
    (equal (sexpr-rewrite-default-alist x)
           (sexpr-rewrite-alist x *sexpr-rewrites*)))


  (defun sexpr-rewrite-default-alists (x)
    (declare (Xargs :guard t))
    (if (atom x)
        nil
      (cons (sexpr-rewrite-default-alist (car x))
            (sexpr-rewrite-default-alists (cdr X))))))



(defsection sexpr-rewrite-of-restrict
  :parents (sexpr-rewriting)
  :short "One-pass 4v-sexpr-restrict followed by sexpr-rewrite"
  :long "Equivalent to sexpr-rewrite of 4v-sexpr-restrict.  Careful about
memoization here; wouldn't want to use this when you're about to (or just have)
done a 4v-sexpr-restrict of a similar sexpression with the same alist, or done a
sexpr-rewrite of an sexpression similar to your result.  Memoization won't
carry over."
  (mutual-recursion
   (defun sexpr-rewrite-of-restrict (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-get x al)))
                  ;; less than satisfying...
                  (if look (sexpr-rewrite-default (cdr look)) x)))
       (b* ((args (sexpr-rewrite-of-restrict-list (cdr x) al)))
         (sexpr-rewrite-n 100 (car x) args *sexpr-rewrites*))))

   (defun sexpr-rewrite-of-restrict-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (hons (sexpr-rewrite-of-restrict (car x) al)
             (sexpr-rewrite-of-restrict-list (cdr x) al)))))

  (memoize 'sexpr-rewrite-of-restrict :condition '(consp x))

  (defthm-4v-sexpr-flag
    (defthm sexpr-rewrite-of-restrict-is-sexpr-rewrite-of-4v-sexpr-restrict
      (equal (sexpr-rewrite-of-restrict x al)
             (sexpr-rewrite (4v-sexpr-restrict x al) *sexpr-rewrites*))
      :flag sexpr)
    (defthm sexpr-rewrite-of-restrict-list-is-sexpr-rewrite-list-of-4v-sexpr-restrict-list
      (equal (sexpr-rewrite-of-restrict-list x al)
             (sexpr-rewrite-list (4v-sexpr-restrict-list x al)
                                 *sexpr-rewrites*))
      :flag sexpr-list))

  (defun sexpr-rewrite-of-restrict-alist (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (atom (car x))
          (sexpr-rewrite-of-restrict-alist (cdr x) al)
        (cons (cons (caar x) (sexpr-rewrite-of-restrict (cdar x) al))
              (sexpr-rewrite-of-restrict-alist (cdr x) al)))))

  (defthm sexpr-rewrite-of-restrict-alist-is-sexpr-rewrite-alist
    (equal (sexpr-rewrite-of-restrict-alist x al)
           (sexpr-rewrite-alist
            (4v-sexpr-restrict-alist x al)
            *sexpr-rewrites*)))


  (defun sexpr-rewrite-of-restrict-alists (x al)
    (declare (Xargs :guard t))
    (if (atom x)
        nil
      (cons (sexpr-rewrite-of-restrict-alist (car x) al)
            (sexpr-rewrite-of-restrict-alists (cdr X) al))))

  (defun sexpr-rewrite-of-restrict-list-list (x al)
    (declare (Xargs :guard t))
    (if (atom x)
        nil
      (cons (sexpr-rewrite-of-restrict-list (car x) al)
            (sexpr-rewrite-of-restrict-list-list (cdr X) al)))))



(defsection 4v-sexpr-restrict-with-rw
  :parents (sexpr-rewriting 4v-sexprs)
  :short "4v-sexpr-restrict with inline rewriting."
  :long "This is different from
sexpr-rewrite-of-restrict because it doesn't apply rewriting to the alist
lookups; it basically assumes they've already been rewritten.  So while we
can't prove that this is equal to sexpr-rewrite of 4v-sexpr-restrict, we can
prove that it's sexpr-equivalent to 4v-sexpr-restrict, and contains a subset of
its variables.

Careful about
memoization here; wouldn't want to use this when you're about to (or just have)
done a 4v-sexpr-restrict of a similar sexpression with the same alist, or done a
sexpr-rewrite of an sexpression similar to your result.  Memoization won't
carry over."
  (mutual-recursion
   (defun 4v-sexpr-restrict-with-rw (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-get x al)))
                  ;; No rewriting done on the lookup.  Assume the alist range
                  ;; consists of already-rewritten sexprs.
                  (if look (cdr look) x)))
       (b* ((args (4v-sexpr-restrict-with-rw-list (cdr x) al)))
         (sexpr-rewrite-n 100 (car x) args *sexpr-rewrites*))))

   (defun 4v-sexpr-restrict-with-rw-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (hons (4v-sexpr-restrict-with-rw (car x) al)
             (4v-sexpr-restrict-with-rw-list (cdr x) al)))))

  (memoize '4v-sexpr-restrict-with-rw :condition '(consp x))


  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-restrict-with-rw-equiv-to-4v-sexpr-restrict
      (4v-sexpr-equiv (4v-sexpr-restrict-with-rw x al)
                      (4v-sexpr-restrict x al))
      :flag sexpr)
    (defthm 4v-sexpr-restrict-with-rw-list-equiv-to-4v-sexpr-restrict-list
      (4v-sexpr-list-equiv (4v-sexpr-restrict-with-rw-list x al)
                           (4v-sexpr-restrict-list x al))
      :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing))
      :flag sexpr-list))


  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-vars-4v-sexpr-restrict-with-rw
      (implies (and (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
                    (not (and (member-equal k (4v-sexpr-vars x))
                              (not (member-equal k (alist-keys al))))))
               (not (member-equal k (4v-sexpr-vars (4v-sexpr-restrict-with-rw x al)))))
      :flag sexpr)
    (defthm 4v-sexpr-vars-list-4v-sexpr-restrict-with-rw-list
      (implies
       (and (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
            (not (and (member-equal k (4v-sexpr-vars-list x))
                      (not (member-equal k (alist-keys al))))))
       (not (member-equal k (4v-sexpr-vars-list (4v-sexpr-restrict-with-rw-list x al)))))
      :flag sexpr-list))


  (defun 4v-sexpr-restrict-with-rw-alist (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (atom (car x))
          (4v-sexpr-restrict-with-rw-alist (cdr x) al)
        (cons (cons (caar x) (4v-sexpr-restrict-with-rw (cdar x) al))
              (4v-sexpr-restrict-with-rw-alist (cdr x) al)))))

  (defthm hons-assoc-equal-4v-sexpr-restrict-with-rw-alist
    (equal (hons-assoc-equal k (4v-sexpr-restrict-with-rw-alist x al))
           (and (hons-assoc-equal k x)
                (cons k (4v-sexpr-restrict-with-rw
                         (cdr (hons-assoc-equal k x))
                         al)))))

  (defthm 4v-sexpr-restrict-with-rw-alist-equiv-to-4v-sexpr-restrict-alist
    (4v-sexpr-alist-equiv (4v-sexpr-restrict-with-rw-alist x al)
                          (4v-sexpr-restrict-alist x al)))

  (defthm sexpr-eval-alist-of-4v-sexpr-restrict-with-rw-alist
    (equal (4v-sexpr-eval-alist (4v-sexpr-restrict-with-rw-alist x al) env)
           (4v-sexpr-eval-alist (4v-sexpr-restrict-alist x al) env)))

  (defthm alist-keys-4v-sexpr-restrict-with-rw-alist
    (equal (alist-keys (4v-sexpr-restrict-with-rw-alist al env))
           (alist-keys al)))

  (defthm 4v-sexpr-restrict-with-rw-alist-append
    (equal (4v-sexpr-restrict-with-rw-alist (append al1 al2) env)
           (append (4v-sexpr-restrict-with-rw-alist al1 env)
                   (4v-sexpr-restrict-with-rw-alist al2 env))))

  (defun 4v-sexpr-restrict-with-rw-alists (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-restrict-with-rw-alist (car x) al)
            (4v-sexpr-restrict-with-rw-alists (cdr x) al))))

  (defun 4v-sexpr-restrict-with-rw-list-list (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-restrict-with-rw-list (car x) al)
            (4v-sexpr-restrict-with-rw-list-list (cdr x) al)))))


(defsection 4v-sexpr-compose-with-rw
  :parents (sexpr-rewriting 4v-sexprs)
  :short "4v-sexpr-compose with inline rewriting."
  :long "This is different from
sexpr-rewrite-of-compose because it doesn't apply rewriting to the alist
lookups; it basically assumes they've already been rewritten.  So while we
can't prove that this is equal to sexpr-rewrite of 4v-sexpr-compose, we can
prove that it's sexpr-equivalent to 4v-sexpr-compose, and contains a subset of
its variables.

Careful about
memoization here; wouldn't want to use this when you're about to (or just have)
done a 4v-sexpr-compose of a similar sexpression with the same alist, or done a
sexpr-rewrite of an sexpression similar to your result.  Memoization won't
carry over."
  (mutual-recursion
   (defun 4v-sexpr-compose-with-rw (x al)
     (declare (xargs :guard t))
     (if (atom x)
         (and x (let ((look (hons-get x al)))
                  ;; No rewriting done on the lookup.  Assume the alist range
                  ;; consists of already-rewritten sexprs.
                  (and look (cdr look))))
       (b* ((args (4v-sexpr-compose-with-rw-list (cdr x) al)))
         (sexpr-rewrite-n 100 (car x) args *sexpr-rewrites*))))

   (defun 4v-sexpr-compose-with-rw-list (x al)
     (declare (xargs :guard t))
     (if (atom x)
         x
       (hons (4v-sexpr-compose-with-rw (car x) al)
             (4v-sexpr-compose-with-rw-list (cdr x) al)))))

  (memoize '4v-sexpr-compose-with-rw :condition '(consp x))


  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-compose-with-rw-equiv-to-4v-sexpr-compose
      (4v-sexpr-equiv (4v-sexpr-compose-with-rw x al)
                      (4v-sexpr-compose x al))
      :flag sexpr)
    (defthm 4v-sexpr-compose-with-rw-list-equiv-to-4v-sexpr-compose-list
      (4v-sexpr-list-equiv (4v-sexpr-compose-with-rw-list x al)
                           (4v-sexpr-compose-list x al))
      :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing))
      :flag sexpr-list))


  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-vars-4v-sexpr-compose-with-rw
      (implies (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
               (not (member-equal k (4v-sexpr-vars (4v-sexpr-compose-with-rw x al)))))
      :flag sexpr)
    (defthm 4v-sexpr-vars-list-4v-sexpr-compose-with-rw-list
      (implies
       (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
       (not (member-equal k (4v-sexpr-vars-list (4v-sexpr-compose-with-rw-list x al)))))
      :flag sexpr-list))


  (defun 4v-sexpr-compose-with-rw-alist (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (atom (car x))
          (4v-sexpr-compose-with-rw-alist (cdr x) al)
        (cons (cons (caar x) (4v-sexpr-compose-with-rw (cdar x) al))
              (4v-sexpr-compose-with-rw-alist (cdr x) al)))))

  (defthm hons-assoc-equal-4v-sexpr-compose-with-rw-alist
    (equal (hons-assoc-equal k (4v-sexpr-compose-with-rw-alist x al))
           (and (hons-assoc-equal k x)
                (cons k (4v-sexpr-compose-with-rw
                         (cdr (hons-assoc-equal k x))
                         al)))))

  (defthm 4v-sexpr-compose-with-rw-alist-equiv-to-4v-sexpr-compose-alist
    (4v-sexpr-alist-equiv (4v-sexpr-compose-with-rw-alist x al)
                          (4v-sexpr-compose-alist x al)))

  (defthm sexpr-eval-alist-of-4v-sexpr-compose-with-rw-alist
    (equal (4v-sexpr-eval-alist (4v-sexpr-compose-with-rw-alist x al) env)
           (4v-sexpr-eval-alist (4v-sexpr-compose-alist x al) env)))

  (defthm alist-keys-4v-sexpr-compose-with-rw-alist
    (equal (alist-keys (4v-sexpr-compose-with-rw-alist al env))
           (alist-keys al)))

  (defthm 4v-sexpr-compose-with-rw-alist-append
    (equal (4v-sexpr-compose-with-rw-alist (append al1 al2) env)
           (append (4v-sexpr-compose-with-rw-alist al1 env)
                   (4v-sexpr-compose-with-rw-alist al2 env))))

  (defun 4v-sexpr-compose-with-rw-alists (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-compose-with-rw-alist (car x) al)
            (4v-sexpr-compose-with-rw-alists (cdr x) al))))

  (defun 4v-sexpr-compose-with-rw-list-list (x al)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-compose-with-rw-list (car x) al)
            (4v-sexpr-compose-with-rw-list-list (cdr x) al)))))



(defstub 4v-sexpr-simp-and-eval-output (simp-fns structtype) nil)

(defun 4v-sexpr-simp-and-eval-output-quiet (simp-fns structtype)
  (declare (xargs :guard t) (ignore simp-fns structtype))
  nil)







(defun 4v-sexpr-simp-and-eval-output-loud (simp-fns structtype)
  (declare (xargs :guard t))
  (let ((unbound-vars (case structtype
                        (sexpr (4v-sexpr-vars-1pass simp-fns))
                        (list (4v-sexpr-vars-1pass simp-fns))
                        (alist (4v-sexpr-vars-1pass-list (alist-vals simp-fns)))
                        (alists (4v-sexpr-vars-alists simp-fns))
                        (list-list (4v-sexpr-vars-1pass-list-list simp-fns)))))
    (and unbound-vars
         (cw "4v-sexpr-simp-and-eval: unbound variables:~%~x0~%"
             unbound-vars))))

(defmacro 4v-sexpr-simp-and-eval-complain (flag)
  `(defattach 4v-sexpr-simp-and-eval-output
     ,(if flag '4v-sexpr-simp-and-eval-output-loud
        '4v-sexpr-simp-and-eval-output-quiet)))

(4v-sexpr-simp-and-eval-complain nil)




(defsection 4v-sexpr-simp-and-eval
  :parents (4v-sexpr-eval)
  :short "Version of 4v-sexpr-eval that simplifies before evaluating"
  :long "4v-sexpr-simp-and-eval computes the same result as 4v-sexpr-eval, but
does so in a roundabout way where it first simplifies the given S-expression
under the assignments given in the alist.  However, missing assignments, which
in 4v-sexpr-eval are treated as X, are ignored during this simplification pass,
which uses 4v-sexpr-restrict-with-rw.  After simplification, 4v-sexpr-eval is
called with an empty environment, so that all remaining variables are assigned
X.

What is the advantage of 4v-sexpr-simp-and-eval?  Sometimes during verification
we have a complicated S-expression that contains variables that probably don't
matter, and since we don't want to assume anything about their values, we leave
them as Xes.  But sometimes we then find that the result we get is itself X,
and we want to know why.  We can set 4v-lookup to complain when it doesn't find
a variable in the environment, but if we're running the standard 4v-sexpr-eval
we'll just get complaints about all the missing variables.  However, if we run
4v-sexpr-simp-and-eval instead, we only get complaints about the ones that seem
to actually matter in the final result, i.e. they weren't pruned away when
simplifying using the known signals."

  (defun 4v-al-to-sexpr-al (al)
    (declare (xargs :guard t))
    (cond ((atom al) nil)
          ((atom (car al)) (4v-al-to-sexpr-al (cdr al)))
          (t (cons (cons (caar al) (hons (4v-fix (cdar al)) nil))
                   (4v-al-to-sexpr-al (cdr al))))))

  (defthm 4v-al-to-sexpr-al-lookup
    (equal (hons-assoc-equal x (4v-al-to-sexpr-al al))
           (and (hons-assoc-equal x al)
                (cons x (list (4v-fix (cdr (hons-assoc-equal x al)))))))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal) (4v-fix)))))

  (defthm 4v-sexpr-eval-of-list-4v-fix
    (equal (4v-sexpr-eval (list (4v-fix x)) env)
           (4v-fix x)))

  (local (in-theory (disable 4v-sexpr-eval 4v-fix)))

  (defthm 4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
    (4v-env-equiv (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) env)
                  al)
    :hints ((witness)))

  (defun 4v-sexpr-simp-and-eval (x al)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-eval x al)
         :exec (b* ((restrict-al (make-fast-alist (4v-al-to-sexpr-al al)))
                    (simpl-x (4v-sexpr-restrict-with-rw x restrict-al)))
                 (4v-sexpr-simp-and-eval-output simpl-x 'sexpr)
                 (fast-alist-free restrict-al)
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-eval simpl-x nil))))

  (defun 4v-sexpr-simp-and-eval-list (x al)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-eval-list x al)
         :exec (b* ((restrict-al (make-fast-alist (4v-al-to-sexpr-al al)))
                    (simpl-x (4v-sexpr-restrict-with-rw-list x restrict-al)))
                 (fast-alist-free restrict-al)
                 (4v-sexpr-simp-and-eval-output simpl-x 'list)
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-eval-list simpl-x nil))))

  (defun 4v-sexpr-simp-and-eval-alist (x al)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-eval-alist x al)
         :exec (b* ((restrict-al (make-fast-alist (4v-al-to-sexpr-al al)))
                    (simpl-x (4v-sexpr-restrict-with-rw-alist x restrict-al)))
                 (4v-sexpr-simp-and-eval-output simpl-x 'alist)
                 (fast-alist-free restrict-al)
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-eval-alist simpl-x nil))))

  (defun 4v-sexpr-simp-and-eval-alists (x al)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-eval-alists x al)
         :exec (b* ((restrict-al (make-fast-alist (4v-al-to-sexpr-al al)))
                    (simpl-x (4v-sexpr-restrict-with-rw-alists x restrict-al)))
                 (4v-sexpr-simp-and-eval-output simpl-x 'alists)
                 (fast-alist-free restrict-al)
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-eval-alists simpl-x nil))))

  (defun 4v-sexpr-simp-and-eval-list-list (x al)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-eval-list-list x al)
         :exec (b* ((restrict-al (make-fast-alist (4v-al-to-sexpr-al al)))
                    (simpl-x (4v-sexpr-restrict-with-rw-list-list x restrict-al)))
                 (4v-sexpr-simp-and-eval-output simpl-x 'list-list)
                 (fast-alist-free restrict-al)
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-eval-list-list simpl-x nil)))))



