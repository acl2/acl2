; Copyright (C) 2012 Centaur Technology
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

; Contextual rewriting framework

(in-package "ACL2")

(include-book "clause-processors/unify-subst" :dir :system)
(include-book "centaur/misc/alist-witness" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)
(include-book "xdoc/top" :dir :system)

(local (in-theory (disable append-of-nil)))
(local (in-theory (disable all-boundp
                           set::double-containment
                           all-keys-bound)))

(defxdoc contextual-rewriting
  :parents (proof-automation)
  :short "A meta-rule system that lets the ACL2 rewriter pass around contextual
information.  Similar to Dave Greve's NARY.  This extends ACL2's notion of
congruence-based rewriting."
  :long "The motivating example:  We have the following two theorems:
<code>
 (defthm mod-n-first-arg-of-plus-context
   (implies (and (rationalp x)
                 (rationalp y)
                 (rationalp n)
                 (not (equal n 0)))
            (equal (mod (+ (mod x n) y) n)
                   (mod (+ x y) n))))
 (defthm mod-n-second-arg-of-plus-context
   (implies (and (rationalp x)
                 (rationalp y)
                 (rationalp n)
                 (not (equal n 0)))
            (equal (mod (+ x (mod y n)) n)
                   (mod (+ x y) n))))
</code>
Basically, if we have addition in a mod N context, then each of the terms of
the sum is also in a mod N context.  Now suppose we have:
<code>
 (defthm foo-bar-under-mod
    (equal (mod (foo m n) n)
           (mod (bar m n) n)))
</code>
This allows us to rewrite (foo m n) to (bar m n) under a mod N context.  But
perhaps we want to prove:
<code>
 (implies (and (rationalp a)
               ...
               (rationalp n)
               (not (equal n 0)))
              (equal (mod (+ a b c d (foo m n) e) n)
                     (mod (+ a b c d (bar m n) e) n)))
</code>

Logically, the three theorems we have are sufficent to prove this last one.
But it's painful because the rewrite rules don't really help us.  What we
really want is to be able to say: When rewriting a sum under mod N context,
we may rewrite all its terms under a mod N context.

So here's how our meta rule accomplishes that.  We take our two context
theorems and tell our meta rule to use them:
<code>
 (add-context-rule mod (:rewrite mod-n-first-arg-of-plus-context))
 (add-context-rule mod (:rewrite mod-n-second-arg-of-plus-context))
</code>
A special thing about each of these rules is that the LHS unifies with the RHS,
and there is only one variable in the substitution that isn't bound to itself
after this unification.  Namely, in the first rule, <tt>x</tt> is bound to
<tt>(mod x n)</tt>, but <tt>y</tt> and <tt>n</tt> are bound to themselves.
This is the requirement for a context rule.  It is used as follows.

Suppose we've come to the MOD term on the LHS of the theorem above.  Our meta rule
operates by trying to apply rewrite rules backwards!  So first, we unify our
term, <tt>(mod (+ a b c d (foo m n) e) n)</tt>, with the RHS of the first rule,
<tt>(mod (+ x y) n)</tt>.  This works and we have <tt>x</tt> bound to
<tt>a</tt>, <tt>y</tt> bound to <tt>(+ b c d (foo m n) e)</tt>, and <tt>n</tt>
bound to <tt>n</tt>.  We then simplify the term corresponding to <tt>x</tt> in
the LHS under this substitution.  This is just <tt>(mod a n)</tt>, which
probably doesn't simplify to anything.  So this application fails.

We then try the second rule.  This causes <tt>y</tt>, which is bound to
<tt>(+ b c d (foo m n) e)</tt>, to be rewritten under mod N.  Now, our meta
rule fires recursively on this sum, so each element is rewritten under a mod N
context.  Specifically, when we get to <tt>(foo m n)</tt>, we can apply
foo-bar-under-mod.

To do: performance tuning; get it working under equivalences other than equal;
add mechanism for disabling certain context-propagation rules; add ttree stuff
when it becomes available.
")


(defevaluator-fast ctx-ev ctx-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (acl2-numberp x)
   (binary-* x y)
   (binary-+ x y)
   (unary-- x)
   (unary-/ x)
   (< x y)
   (car x)
   (cdr x)
   (char-code x)
   (characterp x)
   (code-char x)
   (complex x y)
   (complex-rationalp x)
   (coerce x y)
   (cons x y)
   (consp x)
   (denominator x)
   (equal x y)
   (imagpart x)
   (integerp x)
   (intern-in-package-of-symbol x y)
   (numerator x)
   (rationalp x)
   (realpart x)
   (stringp x)
   (symbol-name x)
   (symbol-package-name x)
   (symbolp x))
  :namedp t)

(def-meta-extract ctx-ev ctx-ev-lst)

(def-unify ctx-ev ctx-ev-alist)

(def-functional-instance
  ctx-ev-of-sublis-var
  eval-of-sublis-var
  ((cterm-ev ctx-ev)
   (cterm-ev-lst ctx-ev-lst)
   (cterm-ev-alist ctx-ev-alist))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable ctx-ev-of-fncall-args)))))

(def-functional-instance
  ctx-ev-of-term-subst
  eval-of-term-subst
  ((cterm-ev ctx-ev)
   (cterm-ev-lst ctx-ev-lst)
   (cterm-ev-alist ctx-ev-alist))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable ctx-ev-of-fncall-args)))))

(local (defthm assoc-equal-when-key-nonnil
         (implies key
                  (equal (assoc-equal key x)
                         (hons-assoc-equal key x)))))

(defun rewrite-rule-parts (lemma)
  (declare (xargs :verify-guards nil))
  (mv (access rewrite-rule lemma :subclass)
      (access rewrite-rule lemma :hyps)
      (access rewrite-rule lemma :equiv)
      (access rewrite-rule lemma :lhs)
      (access rewrite-rule lemma :rhs)))

(local (in-theory (disable symbol-alistp)))

(defthm symbol-listp-strip-cars-of-symbol-alist
  (implies (symbol-alistp x)
           (symbol-listp (strip-cars x)))
  :hints(("Goal" :in-theory (enable symbol-alistp))))


(local (defthm pseudo-term-substp-of-append
         (implies (and (pseudo-term-substp a)
                       (pseudo-term-substp b))
                  (pseudo-term-substp (append a b)))
         :hints(("Goal" :in-theory (enable pseudo-term-substp)))))


(defsection mx-relieve-hyp
  (local (defthm symbol-alistp-impl-true-listp
           (implies (symbol-alistp x)
                    (true-listp x))))
  (defund mx-relieve-hyp (hyp alist rune target n mfc state)
    (declare (xargs :stobjs state
                    :guard (and (pseudo-termp hyp)
                                (symbol-alistp alist)
                                (natp n))))
    (b* (((unless (mbe :logic (eq (ffn-symb hyp) 'synp)
                       :exec (and (nvariablep hyp)
                                  (not (fquotep hyp))
                                  (eq (ffn-symb hyp) 'synp))))
          (b* (((unless (all-keys-bound (simple-term-vars hyp) alist))
                ;; Can't allow free variables in the hyps if we're going to
                ;; extend the substitution later.
                ;; Deal later with binding-hyps and free-variable hyps, maybe.
                (cw "mx-relieve-hyp: hyp has free variables: ~x0~%" hyp)
                (mv nil alist))
               (res (mfc-relieve-hyp hyp alist rune target (1+ n) mfc state
                                     :forcep nil)))
            (mv res alist)))
         (args (fargs hyp))
         ((unless (and
                   ;; check that synp is defined as expected
                   (fn-check-def 'synp state '(vars form term) ''t)
                   ;; check that all three args are quoted
                   (equal (len args) 3)
                   (quote-listp args)))
          (mv nil alist))
         (syntaxp-form (unquote (second args)))
         (syntaxp-fn (and (consp syntaxp-form) (car syntaxp-form)))
         ((unless (member syntaxp-fn '(bind-free syntaxp)))
          (mv nil alist))
         (term (unquote (third args)))
         ((unless (pseudo-termp term))
          (mv nil alist))
         ((mv eval-err val)
          (magic-ev term alist state t t))
         ((when eval-err)
          (cw "synp error in mx-relieve-hyp: ~@0~%" (if (eq eval-err t) "error"
                                                      eval-err))
          (mv nil alist))
         ((unless (and val
                       (implies (eq syntaxp-fn 'syntaxp)
                                (eq val t))
                       (implies (eq syntaxp-fn 'bind-free)
                                (and (symbol-alistp val)
                                     (not (assoc-eq nil val))
                                     (not (intersectp-eq (strip-cars val)
                                                         (strip-cars alist)))
                                     (pseudo-term-substp val)))))
          (mv nil alist)))
      (mv t (if (eq syntaxp-fn 'bind-free)
                (append val alist)
              alist))))
  (local (in-theory (enable mx-relieve-hyp)))

  (encapsulate nil
    (local (defthm alistp-member-strip-cars
             (implies (not (member x (strip-cars y)))
                      (not (hons-assoc-equal x y)))
             :hints(("Goal" :in-theory (enable strip-cars hons-assoc-equal)))))
    (local (defthm sub-alistp-append-when-not-intersecting-1
             (implies (and (alistp a)
                           (not (intersectp (strip-cars a) (strip-cars b)))
                           (hons-assoc-equal x b))
                      (equal (hons-assoc-equal x a) nil))
             :hints(("Goal" :in-theory (enable strip-cars hons-assoc-equal append)
                     :induct (append a b)))))

    (defthm sub-alistp-append-when-not-intersecting
      (implies (and (alistp a)
                    (not (intersectp (strip-cars a) (strip-cars b))))
               (sub-alistp b (append a b)))
      :hints(("Goal" :in-theory (enable sub-alistp-iff-witness)))))

  (defthm alistp-when-symbol-alistp
    (implies (symbol-alistp x)
             (alistp x)))

  (defthm mx-relieve-hyp-extends-alist
    (sub-alistp alist (mv-nth 1 (mx-relieve-hyp
                                 hyp alist rune target n mfc state)))
    :hints(("Goal" :in-theory (enable sub-alistp-when-witness))))

  (encapsulate nil
    (local (defthm equal-len
             (implies (syntaxp (quotep n))
                      (equal (equal (len x) n)
                             (and (natp n)
                                  (if (= n 0)
                                      (atom x)
                                    (and (consp x)
                                         (equal (len (cdr x)) (1- n)))))))))

    (defthm mx-relieve-hyp-all-vars-bound
      (mv-let (ok new-alist)
        (mx-relieve-hyp hyp alist rune target n mfc state)
        (implies ok
                 (all-keys-bound (simple-term-vars hyp) new-alist)))
      :hints(("Goal" :in-theory (enable all-keys-bound
                                        simple-term-vars
                                        simple-term-vars-lst)))))


  (defthm hons-assoc-equal-in-ctx-ev-alist
    (implies x
             (equal (hons-assoc-equal x (ctx-ev-alist subst a))
                    (and (hons-assoc-equal x subst)
                         (cons x (ctx-ev (cdr (hons-assoc-equal x subst)) a))))))


  (defthm-substitute-into-term-flag
    (defthm ctx-ev-alist-equiv
      (implies (and (alist-equiv a b)
                    (pseudo-termp x))
               (equal (ctx-ev x a)
                      (ctx-ev x b)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable ctx-ev-of-fncall-args))))
      :rule-classes nil
      :flag substitute-into-term)
    (defthm ctx-ev-lst-alist-equiv
      (implies (and (alist-equiv a b)
                    (pseudo-term-listp x))
               (equal (ctx-ev-lst x a)
                      (ctx-ev-lst x b)))
      :rule-classes nil
      :flag substitute-into-list))

  (defthm alist-equiv-append-sub-alist
    (implies (sub-alistp a b)
             (alist-equiv (append a b)
                          b))
    :hints((alist-reasoning)))

  (defthm-substitute-into-term-flag
    (defthm ctx-ev-alist-extension-when-vars-bound
      (implies (and (all-keys-bound (simple-term-vars x) a)
                    (sub-alistp a b)
                    (pseudo-termp x))
               (equal (equal (ctx-ev x b)
                             (ctx-ev x a))
                      t))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable ctx-ev-of-fncall-args
                                        sub-alistp-hons-assoc-equal
                                        simple-term-vars-lst
                                        all-keys-bound)
                     :expand ((simple-term-vars x)))))
      :flag substitute-into-term)
    (defthm ctx-ev-lst-extension-when-vars-bound
      (implies (and (all-keys-bound (simple-term-vars-lst x) a)
                    (sub-alistp a b)
                    (pseudo-term-listp x))
               (equal (equal (ctx-ev-lst x b)
                             (ctx-ev-lst x a))
                      t))
      :hints ('(:expand ((simple-term-vars-lst x))))
      :flag substitute-into-list))

  (defthm-substitute-into-term-flag
    (defthm ctx-ev-alist-extension-append-when-vars-bound
      (implies (and (all-keys-bound (simple-term-vars x) a)
                    (pseudo-termp x))
               (equal (ctx-ev x (append a b))
                      (ctx-ev x a)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable ctx-ev-of-fncall-args
                                        all-keys-bound)
                     :expand ((simple-term-vars x)))))
      :flag substitute-into-term)
    (defthm ctx-ev-lst-extension-append-when-vars-bound
      (implies (and (all-keys-bound (simple-term-vars-lst x) a)
                    (pseudo-term-listp x))
               (equal (ctx-ev-lst x (append a b))
                      (ctx-ev-lst x a)))
      :hints ('(:expand ((simple-term-vars-lst x))))
      :flag substitute-into-list))

  (local (in-theory (disable symbol-alistp magic-ev
                             pseudo-term-substp)))

  (defthm ctx-ev-mx-relieve-hyp-correct
    (mv-let (ok new-alist)
      (mx-relieve-hyp hyp alist rune target n mfc state)
      (implies (and (ctx-ev-meta-extract-contextual-facts a)
                    (ctx-ev-meta-extract-global-facts)
                    (not (assoc nil alist))
                    (pseudo-termp hyp)
                    ok)
               (ctx-ev hyp (append (ctx-ev-alist new-alist a) a))))
    :hints (("goal" :do-not-induct t
             :use ((:instance ctx-ev-meta-extract-relieve-hyp
                    (bkptr (1+ n))))
             :in-theory (disable ctx-ev-meta-extract-relieve-hyp))))

  (defthm symbol-alistp-append
    (implies (and (symbol-alistp a1)
                  (symbol-alistp a2))
             (symbol-alistp (append a1 a2)))
    :hints(("Goal" :in-theory (enable symbol-alistp))))

  (defthm symbol-alistp-mx-relieve-hyp
    (implies (symbol-alistp alist)
             (symbol-alistp (mv-nth 1 (mx-relieve-hyp
                                       hyp alist rune target n mfc state)))))

  (defthm alistp-mx-relieve-hyp
    (implies (alistp alist)
             (alistp (mv-nth 1 (mx-relieve-hyp
                                       hyp alist rune target n mfc state)))))

  (defthm assoc-nil-of-mx-relieve-hyp
    (implies (not (assoc nil alist))
             (not (assoc nil (mv-nth 1 (mx-relieve-hyp
                                        hyp alist rune target n mfc state))))))

  (defthm pseudo-term-substp-mx-relieve-hyp
    (implies (pseudo-term-substp alist)
             (pseudo-term-substp (mv-nth 1 (mx-relieve-hyp
                                                hyp alist rune target n mfc
                                                state))))))


(defsection mx-relieve-hyps
  (defund mx-relieve-hyps (hyps alist rune target n mfc state)
    (declare (xargs :stobjs state
                    :guard (and (pseudo-term-listp hyps)
                                (symbol-alistp alist)
                                (natp n))))
    (b* (((when (atom hyps))
          (mv t alist))
         ((mv ok alist)
          (mx-relieve-hyp (car hyps) alist rune target n mfc state))
         ((unless ok) (mv nil alist)))
      (mx-relieve-hyps (cdr hyps) alist rune target (1+ n) mfc state)))

  (local (in-theory (enable mx-relieve-hyps)))

  (defthm alists-agree-of-cons
    (implies (and (alists-agree keys a b)
                  (not (member-equal x keys)))
             (alists-agree keys a (cons (cons x y) b)))
    :hints(("Goal" :in-theory (enable alists-agree))))

  (defthm sub-alistp-of-cons
    (implies (and (sub-alistp a b)
                  (not (hons-assoc-equal x a)))
             (sub-alistp a (cons (cons x y) b)))
    :hints(("Goal" :in-theory (enable sub-alistp))))

  (defthm alists-agree-transitive
    (implies (and (alists-agree keys1 a b)
                  (alists-agree keys2 b c)
                  (subsetp-equal keys1 keys2))
             (alists-agree keys1 a c))
    :hints(("Goal" :in-theory (enable alists-agree subsetp-equal
                                      alists-agree-hons-assoc-equal)
            :induct t)))
  (defthm alists-agree-implies-subsetp-keys
    (implies (and (alists-agree keys a b)
                  (subsetp-equal keys (alist-keys a)))
             (subsetp-equal keys (alist-keys b)))
    :hints(("Goal" :in-theory (enable alists-agree subsetp-equal alist-keys))))

  (defthm sub-alistp-transitive-1
    (implies (and (sub-alistp a b)
                  (sub-alistp b c))
             (sub-alistp a c))
    :hints(("Goal" :in-theory (e/d (sub-alistp)))))

  (defthm sub-alistp-transitive-2
    (implies (and (sub-alistp b c)
                  (sub-alistp a b))
             (sub-alistp a c))
    :hints(("Goal" :in-theory (e/d (sub-alistp)))))

  (defthm mx-relieve-hyps-alist-extension
    (sub-alistp alist
                (mv-nth 1 (mx-relieve-hyps
                           hyps alist rune target n mfc state))))

  (defthm symbol-alistp-mx-relieve-hyps
    (implies (symbol-alistp alist)
             (symbol-alistp (mv-nth 1 (mx-relieve-hyps
                                       hyps alist rune target n mfc state)))))

  (defthm alistp-mx-relieve-hyps
    (implies (alistp alist)
             (alistp (mv-nth 1 (mx-relieve-hyps
                                       hyps alist rune target n mfc state)))))

  (defthm pseudo-term-substp-mx-relieve-hyps
    (implies (pseudo-term-substp alist)
             (pseudo-term-substp (mv-nth 1 (mx-relieve-hyps
                                                hyps alist rune target n mfc
                                                state)))))

  (defthm all-vars-bound-when-sub-alistp
    (implies (and (all-keys-bound keys sub)
                  (not (member nil keys))
                  (sub-alistp sub sup))
             (all-keys-bound keys sup))
    :hints (("goal" :induct t
             :in-theory (enable all-keys-bound))
            (alist-reasoning)))

  (defthm-substitute-into-term-flag
    (defthm nil-not-member-simple-term-vars
      (not (member nil (simple-term-vars x)))
      :hints ('(:expand ((simple-term-vars x))))
      :flag substitute-into-term)
    (defthm nil-not-member-simple-term-vars-lst
      (not (member nil (simple-term-vars-lst x)))
      :hints ('(:expand ((simple-term-vars-lst x))))
      :flag substitute-into-list))

  (defthm all-vars-bound-when-sub-alistp-mx-relieve-hyps
    (implies (and (all-keys-bound keys alist)
                  (not (member nil keys)))
             (all-keys-bound keys
                             (mv-nth 1 (mx-relieve-hyps
                                        hyps alist rune target n mfc state))))
    :hints (("goal" :use ((:instance mx-relieve-hyps-alist-extension))
             :in-theory (disable mx-relieve-hyps-alist-extension))))

  (defthm mx-relieve-hyps-all-vars-bound
    (mv-let (ok new-alist)
      (mx-relieve-hyps hyps alist rune target n mfc state)
      (implies ok
               (all-keys-bound (simple-term-vars-lst hyps) new-alist)))
    :hints(("Goal" :in-theory (enable all-keys-bound
                                      simple-term-vars-lst))))

  (defthm hons-assoc-equal-ctx-ev-alist
    (implies (alistp x)
             (equal (hons-assoc-equal k (ctx-ev-alist x a))
                    (and (hons-assoc-equal k x)
                         (cons k (ctx-ev (cdr (hons-assoc-equal k x)) a)))))
    :hints(("Goal" :in-theory (enable ctx-ev-alist))))

  (defthm sub-alistp-ctx-ev-alist
    (implies (and (sub-alistp x y)
                  (alistp y) (alistp x))
             (sub-alistp (ctx-ev-alist x a) (ctx-ev-alist y a)))
    :hints ((alist-reasoning)))


  (defthm all-keys-bound-of-ctx-ev-alist
    (implies (all-keys-bound keys subst)
             (all-keys-bound keys (ctx-ev-alist subst a)))
    :hints(("Goal" :in-theory (enable all-keys-bound))))

  (defthm all-keys-bound-append-1
    (implies (all-keys-bound k a)
             (all-keys-bound k (append a b)))
    :hints(("Goal" :in-theory (enable all-keys-bound))))

  ;; (defthm sub-alistp-append-sub-alists
  ;;   (implies (sub-alistp a b)
  ;;            (sub-alistp (append a c)
  ;;                        (append b c)))
  ;;   :hints ((alist-reasoning)))

  (defthm ctx-ev-alist-extension-mx-relieve-hyps
    (implies (and (all-keys-bound (simple-term-vars x) alist)
                  (pseudo-termp x)
                  (alistp alist))
             (equal (ctx-ev x (append (ctx-ev-alist
                                       (mv-nth 1 (mx-relieve-hyps
                                                  hyps alist rune target n mfc
                                                  state))
                                       a)
                                      a))
                    (ctx-ev x (append (ctx-ev-alist alist a) a))))
    :hints(("Goal" :in-theory (disable mx-relieve-hyps
                                       ctx-ev-alist-extension-when-vars-bound)
            :use ((:instance ctx-ev-alist-extension-when-vars-bound
                   (b (ctx-ev-alist
                               (mv-nth 1 (mx-relieve-hyps
                                          hyps alist rune target n mfc
                                          state))
                               a))
                   (a (ctx-ev-alist alist a)))))))

  (defthm ctx-ev-alist-extension-mx-relieve-hyps1
    (implies (and (all-keys-bound (simple-term-vars x) alist)
                  (pseudo-termp x)
                  (alistp alist))
             (equal (ctx-ev x (ctx-ev-alist
                               (mv-nth 1 (mx-relieve-hyps
                                          hyps alist rune target n mfc
                                          state))
                               a))
                    (ctx-ev x (ctx-ev-alist alist a))))
    :hints(("Goal" :in-theory (disable mx-relieve-hyps
                                       ctx-ev-alist-extension-when-vars-bound)
            :use ((:instance ctx-ev-alist-extension-when-vars-bound
                   (b (ctx-ev-alist
                       (mv-nth 1 (mx-relieve-hyps
                                  hyps alist rune target n mfc
                                  state))
                       a))
                   (a (ctx-ev-alist alist a)))))))

  (defthm assoc-nil-of-mx-relieve-hyps
    (implies (not (assoc nil alist))
             (not (assoc nil (mv-nth 1 (mx-relieve-hyps
                                        hyps alist rune target n mfc state))))))

  (defthm ctx-ev-mx-relieve-hyps-correct
    (mv-let (ok new-alist)
      (mx-relieve-hyps hyps alist rune target n mfc state)
      (implies (and (ctx-ev-meta-extract-contextual-facts a)
                    (ctx-ev-meta-extract-global-facts)
                    (not (assoc nil alist))
                    (alistp alist)
                    (pseudo-term-listp hyps)
                    ok)
               (ctx-ev (conjoin hyps) (append (ctx-ev-alist new-alist a) a))))
    :hints (("goal" :induct (mx-relieve-hyps hyps alist rune target n mfc
                                             state))
            (and stable-under-simplificationp
                 '(:in-theory (enable ctx-ev-conjoin-when-consp)))))

  (defthm all-keys-bound-of-conjoin
    (implies (all-keys-bound (simple-term-vars-lst hyps) a)
             (all-keys-bound (simple-term-vars (conjoin hyps)) a))
    :hints(("Goal" :in-theory (enable conjoin all-keys-bound
                                      simple-term-vars-lst
                                      simple-term-vars))))

  (defthm ctx-ev-mx-relieve-hyps-correct1
    (mv-let (ok new-alist)
      (mx-relieve-hyps hyps alist rune target n mfc state)
      (implies (and (ctx-ev-meta-extract-contextual-facts a)
                    (ctx-ev-meta-extract-global-facts)
                    (not (assoc nil alist))
                    (alistp alist)
                    (pseudo-term-listp hyps)
                    ok)
               (ctx-ev (conjoin hyps) (ctx-ev-alist new-alist a))))
    :hints (("goal" :use ((:instance ctx-ev-mx-relieve-hyps-correct))
             :in-theory (disable ctx-ev-mx-relieve-hyps-correct)))))







;; (def-functional-instance
;;   ctx-ev-substitute-into-term
;;   substitute-into-term-correct
;;   ((unify-ev ctx-ev)
;;    (unify-ev-lst ctx-ev-lst)
;;    (unify-ev-alist ctx-ev-alist))
;;   :hints ((and stable-under-simplificationp
;;                '(:use ctx-ev-of-fncall-args))))

;; (def-functional-instance
;;   ctx-ev-simple-one-way-unify-usage
;;   simple-one-way-unify-usage
;;   ((unify-ev ctx-ev)
;;    (unify-ev-lst ctx-ev-lst)
;;    (unify-ev-alist ctx-ev-alist))
;;   :hints ((and stable-under-simplificationp
;;                '(:use ctx-ev-of-fncall-args))))

;; (defthm ctx-ev-simple-one-way-unify-usage-rev
;;   (mv-let (ok subst)
;;     (simple-one-way-unify template term alist)
;;     (implies (and ok
;;                   (pseudo-termp term)
;;                   (pseudo-termp template))
;;              (equal (ctx-ev template (ctx-ev-alist subst a))
;;                     (ctx-ev term a)))))

;; (in-theory (disable ctx-ev-simple-one-way-unify-usage-rev))



;; (defthm conjoin-of-termlist-subst
;;   (implies (and (pseudo-term-listp x)
;;                 (not (assoc nil subst)))
;;            (iff (ctx-ev (conjoin (termlist-subst x subst)) a)
;;                 (ctx-ev (sublis-var subst (conjoin x)) a)))
;;   :hints(("Goal" :in-theory (enable termlist-subst term-subst)
;;           :expand ((termlist-subst x subst)
;;                    (conjoin x))
;;           :induct (len x))))



;; (defthm ctx-ev-mfc-relieve-hyps-correct-lemma
;;   (implies (and (ctx-ev-meta-extract-contextual-facts a)
;;                 (not (assoc nil alist))
;;                 (pseudo-term-listp hyps)
;;                 (mfc-relieve-hyps hyps alist rune target n mfc state))
;;            (ctx-ev (sublis-var alist (conjoin hyps)) a))
;;   :hints (("goal" :induct t :do-not-induct t)
;;           (and stable-under-simplificationp
;;                '(:in-theory (e/d (ctx-ev-conjoin-when-consp)
;;                                  (ctx-ev-meta-extract-relieve-hyp))
;;                  :use ((:instance ctx-ev-meta-extract-relieve-hyp
;;                         (hyp (car hyps)) (bkptr (+ 1 n))))))))

;; (defthm ctx-ev-mfc-relieve-hyps-correct
;;   (implies (and (ctx-ev-meta-extract-contextual-facts a)
;;                 (not (assoc nil alist))
;;                 (pseudo-term-listp hyps)
;;                 (mfc-relieve-hyps hyps alist rune target n mfc state))
;;            (ctx-ev (conjoin hyps) (append (ctx-ev-alist alist a) a)))
;;   :hints (("goal" :induct t :do-not-induct t)
;;           (and stable-under-simplificationp
;;                '(:in-theory (e/d (ctx-ev-conjoin-when-consp)
;;                                  (ctx-ev-meta-extract-relieve-hyp))
;;                  :use ((:instance ctx-ev-meta-extract-relieve-hyp
;;                         (hyp (car hyps)) (bkptr (+ 1 n))))))))

;; (defthm mfc-relieve-hyps-correct
;;   (implies (and (pseudo-term-listp hyps)
;;                 (ctx-ev-meta-extract-contextual-facts a)
;;                 (mfc-relieve-hyps hyps alist rune target n mfc state))
;;            (ctx-ev (conjoin hyps)
;;                    (append (ctx-ev-alist alist a) a)))
;;   :hints (("goal" :use mfc-relieve-hyps-correct-lemma
;;            :in-theory (disable mfc-relieve-hyps-correct-lemma))))

(local (defthm assoc-of-append
         (implies x
                  (equal (assoc x (append a b))
                         (or (assoc x a)
                             (assoc x b))))))

(defthm-substitute-into-term-flag
  (defthm ctx-ev-append-when-all-keys-bound
    (implies (and (pseudo-termp x)
                  (all-keys-bound (simple-term-vars x) a))
             (equal (ctx-ev x (append a b))
                    (ctx-ev x a)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ctx-ev-of-fncall-args))))
    :flag substitute-into-term)
  (defthm ctx-ev-lst-when-all-keys-bound
    (implies (and (pseudo-term-listp x)
                  (all-keys-bound (simple-term-vars-lst x) a))
             (equal (ctx-ev-lst x (append a b))
                    (ctx-ev-lst x a)))
    :flag substitute-into-list))

(local (defthm subsetp-of-union
         (subsetp-equal a (union-equal a b))))

(defthm simple-term-vars-of-conjoin
  (subsetp-equal (simple-term-vars (conjoin x))
                 (simple-term-vars-lst x))
  :hints(("Goal" :in-theory (enable conjoin
                                    simple-term-vars-lst
                                    simple-term-vars))))

(defthm all-keys-bound-when-subsetp
  (implies (and (subsetp-equal a b)
                (all-keys-bound b alist))
           (all-keys-bound a alist))
  :hints(("Goal" :in-theory (enable subsetp-equal all-keys-bound))))





;; (defthm ctx-ev-mfc-relieve-hyps-correct-all-keys
;;   (implies (and (pseudo-term-listp hyps)
;;                 (not (assoc nil alist))
;;                 (ctx-ev-meta-extract-contextual-facts a)
;;                 (mfc-relieve-hyps hyps alist rune target n mfc state)
;;                 (all-keys-bound (simple-term-vars-lst hyps) alist))
;;            (ctx-ev (conjoin hyps)
;;                    (ctx-ev-alist alist a)))
;;   :hints (("goal" :use (ctx-ev-mfc-relieve-hyps-correct-lemma
;;                         (:instance simple-term-vars-of-conjoin
;;                          (x hyps)))
;;            :in-theory (e/d ()
;;                            (ctx-ev-mfc-relieve-hyps-correct-lemma
;;                             ctx-ev-mfc-relieve-hyps-correct
;;                             simple-term-vars-of-conjoin)))))

;; (in-theory (disable mfc-relieve-hyps))


(defthm unify-const-nil-not-bound
  (mv-let (unified subst)
    (unify-const pat const alist)
    (implies (and (not (assoc nil alist))
                  unified)
             (not (assoc nil subst))))
  :hints(("Goal" :in-theory (enable unify-const))))

(defthm-simple-one-way-unify-flag
  (defthm simple-one-way-unify-nil-not-bound
    (mv-let (unified subst)
      (simple-one-way-unify pat term alist)
      (implies (and (not (assoc nil alist))
                    unified)
             (not (assoc nil subst))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))))
    :flag simple-one-way-unify)
  (defthm simple-one-way-unify-lst-nil-not-bound
    (mv-let (unified subst)
      (simple-one-way-unify-lst pat term alist)
      (implies (and (not (assoc nil alist))
                    unified)
             (not (assoc nil subst))))
    :hints ('(:expand ((simple-one-way-unify-lst pat term alist))))
    :flag simple-one-way-unify-lst))

(defthm symbol-alistp-unify-const
  (mv-let (unified subst)
    (unify-const pat const alist)
    (implies (and (symbol-alistp alist)
                  (pseudo-termp pat)
                  unified)
             (symbol-alistp subst)))
  :hints(("Goal" :in-theory (enable unify-const symbol-alistp))))

(defthm-simple-one-way-unify-flag
  (defthm simple-one-way-unify-symbol-alistp
    (mv-let (unified subst)
      (simple-one-way-unify pat term alist)
      (implies (and (symbol-alistp alist)
                    (pseudo-termp pat)
                    unified)
               (symbol-alistp subst)))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))
              :in-theory (enable symbol-alistp)))
    :flag simple-one-way-unify)
  (defthm simple-one-way-unify-lst-symbol-alistp
    (mv-let (unified subst)
      (simple-one-way-unify-lst pat term alist)
      (implies (and (symbol-alistp alist)
                    (pseudo-term-listp pat)
                    unified)
               (symbol-alistp subst)))
    :hints ('(:expand ((simple-one-way-unify-lst pat term alist))))
    :flag simple-one-way-unify-lst))



(defun mfc-apply-rewrite-rule (rule rune term mfc state)
  (declare (xargs :guard (pseudo-termp term)
                  :stobjs state))
  (b* (((mv class hyps equiv lhs rhs)
        (ec-call (rewrite-rule-parts rule)))
       ((when (not (and (pseudo-term-listp hyps)
                        (pseudo-termp lhs)
                        (pseudo-termp rhs)
                        (symbolp equiv)
                        (not (eq class 'meta)))))
        (mv nil term))
       ((mv unify-ok subst)
        (simple-one-way-unify lhs term nil))
       ((unless unify-ok)
        (mv nil term))
       (rhs-vars (simple-term-vars rhs))
       ((mv ok subst) (mx-relieve-hyps hyps subst rune term 0 mfc state))
       ;; don't allow free variables in rhs after hyps
       ((unless (ec-call (all-keys-bound rhs-vars subst)))
        (mv nil term))
       ((unless ok)
        (mv nil term)))
    (mv t (substitute-into-term rhs subst))))



(defthm mfc-apply-rewrite-rule-correct
  (implies (and (ctx-ev-meta-extract-contextual-facts a)
                (ctx-ev-meta-extract-global-facts)
                (ctx-ev-theoremp (rewrite-rule-term rule))
                (equal (access rewrite-rule rule :equiv) 'equal)
                (pseudo-termp term))
           (equal (ctx-ev (mv-nth 1 (mfc-apply-rewrite-rule rule rune term mfc state)) a)
                  (ctx-ev term a)))
  :hints (("goal" :use ((:instance ctx-ev-falsify
                         (x (rewrite-rule-term rule))
                         (a (append (ctx-ev-alist
                                     (mv-nth 1
                                             (mx-relieve-hyps
                                              (mv-nth 1 (rewrite-rule-parts rule))
                                              (mv-nth 1 (simple-one-way-unify
                                                (mv-nth 3 (rewrite-rule-parts rule))
                                                term nil))
                                              rune
                                              term 0 mfc state))
                                     a)
                                    a))))
           :in-theory (disable symbol-alistp alistp-of-cdr))))





(in-theory (disable mfc-apply-rewrite-rule))



(defun all-identities-except-x (x alist)
  (declare (xargs :guard t))
  (if (atom alist)
      t
    (and (or (atom (car alist))
             (equal (caar alist) x)
             (equal (caar alist) (cdar alist)))
         (all-identities-except-x x (cdr alist)))))

(defun find-non-identity (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      nil
    (if (or (atom (car alist))
            (equal (caar alist) (cdar alist)))
        (find-non-identity (cdr alist))
      (caar alist))))



;; (defthm consp-assoc-equal-when-nonnil
;;   (implies var
;;            (iff (consp (assoc-equal var alist))
;;                 (assoc-equal var alist))))

(defthm pseudo-termp-hons-assoc
  (implies (pseudo-term-substp x)
           (pseudo-termp (cdr (hons-assoc-equal k x))))
  :hints(("Goal" :in-theory (enable pseudo-term-substp))))



(mutual-recursion
 (defun subtermp (sub x)
   (declare (xargs :guard (pseudo-termp x)))
   (cond ((equal x sub) t)
         ((or (variablep x) (fquotep x)) nil)
         (t (subtermp-in-list sub (cdr x)))))
 (defun subtermp-in-list (sub x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (endp x)
       nil
     (or (subtermp sub (car x))
         (subtermp-in-list sub (cdr x))))))

;; This is the core of the contextual rewriting system.

;; returns (mv success new-term)
(defun try-context-rw (term rule rune mfc state)
  (declare (xargs :stobjs state
                  :guard (pseudo-termp term)))
  ;; The rule should be an EQUAL rewrite rule, (equal lhs rhs) where lhs can
  ;; unify with rhs with only a single rhs variable (VAR) substituted for
  ;; something other than itself.  E.g., (equal (foo (bar y x) y (bar y x))
  ;; (foo x y x)) is ok for var = X, but (equal (foo (bar x) (baz y) (bar x))
  ;; (foo x y x)) is not because y and x both have non-identity substitutions.
  ;; In our running example, term is (bar w (baz z)), formula is (equal (bar y
  ;; (foo y x)) (bar y x)), var is x, and we assume that (foo w (baz z))
  ;; rewrites to (foo w z).
  (b* (((mv class hyps equiv lhs rhs)
        (ec-call (rewrite-rule-parts rule)))
       ((unless (and (eq equiv 'equal)
                     (pseudo-term-listp hyps)
                     (pseudo-termp lhs)
                     (pseudo-termp rhs)
                     (not (eq class 'meta))))
        (mv nil term))
       ;; this should be all identities except VAR.  Unify the RHS (base term)
       ;; with the LHS (term with context inserted) so that we can find whcih
       ;; variable has context inserted.
       ((mv ok lhs-subst) (simple-one-way-unify rhs lhs nil))
       ;; '((x . (foo y x)) (y . y))
       ((unless ok) (mv nil term))
       (var (find-non-identity lhs-subst))
       ((unless (and var (symbolp var)
                     (all-identities-except-x var lhs-subst)))
        (mv nil term))
       (ctx-term (cdr (assoc var lhs-subst))) ;; (foo y x)
       ;; Now var is the variable and ctx-term is the context for that
       ;; variable.
       ;; Unify the term we're rewriting with the RHS to find the subterm
       ;; corresponding to the variable.
       ((mv ok term-subst) (simple-one-way-unify rhs term nil))
       ;; '((x . (baz z)) (y . w))
       ((unless ok) (mv nil term))
       ((mv ok term-subst)
        (mx-relieve-hyps hyps term-subst rune term 0 mfc state))

       ((unless ok) (mv nil term))
       ;; Relieve the hyps...
       ((unless ;; We don't yet bind free variables -- maybe soon
            (all-keys-bound (simple-term-vars ctx-term) term-subst))
        (mv nil term))
       ;; Now rewrite the context term under the substitution alist.
       (ctx-rw (mfc-rw+ ctx-term term-subst '? nil mfc state :forcep nil))
       ((unless (pseudo-termp ctx-rw))
        (mv nil term))
       ;; (foo y x) under '((x . (baz z)) (y . w)) = (foo w (baz z)) => (foo w z)
       ((mv no-change &) (simple-one-way-unify ctx-term ctx-rw term-subst))
       ;; The above just checks to see if ctx-term under term-subst equals
       ;; ctx-rw, i.e. there was no change.
       ((when no-change)
        ;; the rewriter didn't simplify anything
        (mv nil term))
       ;; Additionally, we want to make sure that the added context actually
       ;; causes some simplification of the subterm that we applied it to.
       ;; In particular, we'll require that the subterm bound to the variable
       ;; doesn't appear (identically) inside the ctx-rw result.
       ((when (subtermp (cdr (assoc var term-subst)) ctx-rw))
        (mv nil term))

       ;; at this point we have:
       ;; term = (bar w (baz z))
       ;; lhs = (bar y (foo y x))
       ;; rhs = (bar y x)
       ;; var = x
       ;; ctx-term = (foo y x)
       ;; term-subst = ((x . (baz z)) (y . w))
       ;; ctx-rw = (foo w z)

       ;; If we just do this:
       (new-term (substitute-into-term
                  rhs (cons (cons var ctx-rw) term-subst)))
       ;; we end up with (bar w (foo w z)).  This is maybe ok since it will
       ;; rewrite to (bar w (foo w z)) under normal rewriting with the rule
       ;; we've just used backwards.  But perhaps we can do better?  If this
       ;; unifies with the LHS (as it does in this case), then we can undo the
       ;; rewrite (by applying the rule, as below).  Should we?  Not sure.
       ((mv & new-term-rw)
        (mfc-apply-rewrite-rule rule rune new-term mfc state))
       )
    ;; (bar y x) under '((x . (foo w z)) (y . w)) => (bar w (foo w z))
    (mv t new-term-rw)))



(defthm assoc-when-all-identities-except-x
  (implies (and (all-identities-except-x var subst)
                (not (equal x var))
                (hons-assoc-equal x subst))
           (equal (cdr (hons-assoc-equal x subst)) x)))

(defthm-substitute-into-term-flag
  (defthm ctx-ev-when-all-identities-except-x
    (implies (and (pseudo-termp x)
                  (all-keys-bound (simple-term-vars x) subst)
                  (all-identities-except-x var subst))
             (equal (ctx-ev x (cons (cons var x1)
                                    (ctx-ev-alist subst a)))
                    (ctx-ev x (cons (cons var x1) a))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ctx-ev-of-fncall-args
                                      all-keys-bound)
                   :expand ((simple-term-vars x)))))
    :flag substitute-into-term)
  (defthm ctx-ev-lst-when-all-identities-except-x
    (implies (and (pseudo-term-listp x)
                  (all-keys-bound (simple-term-vars-lst x) subst)
                  (all-identities-except-x var subst))
             (equal (ctx-ev-lst x (cons (cons var x1)
                                        (ctx-ev-alist subst a)))
                    (ctx-ev-lst x (cons (cons var x1) a))))
    :hints ('(:expand ((simple-term-vars-lst x))))
    :flag substitute-into-list))



(defthm-substitute-into-term-flag
  (defthm ctx-ev-cons-redundant-value
    (implies (and (pseudo-termp x)
                  (equal val (cdr (hons-assoc-equal var a))))
             (equal (ctx-ev x (cons (cons var val) a))
                    (ctx-ev x a)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ctx-ev-of-fncall-args))))
    :flag substitute-into-term)
  (defthm ctx-ev-lst-cons-redundant-value
    (implies (and (pseudo-term-listp x)
                  (equal val (cdr (hons-assoc-equal var a))))
             (equal (ctx-ev-lst x (cons (cons var val) a))
                    (ctx-ev-lst x a)))
    :flag substitute-into-list))




(defthm unify-const-reduce-when-all-keys-bound
  (mv-let (ok subst)
    (unify-const pat x alist)
    (implies (and ok
                  (all-keys-bound (simple-term-vars pat) alist))
             (equal subst alist)))
  :hints(("Goal" :in-theory (enable unify-const all-keys-bound
                                    simple-term-vars-lst)
          :expand ((simple-term-vars pat)))))


(defthm-simple-one-way-unify-flag
  (defthm one-way-unify-reduce-when-all-keys-bound
    (mv-let (ok subst)
      (simple-one-way-unify pat x alist)
      (implies (and ok
                    (all-keys-bound (simple-term-vars pat) alist))
               (equal subst alist)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x) (simple-one-way-unify pat x alist))
                            (:free (x) (simple-one-way-unify nil x alist))
                            (simple-term-vars pat))
                   :in-theory (enable all-keys-bound))))
    :flag simple-one-way-unify)
  (defthm one-way-unify-lst-reduce-when-all-keys-bound
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat x alist)
      (implies (and ok
                    (all-keys-bound (simple-term-vars-lst pat) alist))
               (equal subst alist)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x) (simple-one-way-unify-lst pat x alist))
                            (simple-term-vars-lst pat)))))
    :flag simple-one-way-unify-lst)
  :hints (("goal" :induct (simple-one-way-unify-flag flag pat x alist))))







(defthm sub-alistp-of-unify-const
  (mv-let (ok subst)
    (unify-const pat x subst0)
    (implies ok
             (sub-alistp subst0 subst)))
  :hints(("Goal" :in-theory (enable unify-const))))

(defthm-simple-one-way-unify-flag
  (defthm sub-alistp-of-one-way-unify
    (mv-let (ok subst)
      (simple-one-way-unify pat x subst0)
      (implies ok
               (sub-alistp subst0 subst)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify pat x subst)))
                   :in-theory (enable all-keys-bound))))
    :flag simple-one-way-unify)
  (defthm sub-alistp-of-one-way-unify-lst
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat x subst0)
      (implies ok
               (sub-alistp subst0 subst)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify-lst pat x subst))))))
    :flag simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat x subst0))))

(encapsulate nil
  (local (defthm equal-of-len
           (equal (equal (len x) n)
                  (if (zp n)
                      (and (equal n 0)
                           (not (consp x)))
                    (and (consp x)
                         (equal (len (cdr x)) (1- n)))))))
  (local (in-theory (disable len)))
  (defthm alist-keys-of-unify-const
    (mv-let (ok subst)
      (unify-const pat x subst0)
      (implies ok
               (set-equiv (alist-keys subst)
                           (append (simple-term-vars pat)
                                   (alist-keys subst0)))))
    :hints(("Goal" :in-theory (enable unify-const simple-term-vars
                                      simple-term-vars-lst)
            :induct t))))

(defthm-simple-one-way-unify-flag
  (defthm alist-keys-of-simple-one-way-unify
    (mv-let (ok subst)
      (simple-one-way-unify pat x subst0)
      (implies ok
               (set-equiv (alist-keys subst)
                           (append (simple-term-vars pat)
                                   (alist-keys subst0)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify pat x subst))
                            (simple-term-vars pat))
                   :in-theory (enable all-keys-bound))))
    :flag simple-one-way-unify)
  (defthm alist-keys-of-simple-one-way-unify-lst
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat x subst0)
      (implies ok
               (set-equiv (alist-keys subst)
                           (append (simple-term-vars-lst pat)
                                   (alist-keys subst0)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify-lst pat x subst))
                            (simple-term-vars-lst pat)))))
    :flag simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat x subst0))))

(defthm alist-keys-subsetp-equal
  (implies (and (subsetp-equal keys1 keys2)
                (alists-agree keys2 a b))
           (alists-agree keys1 a b))
  :hints(("Goal" :in-theory (enable subsetp-equal alists-agree))))

(defcong set-equiv equal (alists-agree keys al1 al2) 1
  :hints(("Goal" :in-theory (enable set-equiv)
          :cases ((alists-agree keys al1 al2)))))



;; (defthm alists-compatible-nil
;;   (alists-compatible nil x)
;;   :hints(("Goal" :in-theory (enable alists-compatible-in-terms-of-alists-agree
;;                                     intersection-equal
;;                                     alists-agree))))

;; (defthm alists-compatible-self
;;   (alists-compatible x x)
;;   :hints(("Goal" :in-theory (enable alists-compatible-iff-agree-on-bad-guy))))

(local (in-theory (enable alists-compatible-sym)))

;; (defthm alists-compatible-commute
;;   (iff (alists-compatible b a)
;;        (alists-compatible a b))
;;   :hints ((alist-reasoning)))

(defthm alists-compatible-when-sub-alistp
  (implies (sub-alistp a b)
           (and (alists-compatible a b)
                (alists-compatible b a)))
  :hints ((alist-reasoning)))

(defthm alists-compatible-of-one-way-unify
  (mv-let (ok subst)
    (simple-one-way-unify pat x subst0)
    (implies ok
             (and (alists-compatible subst0 subst)
                  (alists-compatible subst subst0)))))

(defthm not-alists-compatible-append-2
  (implies (and (not (alists-compatible a b))
                (alists-compatible b c))
           (not (alists-compatible a (append c b))))
  :hints ((alist-reasoning)))

(defthm alists-compatible-of-one-way-unify-lst
  (mv-let (ok subst)
    (simple-one-way-unify-lst pat x subst0)
    (implies ok
             (and (alists-compatible subst0 subst)
                  (alists-compatible subst subst0)))))


(defcong alist-equiv equal (alists-compatible a b) 1
  :hints (("goal" :cases ((alists-compatible a b)))
          (alist-reasoning)))

(defcong alist-equiv equal (alists-compatible a b) 2
  :hints (("goal" :cases ((alists-compatible a b)))
          (alist-reasoning)))



(defun unify-const-redef (pat const)
  (cond ((atom pat)
         (if (and pat (symbolp pat))
             (mv t (list (cons pat (kwote const))))
           (if (eq const nil)
               (mv t nil)
             (mv nil nil))))
        ((eq (car pat) 'quote)
         (mv (equal (unquote pat) const) nil))
        ((and (eq (car pat) 'cons)
              (int= (len pat) 3))
         (if (consp const)
             (b* (((mv car-ok car-alist)
                   (unify-const-redef (second pat) (car const)))
                  ((unless car-ok) (mv nil nil))
                  ((mv cdr-ok cdr-alist)
                   (unify-const-redef (third pat) (cdr const)))
                  ((unless (and cdr-ok
                                (alists-compatible cdr-alist car-alist)))
                   (mv nil nil)))
               (mv t (append cdr-alist car-alist)))
           (mv nil nil)))
        ((and (eq (car pat) 'binary-+)
              (int= (len pat) 3))
         (cond ((not (acl2-numberp const))
                (mv nil nil))
               ((quotep (second pat))
                (let ((num (unquote (second pat))))
                  (if (acl2-numberp num)
                      (unify-const-redef (third pat) (- const num))
                    (mv nil nil))))
               ((quotep (third pat))
                (let ((num (unquote (third pat))))
                  (if (acl2-numberp num)
                      (unify-const-redef (second pat) (- const num))
                    (mv nil nil))))
               (t (mv nil nil))))
        (t (mv nil nil))))

(local (defthm hons-assoc-equal-nil
         (equal (hons-assoc-equal x nil) nil)))

(local (defthm hons-assoc-equal-cons
         (equal (hons-assoc-equal x (cons a b))
                (or (and (consp a) (equal x (car a)) a)
                    (hons-assoc-equal x b)))))

(defthm unify-const-is-redef
  (mv-let (ok subst)
    (unify-const pat x subst0)
    (mv-let (okr substr)
      (unify-const-redef pat x)
      (and (iff ok
                (and okr
                     (alists-compatible substr subst0)))
           (implies ok
                    (alist-equiv subst (append substr subst0))))))
  :hints (("goal" :induct (unify-const pat x subst0)
           :in-theory (e/d ((:induction unify-const))
                           (pseudo-termp
                            unify-const-redef
                            set::double-containment
                            default-car default-cdr
                            append len hons-assoc-equal
                            alists-compatible-when-sub-alistp
                            unify-const-reduce-when-all-keys-bound)))
          (and stable-under-simplificationp
               '(:expand ((:free (x subst)
                           (unify-const pat x subst))
                          (:free (x subst)
                           (unify-const nil x subst))
                          (:free (x)
                           (unify-const-redef pat x))
                          (:free (x)
                           (unify-const-redef nil x)))))
          (alist-reasoning)))

(defthm pseudo-term-substp-of-unify-const-redef
  (implies (pseudo-termp pat)
           (pseudo-term-substp (mv-nth 1 (unify-const-redef pat const)))))

(in-theory (disable unify-const-redef))

(mutual-recursion
 (defun one-way-unify-redef (pat term)
   (cond ((atom pat)
          (if (and pat (symbolp pat))
              (mv t (list (cons pat term)))
            (mv (or (eq term nil)
                    (equal term *nil*))
                nil)))
         ((atom term)
          (mv nil nil))
         ((eq (car pat) 'quote)
          (mv (equal pat term) nil))
         ((eq (car term) 'quote)
          (unify-const pat (unquote term) nil))
         ((equal (car pat) (car term))
          (one-way-unify-redef-lst (cdr pat) (cdr term)))
         (t (mv nil nil))))
 (defun one-way-unify-redef-lst (pat term)
   (if (atom pat)
       (if (atom term)
           (mv t nil)
         (mv nil nil))
     (if (atom term)
         (mv nil nil)
       (mv-let (ok alist)
         (one-way-unify-redef (car pat) (car term))
         (if ok
             (mv-let (ok alist2)
               (one-way-unify-redef-lst (cdr pat) (cdr term))
               (if (and ok (alists-compatible alist2 alist))
                   (mv t (append alist2 alist))
                 (mv nil nil)))
           (mv nil nil)))))))


(defthm-simple-one-way-unify-flag
  (defthm one-way-unify-is-redef
    (mv-let (ok subst)
      (simple-one-way-unify pat x subst0)
      (mv-let (okr substr)
        (one-way-unify-redef pat x)
        (and (iff ok
                  (and okr
                       (alists-compatible substr subst0)))
             (implies ok
                      (alist-equiv subst (append substr subst0))))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify pat x subst))
                            (:free (x subst)
                             (simple-one-way-unify nil x subst))
                            (:free (x)
                             (one-way-unify-redef pat x)))))
            (alist-reasoning))
    :flag simple-one-way-unify)
  (defthm one-way-unify-lst-is-redef
    (mv-let (ok subst)
      (simple-one-way-unify-lst pat x subst0)
      (mv-let (okr substr)
        (one-way-unify-redef-lst pat x)
        (and (iff ok
                  (and okr
                       (alists-compatible substr subst0)))
             (implies ok
                      (alist-equiv subst (append substr subst0))))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (x subst)
                             (simple-one-way-unify-lst pat x subst))
                            (:free (x)
                             (one-way-unify-redef-lst pat x)))))
            (alist-reasoning))
    :flag simple-one-way-unify-lst)
  :hints (("Goal" :induct (simple-one-way-unify-flag flag pat x subst0))))

(defthm one-way-unify-of-self-lemma
  (mv-let (ok1 subst1)
    (simple-one-way-unify pat x subst0)
    (mv-let (ok2 subst2)
      (simple-one-way-unify pat x subst1)
      (declare (ignore subst2))
      (implies ok1
               ok2))))


(in-theory (disable one-way-unify-is-redef
                    one-way-unify-lst-is-redef
                    unify-const-is-redef))



(encapsulate nil
  (local
   (defun subst-ind (flg pat term)
     (if flg
         (cond ((or (null pat)
                    (atom pat)
                    (atom term)
                    (eq (car pat) 'quote)
                    (not (equal (car pat) (car term))))
                (list pat term))
               (t (subst-ind nil (cdr pat) (cdr term))))
       (if (or (atom pat) (atom term))
           (list pat term)
         (list (subst-ind t (car pat) (car term))
               (subst-ind nil (cdr pat) (cdr term)))))))


  (encapsulate nil
    (local (defthm equal-of-len
             (implies (syntaxp (quotep n))
                      (equal (equal (len x) n)
                             (if (zp n)
                                 (and (equal n 0)
                                      (not (consp x)))
                               (and (consp x)
                                    (equal (len (cdr x)) (1- n))))))))
    (local (in-theory (disable len)))

    (defthm unify-const-single-var-unify-lemma
      (implies (and (all-keys-bound (simple-term-vars pat) alist)
                    (mv-nth 0 (unify-const pat const alist))
                    (all-identities-except-x var alist)
                    (pseudo-termp pat))
               (equal (ctx-ev
                       pat
                       (cons (cons var (ctx-ev
                                        (cdr (hons-assoc-equal var alist))
                                        (ctx-ev-alist subst a)))
                             (ctx-ev-alist subst a)))
                      const))
      :hints(("Goal" :in-theory (enable unify-const
                                        simple-term-vars
                                        simple-term-vars-lst
                                        all-keys-bound)))))


  (defthm-simple-one-way-unify-flag
    (defthm substitute-into-single-var-unify-term-lemma
      (implies (and (all-keys-bound (simple-term-vars pat) alist)
                    (mv-nth 0 (simple-one-way-unify pat term alist))
                    (all-identities-except-x var alist)
                    (pseudo-termp pat)
                    (pseudo-termp term))
               (equal (ctx-ev
                       pat
                       (cons (cons var (ctx-ev
                                        (cdr (hons-assoc-equal var alist))
                                        (ctx-ev-alist subst a)))
                             (ctx-ev-alist subst a)))
                      (ctx-ev term (ctx-ev-alist subst a))))
      :hints ('(:do-not-induct t
                :expand ((:free (term) (simple-one-way-unify pat term alist))
                         (simple-term-vars pat)))
              (and stable-under-simplificationp
                   '(:in-theory (enable ctx-ev-of-fncall-args all-keys-bound))))
      :flag simple-one-way-unify)
    (defthm substitute-into-single-var-unify-list-lemma
      (implies (and (all-keys-bound (simple-term-vars-lst pat) alist)
                    (mv-nth 0 (simple-one-way-unify-lst pat term alist))
                    (all-identities-except-x var alist)
                    (pseudo-term-listp pat)
                    (pseudo-term-listp term))
               (equal (ctx-ev-lst
                       pat
                       (cons (cons var (ctx-ev
                                        (cdr (hons-assoc-equal var alist))
                                        (ctx-ev-alist subst a)))
                             (ctx-ev-alist subst a)))
                      (ctx-ev-lst term (ctx-ev-alist subst a))))
      :hints ('(:expand ((:free (term) (simple-one-way-unify-lst nil term
                                                                 alist))
                         (:free (term) (simple-one-way-unify-lst pat term
                                                                 alist))
                         (simple-term-vars-lst pat))
                :in-theory (enable ctx-ev-alist)))
      :flag simple-one-way-unify-lst)))

  ;; (local (defthm substitute-into-single-var-unify-term-lemma
  ;;          (if flg
  ;;              (implies (and (all-keys-bound (simple-term-vars pat) alist)
  ;;                            (mv-nth 0 (simple-one-way-unify pat term alist))
  ;;                            (all-identities-except-x var alist)
  ;;                            (pseudo-termp pat)
  ;;                            (pseudo-termp term))
  ;;                       (equal (ctx-ev
  ;;                               pat
  ;;                               (cons (cons var (ctx-ev
  ;;                                                (cdr (hons-assoc-equal var alist))
  ;;                                                (ctx-ev-alist subst a)))
  ;;                                     (ctx-ev-alist subst a)))
  ;;                              (ctx-ev term (ctx-ev-alist subst a))))
  ;;            (implies (and (all-keys-bound (simple-term-vars-lst pat) alist)
  ;;                          (mv-nth 0 (simple-one-way-unify-lst pat term alist))
  ;;                          (all-identities-except-x var alist)
  ;;                          (pseudo-term-listp pat)
  ;;                          (pseudo-term-listp term))
  ;;                     (equal (ctx-ev-lst
  ;;                             pat
  ;;                             (cons (cons var (ctx-ev
  ;;                                                (cdr (hons-assoc-equal var alist))
  ;;                                                (ctx-ev-alist subst a)))
  ;;                                     (ctx-ev-alist subst a)))
  ;;                            (ctx-ev-lst term (ctx-ev-alist subst a)))))
  ;;          :hints (("goal" :induct (subst-ind flg pat term))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:expand ((simple-one-way-unify-lst pat term alist)
  ;;                                  (substitute-into-list term subst)
  ;;                                  (:free (subst) (substitute-into-list pat subst))
  ;;                                  (:free (term) (simple-one-way-unify pat term alist))
  ;;                                  (simple-one-way-unify nil term alist)
  ;;                                  (substitute-into-term term subst)
  ;;                                  (:free (subst) (substitute-into-term pat
  ;;                                                                       subst)))))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:in-theory (enable ctx-ev-of-fncall-args))))
  ;;          :rule-classes nil))

  ;; (defthm substitute-into-single-var-unify-term
  ;;   (implies (and (all-keys-bound (simple-term-vars pat) alist)
  ;;                 (mv-nth 0 (simple-one-way-unify pat term alist))
  ;;                 (all-identities-except-x var alist)
  ;;                 (pseudo-)
  ;;            (equal (substitute-into-term
  ;;                    pat
  ;;                    (cons (cons var (substitute-into-term
  ;;                                     (cdr (hons-assoc-equal var alist))
  ;;                                     subst))
  ;;                          subst))
  ;;                   (substitute-into-term term subst)))
  ;;   :hints (("goal" :use ((:instance substitute-into-single-var-unify-term-lemma
  ;;                          (flg t)))))))



;; (encapsulate nil
;;   (local
;;    (defun subst-ind (flg pat term)
;;      (if flg
;;          (cond ((or (null pat)
;;                     (atom pat)
;;                     (atom term)
;;                     (eq (car pat) 'quote)
;;                     (not (equal (car pat) (car term))))
;;                 (list pat term))
;;                (t (subst-ind nil (cdr pat) (cdr term))))
;;        (if (or (atom pat) (atom term))
;;            (list pat term)
;;          (list (subst-ind t (car pat) (car term))
;;                (subst-ind nil (cdr pat) (cdr term)))))))

;;   (local (defthm substitute-into-single-var-unify-term-lemma
;;            (if flg
;;                (implies (and (all-keys-bound (simple-term-vars pat) alist)
;;                              (mv-nth 0 (simple-one-way-unify pat term alist))
;;                              (all-identities-except-x var alist))
;;                         (equal (substitute-into-term
;;                                 pat
;;                                 (cons (cons var (substitute-into-term
;;                                                  (cdr (hons-assoc-equal var alist))
;;                                                  subst))
;;                                       subst))
;;                                (substitute-into-term term subst)))
;;              (implies (and (all-keys-bound (simple-term-vars-lst pat) alist)
;;                            (mv-nth 0 (simple-one-way-unify-lst pat term alist))
;;                            (all-identities-except-x var alist))
;;                       (equal (substitute-into-list
;;                               pat
;;                               (cons (cons var (substitute-into-term
;;                                                (cdr (hons-assoc-equal var alist))
;;                                                subst))
;;                                     subst))
;;                              (substitute-into-list term subst))))
;;            :hints (("goal" :induct (subst-ind flg pat term))
;;                    (and stable-under-simplificationp
;;                         '(:expand ((simple-one-way-unify-lst pat term alist)
;;                                    (substitute-into-list term subst)
;;                                    (:free (subst) (substitute-into-list pat subst))
;;                                    (:free (term) (simple-one-way-unify pat term alist))
;;                                    (simple-one-way-unify nil term alist)
;;                                    (substitute-into-term term subst)
;;                                    (:free (subst) (substitute-into-term pat subst))))))
;;            :rule-classes nil))

;;   (defthm substitute-into-single-var-unify-term
;;     (implies (and (all-keys-bound (simple-term-vars pat) alist)
;;                   (mv-nth 0 (simple-one-way-unify pat term alist))
;;                   (all-identities-except-x var alist))
;;              (equal (substitute-into-term
;;                      pat
;;                      (cons (cons var (substitute-into-term
;;                                       (cdr (hons-assoc-equal var alist))
;;                                       subst))
;;                            subst))
;;                     (substitute-into-term term subst)))
;;     :hints (("goal" :use ((:instance substitute-into-single-var-unify-term-lemma
;;                            (flg t)))))))


;; (defthm eval-of-substitute-into-single-var-unify-term-1
;;   (implies (and (all-keys-bound (simple-term-vars pat) alist)
;;                 (mv-nth 0 (simple-one-way-unify pat term alist))
;;                 (all-identities-except-x var alist)
;;                 (pseudo-termp pat)
;;                 (pseudo-termp term))
;;            (equal (ctx-ev pat
;;                           (cons (cons var
;;                                       (ctx-ev (cdr (hons-assoc-equal var alist))
;;                                               (ctx-ev-alist subst a)))
;;                                 (ctx-ev-alist subst a)))
;;                   (ctx-ev term (ctx-ev-alist subst a)))))
;;   :hints (("goal" :use ((:instance ctx-ev-substitute-into-term
;;                          (x pat)
;;                          (subst (cons (cons var (substitute-into-term
;;                                                  (cdr (hons-assoc-equal var alist))
;;                                                  subst))
;;                                       subst)))))))

(defthm eval-of-substitute-into-single-var-unify-term-rw
  (let ((alist (mv-nth 1 (simple-one-way-unify pat term nil))))
    (implies (and (mv-nth 0 (simple-one-way-unify pat term nil))
                  (all-identities-except-x var alist)
                  (pseudo-termp pat)
                  (pseudo-termp term)
                  (pseudo-termp (cdr (hons-assoc-equal var alist)))
                  ;; (syntaxp (let ((mfc mfc) (state state))
                  ;;            (declare (ignore state))
                  ;;            (prog2$
                  ;;             (cw "mfc-ttree: ~x0~%"
                  ;;                 (access metafunction-context mfc :ttree))
                  ;;             t)))
                  )
             (equal (ctx-ev pat
                            (cons (cons var
                                        (ctx-ev (cdr (hons-assoc-equal var alist))
                                                (ctx-ev-alist subst a)))
                                  (ctx-ev-alist subst a)))
                    (ctx-ev term (ctx-ev-alist subst a)))))
  :hints (("goal" :use ((:instance substitute-into-single-var-unify-term-lemma
                         (alist (mv-nth 1 (simple-one-way-unify pat term
                                                                nil)))))
           :in-theory (disable substitute-into-single-var-unify-term-lemma))))


;; (defun false () nil)
;; (defthm equal-print-ttree
;;   (implies (and (syntaxp (let ((mfc mfc) (state state))
;;                            (declare (ignore state))
;;                            (cw "mfc-ttree: ~x0~%"
;;                                (access metafunction-context mfc :ttree))))
;;                 (false))
;;            (equal (equal x y) t)))

(defthm try-context-rw-correct
  (implies (and (ctx-ev-theoremp (rewrite-rule-term rule))
                (ctx-ev-meta-extract-contextual-facts a)
                (ctx-ev-meta-extract-global-facts)
                (pseudo-termp term))
           (equal (ctx-ev (mv-nth 1 (try-context-rw term rule rune mfc state)) a)
                  (ctx-ev term a)))
  :hints (("goal" :use ((:instance ctx-ev-falsify
                         (x (rewrite-rule-term rule))
                         (a (ctx-ev-alist
                             (mv-nth 1
                                     (mx-relieve-hyps
                                      (mv-nth 1 (rewrite-rule-parts rule))
                                      (mv-nth 1 (simple-one-way-unify
                                                 (access rewrite-rule rule :rhs)
                                                 term nil))
                                      rune term 0 mfc state))
                             a))))
           :in-theory (e/d (rewrite-rule-term)
                           (alistp-of-cdr symbol-alistp)))))

(in-theory (disable try-context-rw))

(defun rewrite-rule-rune (lemma)
  (declare (xargs :verify-guards nil))
  (access rewrite-rule lemma :rune))

(defun lookup-rewrite-in-lemmas (rune lemmas)
  (declare (xargs :guard t))
  (if (atom lemmas)
      nil
    (if (equal rune (ec-call (rewrite-rule-rune (car lemmas))))
        (car lemmas)
      (lookup-rewrite-in-lemmas rune (cdr lemmas)))))

(defthm member-of-lookup-rewrite
  (implies (lookup-rewrite-in-lemmas rune lemmas)
           (member (lookup-rewrite-in-lemmas rune lemmas) lemmas)))


(defun try-context-rws (term runes lemmas mfc state)
  (declare (xargs :stobjs state
                  :guard (pseudo-termp term)))
  (b* (((when (atom runes))
        (mv nil term))
       (rune (car runes))
       (rule (lookup-rewrite-in-lemmas rune lemmas))
       ((unless rule)
        (try-context-rws term (cdr runes) lemmas mfc state))
       ((mv succp new-term)
        (try-context-rw term rule rune mfc state))
       ((when succp)
        (mv t new-term)))
    (try-context-rws term (cdr runes) lemmas mfc state)))

(defthm try-context-rws-correct
  (implies (and (ctx-ev-meta-extract-contextual-facts a)
                (ctx-ev-meta-extract-global-facts)
                (pseudo-termp term)
                var)
           (let ((lemmas (fgetprop fn 'lemmas nil (w state))))
             (equal (ctx-ev (mv-nth 1 (try-context-rws term runes lemmas mfc state)) a)
                    (ctx-ev term a))))
  :hints (("goal" :induct (len runes))
          (and stable-under-simplificationp
               '(:use ((:instance ctx-ev-meta-extract-lemma-term
                        (rule (lookup-rewrite-in-lemmas
                               (car runes)
                               (fgetprop fn 'lemmas nil (w state))))
                        (a (ctx-ev-falsify
                            (rewrite-rule-term
                             (lookup-rewrite-in-lemmas
                              (car runes)
                              (fgetprop fn 'lemmas nil (w state))))))
                        (st state)))))))


(in-theory (disable try-context-rws))

(defun apply-contexts (term mfc state)
  (declare (xargs :stobjs state
                  :guard (pseudo-termp term)
                  :guard-hints (("goal" :in-theory (enable state-p1)))))
  (b* (((unless (and (consp term)
                     (symbolp (car term)))) term)
       (alist (table-alist 'contextual-theorems-table (w state)))
       (runes (cdr (hons-assoc-equal (car term) alist)))
       (lemmas (getprop (car term) 'lemmas nil 'current-acl2-world (w statE)))
       ((mv ?succp term)
        (try-context-rws term runes lemmas mfc state)))
    term))

(defthm apply-contexts-correct
  (implies (and (pseudo-termp term)
                (ctx-ev-meta-extract-contextual-facts a)
                (ctx-ev-meta-extract-global-facts))
           (equal (ctx-ev term a)
                  (ctx-ev (apply-contexts term mfc state) a)))
  :hints(("Goal" :in-theory (disable w)))
  :rule-classes nil)

(defun add-context-rule-fn (fn rune state)
  (declare (Xargs :mode :program :stobjs state))
  (b* ((rule (lookup-rewrite-in-lemmas rune (getprop fn 'lemmas nil
                                                     'current-acl2-world (w state))))
       ((unless rule)
        (er hard 'add-context-rule "Could not find a rewrite rule for ~x0 ~
                                    with rune ~x1.~%" fn rune))
       (name (cadr rune))
       ((mv class hyps equiv lhs rhs) (rewrite-rule-parts rule))
       ((when (eq class 'meta))
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    it is a meta rule." name))
       ((unless (and (pseudo-term-listp hyps)
                     (pseudo-termp lhs)
                     (pseudo-termp rhs)))
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    its hyps, LHS, and RHS are not all ~
                                    pseudo-terms!"
            name))
       ((unless (eq equiv 'equal))
        (er hard 'add-context-rule "~x0 is not a valid context rule (at the ~
                                    moment), because it uses ~x1 rather than ~
                                    EQUAL as its equivalence relation."
            name equiv))
       ((mv ok lhs-subst) (simple-one-way-unify rhs lhs nil))
       ((unless ok)
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    its LHS does not unify with its RHS" name))
       (var (find-non-identity lhs-subst))
       ((unless (and var (symbolp var)
                     (all-identities-except-x var lhs-subst)))
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    more than one variable is substituted ~
                                    between its RHS and LHS" name))
       (ctx-term (cdr (assoc var lhs-subst)))
       (lhs-not-rhs-vars (set-difference-eq (simple-term-vars ctx-term)
                                            (simple-term-vars rhs)))
       ((when lhs-not-rhs-vars)
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    its LHS has variables not present in its ~
                                    RHS: ~x1"
            name lhs-not-rhs-vars))
       (hyp-not-rhs-vars (set-difference-eq (simple-term-vars-lst hyps)
                                            (simple-term-vars rhs)))
       ((when hyp-not-rhs-vars)
        (er hard 'add-context-rule "~x0 is not a valid context rule because ~
                                    its hyps have variables not present in ~
                                    its RHS: ~x1"
            name hyp-not-rhs-vars))
       (rule-table (table-alist 'contextual-theorems-table (w state)))
       (fn-entries (cdr (hons-assoc-equal fn rule-table)))
       ((when fn-entries)
        `(table contextual-theorems-table
                ',fn ',(cons rune fn-entries)))
       (meta-rulename (intern-in-package-of-symbol
                       (concatenate 'string "APPLY-CONTEXT-FOR-" (symbol-name fn))
                       fn)))
    `(progn
       (defthm ,meta-rulename
         (implies (and (pseudo-termp term)
                       (ctx-ev-meta-extract-contextual-facts a)
                       (ctx-ev-meta-extract-global-facts))
                  (equal (ctx-ev term a)
                         (ctx-ev (apply-contexts term mfc state) a)))
         :hints (("goal" :by apply-contexts-correct))
         :rule-classes ((:meta :trigger-fns (,fn))))
       (table contextual-theorems-table ',fn '(,rune)))))


(defmacro add-context-rule (fn rune)
  `(make-event (add-context-rule-fn ',fn ',rune state)))


;; Basic text of contextual rewriting.  For a more useful example see the
;; commented material below involving MOD.
(local
 (progn

   (encapsulate
     (((foo * *) => *)
      ((bar * *) => *)
      ((baz *) => *)
      ((fuz * *) => *)
      ((baf * *) => *)
      ((buzp *) => *)
      ((froz *) => *))

     (set-ignore-ok t)
     (set-irrelevant-formals-ok t)
     (local (defun foo (x y) nil))
     (local (defun fuz (x y) nil))
     (local (defun bar (x y) nil))
     (local (defun baz (x) nil))
     (local (defun baf (x y) nil))
     (local (defun buzp (x) t))
     (local (defun froz (x) nil))

     ;; Under (bar y ...) context, (foo y x) is equivalent to x.
     (defthm bar-of-foo
       (implies (and (buzp (froz x))
                     (buzp (froz y)))
                (equal (bar y (foo y x))
                       (bar y x))))

     ;; unnder (bar y ...) context, (fuz y x) is equivalent to x.
     (defthm bar-of-fuz
       (equal (bar y (fuz y x))
              (bar y x)))

     ;; Under (foo y ...) context, (baz x) is equivalent to (baf x y)
     (defthm foo-of-baz
       (implies (buzp (froz y))
                (equal (foo y (baz x))
                       (foo y (baf x y)))))

     (defthm fuz-of-baf
       (equal (fuz y (baf x y))
              (fuz y x)))

     (defthm buzp-froz
       (buzp (froz y))))


   (add-context-rule bar (:rewrite bar-of-foo))
   (add-context-rule bar (:rewrite bar-of-fuz))


   ;; We don't have any rewrite rules that match (bar w (baz z)) or (baz z).
   ;; But our meta rule fires, so APPLY-CONTEXTS is applied to (bar w (baz z)).
   ;; It first tries BAR-OF-FUZ.  Because (fuz w (baz z)) doesn't simplify, we
   ;; give up on that and try BAR-OF-FOO instead.  The required (buzp (froz x))
   ;; hyps are relieved and we then rewrite (foo w (baz z)), which becomes
   ;; (foo y (baf x y)).  So apply-contexts produces (bar y (foo y (baf x y))).
   ;;

   (defthm bar-of-baz
     (equal (bar w (baz z))
            (bar w z)))))



#||

;; This takes a page from Dave Greve's NARY framework.  Both are attempting to
;; do the same thing: use contextual information in rewriting.  One way to look
;; at it is that we're trying to extend the notion of rewriting under an
;; equivalence context (e.g., under set equivalence, Boolean equivalence, ...)
;; to some sort of parametrized "equivalence", e.g. equivalent mod N,
;; equivalent in the low M bits, equivalent for alist lookups of keys K, etc.

;; Rather than expressing this contextual information in terms of a
;; parametrized equivalence relation, as in NARY we instead express contexts
;; using "fixing functions".  If equiv is a parameterized equivalence relation
;; with parameter P, equiv-fix is a fixing function for it if:
;;    (iff (equiv p a b)    (equal (equiv-fix p a) (equiv-fix p b))).

;; MOD is a good example -- (equal (mod a n) (mod b n)) is an equivalence
;; relation between A and B parameterized by N.

;; The problem we want to solve:  Suppose we know that
;; (mod (foo m n) n) = (mod (bar m n) n) and have this as a rewrite rule.
;; But we have a big sum of things:
;; (mod (+ a b c ...  (foo m n) ...) n).
;; What's a good way to propagate the "mod N" context into the appropriate spot
;; in the addition?

;; Here we define two rules that look like decent rewrite rules, in some sense:
;; as written, they each remove a (mod ... n) call from a place where it's
;; redundant.  But interpreted by our system, they'll actually be used
;; backwards: they'll both match (mod (+ x y) n), the first one will cause X to
;; be rewritten under a (mod .. n) context, and the second will cause Y to be
;; rewritten under a (mod .. n) context.
(encapsulate nil
  (local
   (include-book
    "ihs/quotient-remainder-lemmas" :dir :system))
  (local (in-theory (disable mod)))
  (defthm mod-n-first-arg-of-plus-context
    (implies (and (rationalp x)
                  (rationalp y)
                  (rationalp n)
                  (not (equal n 0)))
             (equal (mod (+ (mod x n) y) n)
                    (mod (+ x y) n))))
  (defthm mod-n-second-arg-of-plus-context
    (implies (and (rationalp x)
                  (rationalp y)
                  (rationalp n)
                  (not (equal n 0)))
             (equal (mod (+ x (mod y n)) n)
                    (mod (+ x y) n)))))

;; These events allow the contextual-rewriting system to use these two rules.
;; The first adds a meta rule for the function APPLY-CONTEXTS triggered on MOD,
;; and they both add runes to a table that we use to look up context rules.
(add-context-rule mod (:rewrite mod-n-first-arg-of-plus-context))
(add-context-rule mod (:rewrite mod-n-second-arg-of-plus-context))

;; Here is our foo/bar theory...
(encapsulate
  (((foo * *) => *)
   ((bar * *) => *))
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun foo (x y) 0))
  (local (defun bar (x y) 0))

  (defthm foo-bar-under-mod
    (equal (mod (foo m n) n)
           (mod (bar m n) n)))

  (defthm rationalp-foo
    (rationalp (foo x y))
    :rule-classes (:rewrite :type-prescription))

  (defthm rationalp-bar
    (rationalp (bar x y))
    :rule-classes (:rewrite :type-prescription)))

(local (in-theory (disable mod)))

(in-theory (disable mod-+-cong1 mod-+-cong2))


(thm (implies (and (rationalp a)
                   (rationalp b)
                   (rationalp c)
                   (rationalp d)
                   (rationalp e)
                   (rationalp n)
                   (not (equal n 0)))
              (equal (mod (+ a b c d (foo m n) e) n)
                     (mod (+ a b c d (bar m n) e) n)))
     :hints(("Goal" :in-theory (disable distributivity
                                        commutativity-of-+))))



(include-book
 "coi/nary/nary" :dir :system)

;; here is the same thing using NARY...
(encapsulate nil
  (local
   (include-book
    "ihs/quotient-remainder-lemmas" :dir :system))
  (defcontext (mod x a) 1)

  (defcong+ mod-+-cong1
    (mod (+ a b) n)
    :hyps (and (rationalp n)
               (rationalp a)
               (rationalp b)
               (not (equal n 0)))
    :cong ((a (equal x (mod a n))))
    :check (rationalp x))
  (defcong+ mod-+-cong2
    (mod (+ a b) n)
    :hyps (and (rationalp n)
               (rationalp a)
               (rationalp b)
               (not (equal n 0)))
    :cong ((b (equal y (mod b n))))
    :check (rationalp y))

  (defthm rationalp-mod
    (implies (and (rationalp x) (rationalp y))
             (rationalp (mod x y)))
    :rule-classes (:rewrite :type-prescription)))

(in-theory (disable common-lisp::apply-context-for-mod))
(thm (implies (and (rationalp a)
                   (rationalp b)
                   (rationalp c)
                   (rationalp d)
                   (rationalp e)
                   (rationalp n)
                   (not (equal n 0)))
              (equal (mod (+ a b c d (foo m n) e) n)
                     (mod (+ a b c d (bar m n) e) n)))
     :hints(("Goal" :in-theory (disable distributivity
                                        commutativity-of-+))))






(defthm mfc-do-rewrites-for-foo/fuz
  (implies (and (pseudo-termp term)
                (ctx-ev-meta-extract-global-facts)
                (ctx-ev-meta-extract-contextual-facts a))
           (equal (ctx-ev term a)
                  (ctx-ev (mfc-do-rewrites term mfc state) a)))
  :hints ('(:by mfc-do-rewrites-correct))
  :rule-classes ((:meta :trigger-fns (foo fuz))))




(table meta-rw-table 'foo '((:rewrite foo-of-baz)))
(table meta-rw-table 'fuz '((:rewrite fuz-of-baf)))


(in-theory (disable ;foo-of-baz
;fuz-of-baf
            (force)))

(table meta-rw-table 'cons '((:rewrite dumb-rewrite)))

(defthm mfc-do-rewrites-for-cons
  (implies (and (pseudo-termp term)
                (ctx-ev-meta-extract-global-facts)
                (ctx-ev-meta-extract-contextual-facts a))
           (equal (ctx-ev term a)
                  (ctx-ev (mfc-do-rewrites term mfc state) a)))
  :hints ('(:by mfc-do-rewrites-correct))
  :rule-classes ((:meta :trigger-fns (cons))))

(thm (implies (equal p q) (equal (cons p z) (cons nil z)))
     :hints(("Goal" :in-theory (disable cons-equal))))

||#
