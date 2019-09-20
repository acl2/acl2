; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "pseudo-rewrite-rule")
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :System)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "reconstruct")
(include-book "centaur/misc/starlogic" :dir :system)
(include-book "term-vars")
(include-book "subst")
(local (include-book "std/lists/sets" :dir :system))

(defevaluator urw-ev urw-ev-list
  ((cons a b)
   (binary-+ a b)
   (typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b))
  :namedp t)

(acl2::def-ev-pseudo-term-fty-support urw-ev urw-ev-list)
(acl2::def-meta-extract urw-ev urw-ev-list)
(acl2::def-unify urw-ev urw-ev-alist)

(define urw-ev-good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (urw-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (urw-ev-good-rewrite-rulesp (cdr rules))))
  ///
  (defthm urw-ev-good-rewrite-rulesp-of-cons
    (equal (urw-ev-good-rewrite-rulesp (cons a b))
           (and (urw-ev-theoremp (acl2::rewrite-rule-term a))
                (urw-ev-good-rewrite-rulesp b))))

  (defthm urw-ev-good-rewrite-rulesp-of-cdr
    (implies (urw-ev-good-rewrite-rulesp x)
             (urw-ev-good-rewrite-rulesp (cdr x))))

  (defthm urw-ev-of-car-when-good-rewrite-rulesp
    (implies (and (urw-ev-good-rewrite-rulesp x) (consp x))
             (urw-ev (acl2::rewrite-rule-term (car x)) a))
    :hints(("Goal" :in-theory (disable acl2::rewrite-rule-term)
            :expand ((urw-ev-good-rewrite-rulesp x))
            :use ((:instance urw-ev-falsify
                   (x (acl2::rewrite-rule-term (car x))) (a a))))))

  (local (defun urw-ev-good-rewrite-rulesp-badguy (rules)
           (if (atom rules)
               nil
             (if (urw-ev-theoremp (acl2::rewrite-rule-term (car rules)))
                 (urw-ev-good-rewrite-rulesp-badguy (cdr rules))
               (car rules)))))

  (local (defthmd urw-ev-good-rewrite-rulesp-by-badguy
           (iff (urw-ev-good-rewrite-rulesp rules)
                (b* ((badguy (urw-ev-good-rewrite-rulesp-badguy rules)))
                  (or (not (member badguy rules))
                      (urw-ev-theoremp (acl2::rewrite-rule-term badguy)))))))


  (defthm urw-ev-good-rewrite-rulesp-of-lemmas
    (implies (and (urw-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (urw-ev-good-rewrite-rulesp (fgetprop fn 'acl2::lemmas nil wrld)))
    :hints(("Goal" :in-theory (e/d (urw-ev-good-rewrite-rulesp-by-badguy)
                                   (urw-ev-good-rewrite-rulesp
                                    urw-ev-good-rewrite-rulesp-badguy
                                    acl2::rewrite-rule-term
                                    w))
            :do-not-induct t))))


(local (in-theory (disable acl2::enabled-numep
                           acl2::enabled-structure-p)))

(define filter-enabled-abbrev-rules (lemmas (ens acl2::enabled-structure-p))
  :returns (rules pseudo-rewrite-rule-listp)
  (b* (((when (atom lemmas)) nil)
       (rule (car lemmas))
       ((unless (pseudo-rewrite-rule-p rule))
        (filter-enabled-abbrev-rules (cdr lemmas) ens))
       ((acl2::rewrite-rule rule))
       ((unless (and (eq rule.subclass 'acl2::abbreviation)
                     (acl2::enabled-numep rule.nume ens)))
        (filter-enabled-abbrev-rules (cdr lemmas) ens)))
    (cons rule (filter-enabled-abbrev-rules (cdr lemmas) ens)))
  ///
  (defret urw-ev-good-rewrite-rulesp-of-<fn>
    (implies (urw-ev-good-rewrite-rulesp lemmas)
             (urw-ev-good-rewrite-rulesp rules))))

(define fn-enabled-abbrev-rules ((fn symbolp) (ens acl2::enabled-structure-p) (wrld plist-worldp))
  :returns (rules pseudo-rewrite-rule-listp)
  (b* ((lemmas (fgetprop fn 'acl2::lemmas nil wrld)))
    (filter-enabled-abbrev-rules lemmas ens))
  ///
  (defret urw-ev-good-rewrite-rulesp-of-<fn>
    (implies (and (urw-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (urw-ev-good-rewrite-rulesp rules)))

  (memoize 'fn-enabled-abbrev-rules))

(define check-enabled-structure (x)
  :enabled t
  (acl2::enabled-structure-p x)
  ///
  (memoize 'check-enabled-structure))

(define fn-enabled-abbrev-rules-st ((fn symbolp) state)
  :returns (rules pseudo-rewrite-rule-listp)
  (b* ((ens (and (boundp-global 'urewrite-ens state)
                 (@ urewrite-ens)))
       ((unless (check-enabled-structure ens)) nil))
    (fn-enabled-abbrev-rules fn ens (w state)))
  ///
  (defret urw-ev-good-rewrite-rulesp-of-<fn>
    (implies (and (urw-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state)))
             (urw-ev-good-rewrite-rulesp rules))))

(define find-executable-counterpart-nume (pairs)
  (if (atom pairs)
      nil
    (b* ((pair (car pairs)))
      (case-match pair
        ((nume ':executable-counterpart . &) nume)
        (& (find-executable-counterpart-nume (cdr pairs)))))))

(define exec-enabledp ((fn symbolp) state)
  :hooks nil
  (b* ((pairs (fgetprop fn 'acl2::runic-mapping-pairs nil (w state)))
       (nume (find-executable-counterpart-nume pairs))
       ((unless (natp nume)) nil)
       (ens (and (boundp-global 'urewrite-ens state)
                 (@ urewrite-ens))))
    (and (check-enabled-structure ens)
         (acl2::enabled-numep nume ens))))



#!acl2
(defret pseudo-term-subst-p-of-unify-const
  (implies (and (pseudo-termp pat)
                (cmr::pseudo-term-subst-p alist))
           (cmr::pseudo-term-subst-p al))
  :hints (("goal" :induct <call> :expand ((:free (const) <call>)
                                          (:free (const) (acl2::unify-const nil const alist)))
           :in-theory (enable (:i acl2::unify-const))))
  :fn acl2::unify-const)

#!acl2
(std::defret-mutual pseudo-term-subst-p-of-simple-one-way-unify
  (defret pseudo-term-subst-p-of-simple-one-way-unify
    (implies (and (pseudo-termp pat)
                  (pseudo-termp term)
                  (cmr::pseudo-term-subst-p alist))
             (cmr::pseudo-term-subst-p a))
    :hints ('(:expand ((:free (term) <call>)
                       (:free (term alist) (simple-one-way-unify nil term alist)))) )
    :fn acl2::simple-one-way-unify)

  (defret pseudo-term-subst-p-of-simple-one-way-unify-lst
    (implies (and (pseudo-term-listp pat)
                  (pseudo-term-listp term)
                  (cmr::pseudo-term-subst-p alist))
             (cmr::pseudo-term-subst-p a))
    :hints ('(:expand (<call>)))
    :fn acl2::simple-one-way-unify-lst)
  :mutual-recursion acl2::simple-one-way-unify)


(local (in-theory (disable acl2::rewrite-rule-term)))


(define iff-p-fix (iff-p x)
  (if iff-p (acl2::bool-fix x) x)
  ///
  (defthm iff-p-fix-of-nil
    (equal (iff-p-fix nil x) x))
  (defthm iff-p-fix-of-t
    (equal (iff-p-fix t x) (acl2::bool-fix x))))

(define try-uncond-rewrite-rule ((fn pseudo-fnsym-p)
                                 (args pseudo-term-listp)
                                 (iff-p)
                                 (rule pseudo-rewrite-rule-p))
  :returns (mv successp
               (ans pseudo-termp)
               (alist pseudo-term-subst-p))
  (b* (((acl2::rewrite-rule rule))
       ((unless (and (mbt (pseudo-rewrite-rule-p rule))
                     (mbt (pseudo-term-listp args))
                     (or (eq rule.equiv 'equal)
                         (and iff-p (eq rule.equiv 'iff)))
                     (eq rule.subclass 'acl2::abbreviation)
                     (not rule.hyps)
                     (pseudo-term-case rule.lhs
                       :fncall (eq rule.lhs.fn fn)
                       :otherwise nil)))
        (mv nil nil nil))
       (pat-args (pseudo-term-call->args rule.lhs))
       ((mv unify-ok subst) (acl2::simple-one-way-unify-lst pat-args args nil))
       ((when unify-ok) (mv t rule.rhs subst)))
    (mv nil nil nil))
  ///
  (defret <fn>-correct
    (implies (and successp
                  (urw-ev-theoremp (acl2::rewrite-rule-term rule)))
             (equal (iff-p-fix iff-p (urw-ev ans (urw-ev-alist alist a)))
                    (iff-p-fix iff-p (urw-ev (pseudo-term-fncall fn args) a))))
    :hints(("Goal" :in-theory (enable urw-ev-of-fncall-args
                                      rewrite-rule-term-alt-def
                                      iff-p-fix)
            :use ((:instance urw-ev-falsify
                   (x (acl2::rewrite-rule-term rule))
                   (a (urw-ev-alist
                       (mv-nth 1 (acl2::simple-one-way-unify-lst
                                  (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                                  args nil))
                       a))))))))


(define try-uncond-rewrite-rules ((fn pseudo-fnsym-p)
                                  (args pseudo-term-listp)
                                  (iff-p)
                                  (rules pseudo-rewrite-rule-listp))
  :returns (mv successp
               (ans pseudo-termp)
               (alist pseudo-term-subst-p))
  (b* (((when (atom rules)) (mv nil nil nil))
       ((mv successp rhs subst) (try-uncond-rewrite-rule fn args iff-p (car rules)))
       ((when successp) (mv successp rhs subst)))
    (try-uncond-rewrite-rules fn args iff-p (cdr rules)))
  ///
  
  (defret <fn>-correct
    (implies (and successp
                  (urw-ev-good-rewrite-rulesp rules))
             (equal (iff-p-fix iff-p (urw-ev ans (urw-ev-alist alist a)))
                    (iff-p-fix iff-p (urw-ev (pseudo-term-fncall fn args) a))))
    :hints(("Goal" :in-theory (enable urw-ev-of-fncall-args
                                      rewrite-rule-term-alt-def)
            :use ((:instance urw-ev-falsify
                   (x (acl2::rewrite-rule-term rule))
                   (a (urw-ev-alist
                       (mv-nth 1 (acl2::simple-one-way-unify-lst
                                  (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                                  args nil))
                       a))))))))


(define pseudo-term-quote-listp ((x pseudo-term-listp))
  (if (atom x)
      t
    (and (pseudo-term-case (car x) :quote)
         (pseudo-term-quote-listp (cdr x)))))

(define pseudo-term-quote-list->vals ((x pseudo-term-listp))
  :guard (pseudo-term-quote-listp x)
  :guard-hints (("goal" :in-theory (enable pseudo-term-quote-listp)))
  :returns (vals true-listp)
  (if (atom x)
      nil
    (cons (pseudo-term-quote->val (car x))
          (pseudo-term-quote-list->vals (cdr x))))
  ///
  (defthm urw-ev-list-when-pseudo-term-quote-listp
    (implies (pseudo-term-quote-listp x)
             (equal (urw-ev-list x a)
                    (pseudo-term-quote-list->vals x)))
    :hints(("Goal" :in-theory (enable pseudo-term-quote-listp)))))

(local (defthm and*-hyp
         (implies (acl2::rewriting-negative-literal `(acl2::binary-and* ,a ,b))
                  (iff (acl2::and* a b) (and a b)))))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local
 (defthm pseudo-term-list-count-when-consp
   (implies (consp x)
            (< (+ (pseudo-term-count (car x))
                  (pseudo-term-list-count (cdr x)))
               (pseudo-term-list-count x)))
    :rule-classes :linear))

(local (defthm len-of-cons
         (equal (len (cons a b))
                (+ 1 (len b)))))


(local (defun len-is (x n)
         (if (zp n)
             (and (eql n 0) (atom x))
           (and (consp x)
                (len-is (cdr x) (1- n))))))

(local (defthm open-len-is
         (implies (syntaxp (quotep n))
                  (equal (len-is x n)
                         (if (zp n)
                             (and (eql n 0) (atom x))
                           (and (consp x)
                                (len-is (cdr x) (1- n))))))))
                         

(local (defthm equal-len-hyp
         (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
                                    (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
                                (quotep n)))
                  (equal (equal (len x) n)
                         (len-is x n)))))

(local (defthm assoc-when-key
         (implies key
                  (equal (assoc key x)
                         (hons-assoc-equal key x)))))

(local (defthm pseudo-termp-of-lookup
         (implies (pseudo-term-subst-p x)
                  (pseudo-termp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (enable pseudo-term-subst-p)))))

(define pair-vars-with-terms ((vars symbol-listp)
                              (vals pseudo-term-listp))
  :guard (equal (len vars) (len vals))
  :returns (subst pseudo-term-subst-p)
  (if (atom vars)
      nil
    (if (car vars)
        (cons (cons (pseudo-var-fix (car vars))
                    (pseudo-term-fix (car vals)))
              (pair-vars-with-terms (cdr vars) (cdr vals)))
      (pair-vars-with-terms (cdr vars) (cdr vals))))
  ///
  (defthm lookup-in-pair-vars-with-terms
    (implies (and (pseudo-var-p v)
                  (symbol-listp vars))
             (equal (cdr (hons-assoc-equal v (pair-vars-with-terms vars vals)))
                    (pseudo-term-fix (cdr (hons-assoc-equal v (pairlis$ vars vals))))))
    :hints(("Goal" :in-theory (enable pairlis$)))))






(local (defthm const-equal-const-plus-x
         (implies (and (syntaxp (and (quotep a) (quotep b)))
                       (acl2-numberp b))
                  (equal (equal (+ a x) b)
                         (equal (fix x) (- b a))))))

(local (defthm lookup-in-urw-ev-alist
         (implies v
                  (equal (cdr (hons-assoc-equal v (urw-ev-alist a env)))
                         (urw-ev (cdr (hons-assoc-equal v a)) env)))
         :hints(("Goal" :in-theory (enable urw-ev-alist)))))

(set-state-ok t)

(defthm-term-vars-flag
  (defthm urw-ev-of-pair-vars-with-terms
    (implies (symbol-listp vars)
             (equal (urw-ev x (urw-ev-alist (pair-vars-with-terms vars vals) a))
                    (urw-ev x (urw-ev-alist (pairlis$ vars vals) a))))
    :hints ('(:in-theory (enable urw-ev-of-fncall-args
                                 urw-ev-when-pseudo-term-call)))
    :flag term-vars)
  (defthm urw-ev-list-of-pair-vars-with-terms
    (implies (symbol-listp vars)
             (equal (urw-ev-list x (urw-ev-alist (pair-vars-with-terms vars vals) a))
                    (urw-ev-list x (urw-ev-alist (pairlis$ vars vals) a))))
    :flag termlist-vars))



(defthm urw-ev-alist-of-pairlis$
  (equal (urw-ev-alist (pairlis$ vars vals) a)
         (pairlis$ vars (urw-ev-list vals a))))

(defines urewrite
  (define urewrite-term ((x pseudo-termp)
                         (a pseudo-term-subst-p)
                         (iff-p)
                         (reclimit natp)
                         state)
    :verify-guards nil
    :returns (ans pseudo-termp)
    :well-founded-relation acl2::nat-list-<
    :measure (list reclimit (pseudo-term-count x) 5)
    (pseudo-term-case x
      :var (cdr (assoc-eq x.name (pseudo-term-subst-fix a)))
      :const (pseudo-term-fix x)
      :fncall (b* (((when (acl2::and* (eq x.fn 'if)
                                      (eql (len x.args) 3)))
                    (urewrite-if (first x.args)
                                 (second x.args)
                                 (third x.args)
                                 a iff-p reclimit state))
                   ((when (acl2::and* (eq x.fn 'not)
                                      (eql (len x.args) 1)))
                    (urewrite-not (first x.args)
                                  a iff-p reclimit state))

                   ((when (acl2::and* (eq x.fn 'implies)
                                      (eql (len x.args) 2)))
                    (urewrite-implies (first x.args)
                                      (second x.args)
                                      a iff-p reclimit state))
                   (args (urewrite-termlist x.args a reclimit state)))
                (urewrite-fncall x.fn args iff-p reclimit state))
      
      :lambda (b* ((args (urewrite-termlist x.args a reclimit state))
                   (new-a (pair-vars-with-terms x.formals args)))
                (urewrite-term x.body new-a iff-p reclimit state))))

  (define urewrite-fncall ((fn pseudo-fnsym-p)
                           (args pseudo-term-listp)
                           (iff-p)
                           (reclimit natp)
                           state)
    :returns (ans pseudo-termp)
    :measure (list reclimit 0 0)
    (b* ((fn (pseudo-fnsym-fix fn))
         ((mv ok eval-ans)
          (if (and (pseudo-term-quote-listp args)
                   (exec-enabledp fn state))
              (b* (((mv err ans) (acl2::magic-ev-fncall-logic fn (pseudo-term-quote-list->vals args) state)))
                (mv (not err) ans))
            (mv nil nil)))
         ((when ok) (pseudo-term-quote eval-ans))
         ((mv successp rhs subst)
          (try-uncond-rewrite-rules
           fn args iff-p
           (fn-enabled-abbrev-rules-st fn state)))
         ((when (and successp (posp reclimit)))
          (urewrite-term rhs subst iff-p (1- reclimit) state)))
      (pseudo-term-fncall fn args)))


  (define urewrite-if ((test pseudo-termp)
                       (then pseudo-termp)
                       (else pseudo-termp)
                       (a pseudo-term-subst-p)
                       (iff-p)
                       (reclimit natp)
                       state)
    :returns (ans pseudo-termp)
    :measure (list reclimit (+ (pseudo-term-count test)
                               (pseudo-term-count then)
                               (pseudo-term-count else))
                   2)
    (b* ((test2 (urewrite-term test a t reclimit state))
         ((when (pseudo-term-case test2 :quote))
          (if (pseudo-term-quote->val test2)
              (urewrite-term then a iff-p reclimit state)
            (urewrite-term else a iff-p reclimit state)))
         (then2 (urewrite-term then a iff-p reclimit state))
         (else2 (urewrite-term else a iff-p reclimit state)))
      (urewrite-fncall 'if (list test2 then2 else2) iff-p reclimit state)))

  (define urewrite-not ((x pseudo-termp)
                        (a pseudo-term-subst-p)
                        (iff-p)
                        (reclimit natp)
                        state)
    :returns (ans pseudo-termp)
    :measure (list reclimit (pseudo-term-count x) 10)
    (b* ((x2 (urewrite-term x a t reclimit state)))
      (urewrite-fncall 'not (list x2) iff-p reclimit state)))

  (define urewrite-implies ((hyp pseudo-termp)
                            (concl pseudo-termp)
                            (a pseudo-term-subst-p)
                            (iff-p)
                            (reclimit natp)
                            state)
    :returns (ans pseudo-termp)
    :measure (list reclimit (+ (pseudo-term-count hyp)
                               (pseudo-term-count concl))
                   2)
    (b* ((hyp2 (urewrite-term hyp a t reclimit state))
         ((when (pseudo-term-case hyp2 :quote (not hyp2.val) :otherwise nil))
          ''t)
         (concl2 (urewrite-term concl a t reclimit state)))
      (urewrite-fncall 'implies (list hyp2 concl2) iff-p reclimit state)))

  (define urewrite-termlist ((x pseudo-term-listp)
                             (a pseudo-term-subst-p)
                             (reclimit natp)
                             state)
    :returns (ans pseudo-term-listp)
    :measure (list reclimit (pseudo-term-list-count x) 5)
    (if (atom x)
        nil
      (cons (urewrite-term (car x) a nil reclimit state)
            (urewrite-termlist (cdr x) a reclimit state))))
  ///

  (std::defret-mutual len-of-urewrite-termlist
    (defret len-of-urewrite-termlist
      (equal (len ans) (len x))
      :hints ('(:expand (<call>)))
      :fn urewrite-termlist)
    :skip-others t)

  (verify-guards urewrite-term)

  (std::defret-mutual urewrite-correct
    (defret urewrite-term-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (iff-p-fix iff-p (urw-ev ans env))
                      (iff-p-fix iff-p (urw-ev x (urw-ev-alist a env)))))
      :hints ('(:expand (<call>)
                :in-theory (enable urw-ev-of-fncall-args)))
      :fn urewrite-term)

    (defret urewrite-fncall-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (iff-p-fix iff-p (urw-ev ans env))
                      (iff-p-fix iff-p (urw-ev (pseudo-term-fncall fn args) env))))
      :hints ('(:expand (<call>)
                :in-theory (enable urw-ev-of-fncall-args)))
      :fn urewrite-fncall)

    (defret urewrite-if-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (iff-p-fix iff-p (urw-ev ans env))
                      (b* ((env1 (urw-ev-alist a env)))
                        (iff-p-fix iff-p (if* (urw-ev test env1)
                                              (urw-ev then env1)
                                              (urw-ev else env1))))))
      :hints ('(:expand (<call>)))
      :fn urewrite-if)

    (defret urewrite-not-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (iff-p-fix iff-p (urw-ev ans env))
                      (b* ((env1 (urw-ev-alist a env)))
                        (iff-p-fix iff-p (not (urw-ev x env1))))))
      :hints ('(:expand (<call>)))
      :fn urewrite-not)

    (defret urewrite-implies-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (iff-p-fix iff-p (urw-ev ans env))
                      (b* ((env1 (urw-ev-alist a env)))
                        (iff-p-fix iff-p (implies (urw-ev hyp env1)
                                                  (urw-ev concl env1))))))
      :hints ('(:expand (<call>)))
      :fn urewrite-implies)

    (defret urewrite-termlist-correct
      (implies (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
               (equal (urw-ev-list ans env)
                      (urw-ev-list x (urw-ev-alist a env))))
      :hints ('(:expand (<call>)))
      :fn urewrite-termlist))

  (defret urewrite-term-correct-iff
    (implies (and (and (urw-ev-meta-extract-global-facts :state state0)
                    (equal (w state0) (w state)))
                  iff-p)
             (iff (urw-ev ans env)
                  (urw-ev x (urw-ev-alist a env))))
    :hints (("goal" :use urewrite-term-correct
             :in-theory (e/d (iff-p-fix) (urewrite-term-correct))))
    :fn urewrite-term))


(defthm-term-vars-flag
  (defthm urw-ev-of-pair-term-vars
    (implies (and (subsetp (term-vars x) vars)
                  (pseudo-var-list-p vars))
             (equal (urw-ev x (pairlis$ vars (urw-ev-list vars a)))
                    (urw-ev x a)))
    :hints ('(:in-theory (enable urw-ev-of-fncall-args
                                 urw-ev-when-pseudo-term-call)
              :expand ((term-vars x))))
    :flag term-vars)
  (defthm urw-ev-list-of-pair-termlist-vars
    (implies (and (subsetp (termlist-vars x) vars)
                  (pseudo-var-list-p vars))
             (equal (urw-ev-list x (pairlis$ vars (urw-ev-list vars a)))
                    (urw-ev-list x a)))
    :hints ('(:expand ((termlist-vars x))))
    :flag termlist-vars))

(defthm urw-ev-disjoin-of-pair-termlist-vars
  (implies (and (subsetp (termlist-vars x) vars)
                (pseudo-var-list-p vars))
           (iff (urw-ev (disjoin x) (pairlis$ vars (urw-ev-list vars a)))
                (urw-ev (disjoin x) a)))
  :hints (("goal" :induct (len x)
           :in-theory (enable urw-ev-disjoin-when-consp)
           :expand ((termlist-vars x)))))

                       
(define urewrite-clause ((clause pseudo-term-listp)
                         (a pseudo-term-subst-p)
                         state)
  :returns (ans pseudo-term-listp)
  (if (atom clause)
      nil
    (b* ((lit (urewrite-term (car clause) a t 10000 state)))
      (pseudo-term-case lit
        :quote (if lit.val
                   (list lit)
                 (urewrite-clause (cdr clause) a state))
        :otherwise
    (cons lit (urewrite-clause (cdr clause) a state)))))
  ///

  (defret urewrite-clause-correct
    (implies (and (urw-ev-meta-extract-global-facts :state state0)
                  (equal (w state0) (w state)))
             (iff (urw-ev (disjoin ans) env)
                  (urw-ev (disjoin clause) (urw-ev-alist a env))))
    :hints(("Goal" :in-theory (enable urw-ev-disjoin-when-consp)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance urw-ev-when-pseudo-term-quote
                         (x (urewrite-term (car clause) a t 10000 state))
                         (a env)))
                  :in-theory (disable urw-ev-when-pseudo-term-quote))))))

(local (defthm pseudo-term-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (pseudo-term-listp x))
         :hints(("Goal" :in-theory (enable pseudo-termp pseudo-var-list-p)))))

;; (local (defthm pseudo-term-subst-p-of-pairlis$
;;          (implies (and (pseudo-var-list-p vars)
;;                        (pseudo-term-listp vals))
;;                   (pseudo-term-subst-p (pairlis$ vars vals)))
;;          :hints(("Goal" :in-theory (enable pairlis$)))))

(local (include-book "system/f-put-global" :dir :system))

(define urewrite-check-trivial-clause ((clause pseudo-term-listp))
  (b* (((when (atom clause)) nil)
       (lit (car clause))
       ((when (pseudo-term-case lit :quote lit.val :otherwise nil))
        t))
    (urewrite-check-trivial-clause (cdr clause)))
  ///
  (defthm eval-clause-when-urewrite-check-trivial-clause
    (implies (urewrite-check-trivial-clause clause)
             (urw-ev (disjoin clause) a))))

(define urewrite-return-clause ((clause pseudo-term-listp))
  :returns (clauses)
  (and (not (urewrite-check-trivial-clause clause))
       (list clause))
  ///
  (defret <fn>-correct
    (iff (urw-ev (conjoin-clauses clauses) a)
         (urw-ev (disjoin clause) a))))
     


(define urewrite-clause-proc ((clause pseudo-term-listp)
                              ens
                              state)
  (b* ((state (f-put-global 'urewrite-ens ens state))
       (vars (termlist-vars clause)))
    (value (urewrite-return-clause
            (urewrite-clause clause (pairlis$ vars vars) state))))
  ///
  (defthm urewrite-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (urw-ev-meta-extract-global-facts)
                  (urw-ev (conjoin-clauses (clauses-result (urewrite-clause-proc clause ens state))) a))
             (urw-ev (disjoin clause) a))
    :rule-classes :clause-processor))

(define call-urewrite-clause-proc (&optional (pspv 'pspv))
  :mode :program
  `(:clause-processor
    (urewrite-clause-proc
     clause
     ',(access acl2::rewrite-constant 
               (access acl2::prove-spec-var pspv :rewrite-constant)
               :current-enabled-structure)
     state)))


#||

(defthm nth-of-update-nth-lemma
  (equal (nth 5 (update-nth 4 v x))
         (nth 5 x)))

(defthm equal-x-x
  (equal (equal x x) t))

(defthm bar
  (equal (nth (+ 1 4) (update-nth (+ 1 3) v x))
         (nth (+ 2 3) x))
  :hints ((call-urewrite-clause-proc)))

||#
