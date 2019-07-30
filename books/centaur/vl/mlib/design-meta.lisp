; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)

(defsection vl-design-p-meta
  :parents (mlib vl-design-p)
  :short "Special meta-rule to apply unconditional @(see vl-design-p) rules
          more aggressively."
  :long "<p>This meta rule can simplify:</p>
@({
   (vl-design-p (fn ...)) --> t
      when (fn ...) is known to unconditionally return a design-p

   (vl-design-p (hide (fn ...))) --> t
      when (fn ...) is known to unconditionally return a design-p
})

<p>And it can apply both of these rewrites when @('(fn ...)') is actually a
suitable lambda that expands to a call of @('(fn ...)').  Notably this includes
the kinds of lambdas that are produced by the @('mv') bindings for
@(see vl-design-propagate-errors).</p>

<p>We develop this rule to avoid a quadratic blowup in the size of our terms
when applying a long sequence of transforms such as:</p>

@({
      ((mv good bad) (vl-design-propagate-errors good bad))
      (good          ...)
      ((mv good bad) (vl-design-propagate-errors good bad))
      (good          ...)
      ((mv good bad) (vl-design-propagate-errors good bad))
      (good          ...)
      ((mv good bad) (vl-design-propagate-errors good bad))
})

<p>If we do nothing, then each call of @(see vl-design-propagate-errors) sort
of duplicates everything above it, and even with unconditional rules about
@('(vl-design-p (fn ...))') for each transform, the proof slows to a crawl.</p>

<p>After tinkering with this for awhile, our strategy is to use @(see hide)
in the above calls, basically like this:</p>

@({
      ((mv good bad) (vl-design-propagate-errors (hide good) (hide bad)))
})

<p>We then need some way to resolve the guards of @(see
vl-design-propagate-errors), and this meta rule works well.</p>")

(local (xdoc::set-default-parents xdoc::vl-design-p-meta))

(defevaluator des-ev des-ev-list
  ((hide x)
   (vl-design-p x)
;   (vl-design-propagate-errors good bad)
   (equal x y)
;   (mv-nth n l)
   ;; supporting stuff for meta-extract
   (if a b c)
   (implies a b)
   (iff a b)
   (not a)
   (typespec-check ts x)
   ;; supporting stuff for def-unify
   (binary-+ a b)
   (cons a b)))

(acl2::def-meta-extract des-ev des-ev-list)
(acl2::def-unify des-ev des-ev-alist)

;; Speed hint since case-match gets expensive
(local (in-theory (disable default-car
                           default-cdr
                           acl2::consp-of-car-when-alistp
                           acl2::alistp-of-cdr)))

;; We definitely don't want to look at these.
(local (in-theory (disable fgetprop w)))

(std::defaggrify-defrec rewrite-rule)

(defthm rewrite-rule-term-redef
  (equal (acl2::rewrite-rule-term x)
         (b* (((acl2::rewrite-rule x) x))
           (if (eq x.subclass 'acl2::meta)
               ''t
             `(implies ,(conjoin x.hyps)
                       (,x.equiv ,x.lhs ,x.rhs))))))

#!ACL2 ;; BOZO these should probably be disabled by default
(local (in-theory (disable rewrite-rule->lhs
                           rewrite-rule->rhs
                           rewrite-rule->equiv
                           rewrite-rule->hyps
                           rewrite-rule->subclass
                           rewrite-rule-term)))

(define vl-rule-unconditionally-proves-p
  :short "Recognize rewrite rules that unconditionally prove some @('term')."
  ((term pseudo-termp              "The term we want to prove.")
   (rule acl2::weak-rewrite-rule-p "Any rewrite rule."))
  :returns (proves-p "Does this rule unconditionally establish @('term')?")
  (b* (((acl2::rewrite-rule rule) rule) ;; hell yes!
       ((unless (and (pseudo-termp rule.lhs)
                     (mbt (pseudo-termp term))))
        (raise "Malformed rewrite rule ~x0" rule))
       ((mv ok ?unify-subst)
        (acl2::simple-one-way-unify rule.lhs term nil)))
    (and ok
         (equal rule.rhs ''t)
         (or (equal rule.equiv 'equal)
             (equal rule.equiv 'iff))
         (not rule.hyps)
         (not (eq rule.subclass 'acl2::meta))))
  ///
  (local (in-theory (enable vl-rule-unconditionally-proves-p)))

  (local (defthmd crock
           ;; This is what meta-extract gives us.  It roughly means, "the rule is
           ;; true for any variable bindings."
           (implies (and (member rule (fgetprop fn 'acl2::lemmas nil (w st)))
                         (des-ev-meta-extract-global-facts)
                         (equal (w st) (w state)))
                    (des-ev (acl2::rewrite-rule-term rule) alist))
           :hints(("Goal"
                   :in-theory (disable acl2::rewrite-rule-term
                                       DES-EV-META-EXTRACT-LEMMA-TERM
                                       fgetprop w)
                   :use ((:instance DES-EV-META-EXTRACT-LEMMA-TERM
                                    (acl2::rule rule)
                                    (acl2::fn fn)
                                    (acl2::st st)
                                    (acl2::a alist)))))))

  (local (defthm rewrite-eval-under-unify
           (b* (((mv ok subst) (acl2::simple-one-way-unify pat term alist)))
             (implies (and ok
                           (pseudo-termp term)
                           (pseudo-termp pat))
                      (equal (des-ev term a)
                             (des-ev pat (des-ev-alist subst a)))))))

  (local (in-theory (disable simple-one-way-unify-with-des-ev)))

  (defthm vl-rule-unconditionally-proves-p-correct
    (implies (and (vl-rule-unconditionally-proves-p term rule)
                  ;; meta-extract hyps
                  (member rule (fgetprop fn 'acl2::lemmas nil (w st)))
                  (des-ev-meta-extract-global-facts)
                  (equal (w st) (w state)))
             (des-ev term alist))
    :hints(("Goal"
            :use ((:instance crock
                             (alist
                              (b* (((acl2::rewrite-rule rule) rule)
                                   ((mv ?ok unify-subst)
                                    (acl2::simple-one-way-unify rule.lhs term nil)))
                                (des-ev-alist unify-subst alist)))))))))


(deflist rewrite-rule-list-p (x)
  (acl2::weak-rewrite-rule-p x)
  :elementp-of-nil nil)

;; BOZO could probably memoize this to make it fast, but I'm not going to
;; bother for now because it's not clear who should clear the table...
;; (memoize 'rewrite-rule-list-p :recursive nil)

(define vl-some-rule-unconditionally-proves-p
  ((term  pseudo-termp        "The term we want to prove.")
   (rules rewrite-rule-list-p "Any rewrite rule."))
  :returns (proves-p)
  (if (atom rules)
      nil
    (or (vl-rule-unconditionally-proves-p term (car rules))
        (vl-some-rule-unconditionally-proves-p term (cdr rules))))
  ///
  (defthm vl-some-rule-unconditionally-proves-p-correct
    (implies (and (vl-some-rule-unconditionally-proves-p term rules)
                  ;; meta-extract hyps
                  (subsetp rules (fgetprop fn 'acl2::lemmas nil (w st)))
                  (des-ev-meta-extract-global-facts)
                  (equal (w st) (w state)))
             (des-ev term alist))))

;; BOZO find me a home
(defsection unquote-lst
  (defund unquote-lst (x)
    (declare (xargs :guard (and (pseudo-term-listp x)
                                (acl2::quote-listp x))))
    (if (atom x)
        nil
      (cons (acl2::unquote (car x))
            (unquote-lst (cdr x)))))

  (local (in-theory (enable unquote-lst)))

  (defthm kwote-lst-of-unquote-lst-when-quote-listp
    (implies (and (acl2::quote-listp x)
                  (pseudo-term-listp x))
             (equal (kwote-lst (unquote-lst x))
                    x)))

  (defthm des-ev-list-when-quote-listp
    (implies (acl2::quote-listp x)
             (equal (des-ev-list x a)
                    (unquote-lst x)))))



(define vl-obviously-true-p ((term pseudo-termp) state)
  (b* (((unless (consp term)) nil)
       ((when (eq (car term) 'quote)) (cadr term))
       ((unless (symbolp (car term))) nil)
       ((cons fn args) term)
       (win-by-eval (and (acl2::quote-listp args)
                         (b* (((mv err val)
                               (acl2::magic-ev-fncall-logic fn (unquote-lst args) state)))
                           (and (not err) val))))
       ((when win-by-eval)
        t)
       (rules (fgetprop fn 'acl2::lemmas nil (w state)))
       ((unless (rewrite-rule-list-p rules))
        (raise "Invalid rewrite rules???")))
    (vl-some-rule-unconditionally-proves-p term rules))
  ///
  (defthm vl-obviously-true-p-correct
    (implies (and (vl-obviously-true-p term st)
                  (des-ev-meta-extract-global-facts)
                  (equal (w st) (w state)))
             (des-ev term alist))
    :hints(("Goal"
            :in-theory (e/d (des-ev-constraint-0)
                            (vl-some-rule-unconditionally-proves-p-correct
                                des-ev-meta-extract-fncall))
            :use ((:instance vl-some-rule-unconditionally-proves-p-correct
                             (rules (fgetprop (car term) 'acl2::lemmas nil (w st)))
                             (term term)
                             (fn (car term)))
                  (:instance des-ev-meta-extract-fncall
                             (acl2::fn (car term))
                             (acl2::st st)
                             (acl2::arglist (unquote-lst (cdr term)))))))))

(define vl-prove-design-p-base ((term pseudo-termp) state)
  (case-match term
    ((('lambda (var) ('mv-nth ('quote idx) var)) fncall)
     (and var
          (symbolp var)
          (vl-obviously-true-p
           `(vl-design-p (mv-nth ',idx ,fncall))
           state)))
    (& (vl-obviously-true-p `(vl-design-p ,term) state)))
  ///
  (defthm vl-prove-design-p-base-correct
    (implies (and (vl-prove-design-p-base x st)
                  (des-ev-meta-extract-global-facts)
                  (equal (w st) (w state)))
             (vl-design-p (des-ev x alist)))
    :hints(("Goal"
            :in-theory (e/d (des-ev-constraint-0)
                            (vl-obviously-true-p-correct))
            :use ((:instance vl-obviously-true-p-correct
                             (term `(vl-design-p ,x)))
                  (:instance vl-obviously-true-p-correct
                             (term
                              (case-match x
                                ((('lambda (var) ('mv-nth ('quote idx) var)) fncall)
                                 (declare (ignore var))
                                 `(vl-design-p (mv-nth ',idx ,fncall)))))))))))


(define vl-prove-design-p ((term pseudo-termp) state)
  (or (vl-prove-design-p-base term state)
      (case-match term
        ((('lambda (var) var) body)
         (and var
              (symbolp var)
              (vl-prove-design-p body state)))
        ((('lambda & body) . &)
         (vl-prove-design-p body state))
        (&
         nil)))
  ///
  (local (in-theory (enable pairlis$)))
  (local (defun-nx my-induct (term alist state)
           (declare (ignorable alist)
                    (xargs :stobjs state :verify-guards nil))
           (or (vl-prove-design-p-base term state)
               (case-match term
                 ((('lambda (var) var) body)
                  (declare (ignore var))
                  (my-induct body alist state))
                 ((('lambda formals body) . actuals)
                  (my-induct body (pairlis$ formals (des-ev-list actuals alist)) state))
                 (&
                  nil)))))
  (defthm vl-prove-design-p-correct
    (implies (and (vl-prove-design-p x st)
                  (des-ev-meta-extract-global-facts)
                  (equal (w st) (w state)))
             (vl-design-p (des-ev x alist)))
    :hints(("Goal"
            :induct (my-induct x alist st)))))

(define vl-design-p-of-hide-meta ((x pseudo-termp) mfc state)
  (declare (ignore mfc))
  (case-match x
    (('vl-design-p ('hide body))
     (if (vl-prove-design-p body state)
         ''t
       x))
    (&
     x))
  ///
  (defthm vl-design-p-of-hide-meta-correct
    (implies (des-ev-meta-extract-global-facts)
             (equal (des-ev x alist)
                    (des-ev (vl-design-p-of-hide-meta x mfc state) alist)))
    :rule-classes ((:meta :trigger-fns (vl-design-p)))
    :hints(("Goal" :expand ((:free (x) (hide x)))))))
