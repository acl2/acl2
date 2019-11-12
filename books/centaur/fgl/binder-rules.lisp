; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "rules")
(include-book "centaur/meta/equivalence" :dir :system)
(include-book "clause-processors/generalize" :dir :system) ;; for new-symbol
(include-book "arith-base") ;; for unequiv
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable pseudo-termp
                           pseudo-term-listp
                           acl2::pseudo-termp-opener
                           w)))

;; get theorems from locally included books
(local (fty::deflist fgl-binder-rulelist :elt-type fgl-binder-rule :true-listp t))


(local
 (defthm symbol-listp-when-pseudo-var-list-p
   (implies (pseudo-var-list-p x)
            (symbol-listp x))))

(defthm pseudo-var-list-p-of-append
  (implies (and (pseudo-var-list-p x)
                (pseudo-var-list-p y))
           (pseudo-var-list-p (append x y))))

(define fgl-binder-rule-free-var ((x fgl-binder-rule-p))
  :guard (fgl-binder-rule-case x :brewrite)
  :returns (new-var pseudo-var-p :rule-classes :type-prescription)
  (b* (((fgl-binder-rule-brewrite x))
       (used-vars (append (term-vars x.rhs)
                          (termlist-vars x.lhs-args)
                          (termlist-vars x.hyps))))
    (acl2::new-symbol 'fgl-binder-free-var used-vars))
  ///
  (defret <fn>-not-member-list-when-subsetp-of-used-vars
    (b* (((fgl-binder-rule-brewrite x)))
      (implies (subsetp lst (append (term-vars x.rhs)
                                    (termlist-vars x.lhs-args)
                                    (termlist-vars x.hyps)))
               (not (member new-var lst))))
    :hints (("goal" :use ((:instance acl2::new-symbol-unique
                           (base 'fgl-binder-free-var)
                           (avoid (b* (((fgl-binder-rule-brewrite x)))
                                    (append (term-vars x.rhs)
                                            (termlist-vars x.lhs-args)
                                            (termlist-vars x.hyps))))))
             :in-theory (disable acl2::new-symbol-unique)))))
    


(define fgl-binder-rule-term ((x fgl-binder-rule-p))
  :returns (term pseudo-termp)
  :prepwork ((local (in-theory (enable pseudo-termp))))
  (fgl-binder-rule-case x
    :brewrite (b* ((free-var (fgl-binder-rule-free-var x)))
                `(implies (if ,(conjoin x.hyps)
                              (,x.r-equiv ,free-var ,x.rhs)
                            'nil)
                          (,x.equiv (,x.lhs-fn ,free-var . ,x.lhs-args)
                                    ,free-var)))
    :otherwise ''t))

(define fgl-binder-rule-equiv-term ((x fgl-binder-rule-p))
  :returns (term pseudo-termp)
  (fgl-binder-rule-case x
    :brewrite (cmr::equiv-rel-term x.r-equiv)
    :otherwise ''t))






(local
 (defthmd rules-ev-when-theoremp
   (implies (rules-ev-theoremp x)
            (rules-ev x a))
   :hints (("goal" :use rules-ev-falsify))))

(local (acl2::def-functional-instance
         rules-ev-equiv-rel-term-implies-reflexive
         cmr::equiv-rel-term-implies-reflexive
         ((cmr::equiv-ev rules-ev)
          (cmr::equiv-ev-list rules-ev-list)
          (cmr::equiv-ev-falsify rules-ev-falsify))
         :hints(("Goal" :in-theory (enable rules-ev-when-theoremp
                                           rules-ev-of-fncall-args)))))

(local (acl2::def-functional-instance
         rules-ev-equiv-rel-term-implies-symmetric
         cmr::equiv-rel-term-implies-symmetric
         ((cmr::equiv-ev rules-ev)
          (cmr::equiv-ev-list rules-ev-list)
          (cmr::equiv-ev-falsify rules-ev-falsify))))

(local (acl2::def-functional-instance
         rules-ev-equiv-rel-term-implies-transitive
         cmr::equiv-rel-term-implies-transitive
         ((cmr::equiv-ev rules-ev)
          (cmr::equiv-ev-list rules-ev-list)
          (cmr::equiv-ev-falsify rules-ev-falsify))))


(define rules-ev-good-fgl-binder-rule-p ((x fgl-binder-rule-p))
  (and (rules-ev-theoremp (fgl-binder-rule-term x))
       (rules-ev-theoremp (fgl-binder-rule-equiv-term x)))
  ///
  (local (in-theory (enable rules-ev-when-theoremp)))

  (defthm rules-ev-good-fgl-binder-rule-p-implies-fgl-binder-rule-term
    (implies (rules-ev-good-fgl-binder-rule-p x)
             (rules-ev (fgl-binder-rule-term x) a)))

  (defthm rules-ev-good-fgl-binder-rule-p-implies-fgl-binder-rule-equiv-term
    (implies (rules-ev-good-fgl-binder-rule-p x)
             (rules-ev (fgl-binder-rule-equiv-term x) a))))

(define rules-ev-good-fgl-binder-rules-p ((x fgl-binder-rulelist-p))
  (if (atom x)
      t
    (and (rules-ev-good-fgl-binder-rule-p (car x))
         (rules-ev-good-fgl-binder-rules-p (cdr x))))
  ///

  (defthm rules-ev-good-fgl-binder-rules-p-of-append
    (implies (and (rules-ev-good-fgl-binder-rules-p x)
                  (rules-ev-good-fgl-binder-rules-p y))
             (rules-ev-good-fgl-binder-rules-p (append x y)))))



(define fgl-equivp ((fn pseudo-fnsym-p) (w plist-worldp))
  (b* ((fn (pseudo-fnsym-fix fn)))
    (or (eq fn 'equal)
        (eq fn 'iff)
        (eq fn 'unequiv)
        (cmr::ensure-equiv-relationp fn w)))
  ///

  (local (acl2::def-functional-instance
           rules-ev-ensure-equiv-relationp-correct
           cmr::ensure-equiv-relationp-correct
           ((cmr::equiv-ev rules-ev)
            (cmr::equiv-ev-list rules-ev-list)
            (cmr::equiv-ev-falsify rules-ev-falsify)
            (cmr::equiv-ev-meta-extract-global-badguy rules-ev-meta-extract-global-badguy))
           :hints((and stable-under-simplificationp
                       '(:use rules-ev-meta-extract-global-badguy)))))
  
  (defthm fgl-equivp-correct
    (implies (and (rules-ev-meta-extract-global-facts)
                  (fgl-equivp fn (w state)))
             (rules-ev (cmr::equiv-rel-term fn) a))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable cmr::equiv-rel-term)))))

  (defthm fgl-equivp-correct1
    (implies (and (rules-ev-meta-extract-global-facts)
                  (fgl-equivp fn (w state))
                  (pseudo-fnsym-p fn))
             (and (rules-ev (list fn x x) a)
                  (implies (rules-ev (list fn x y) a)
                           (rules-ev (list fn y x) a))
                  (implies (and (rules-ev (list fn x y) a)
                                (rules-ev (list fn y z) a))
                           (rules-ev (list fn x z) a))))
    :hints (("goal" :use ((:instance fgl-equivp-correct
                           (a (rules-ev-falsify (cmr::equiv-rel-term fn)))))
             :in-theory (disable fgl-equivp-correct
                                 fgl-equivp))))


  (defthm fgl-equivp-correct2
    (implies (and (rules-ev-meta-extract-global-facts)
                  (fgl-equivp fn (w state)))
             (and (rules-ev (pseudo-term-fncall fn (list x x)) a)
                  (implies (rules-ev (pseudo-term-fncall fn (list x y)) a)
                           (rules-ev (pseudo-term-fncall fn (list y x)) a))
                  (implies (and (rules-ev (pseudo-term-fncall fn (list x y)) a)
                                (rules-ev (pseudo-term-fncall fn (list y z)) a))
                           (rules-ev (pseudo-term-fncall fn (list x z)) a))))
    :hints(("Goal" :in-theory (disable fgl-equivp)))))


(local (defthm equal-of-len
         (implies (syntaxp (Quotep n))
                  (equal (equal (len x) n)
                         (cond ((equal n 0) (atom x))
                               ((zp n) nil)
                               ((consp x) (equal (len (cdr x)) (1- n)))
                               (t nil))))))

(local (defthm rules-ev-conjoin-of-pseudo-term-list-fix
         (iff (rules-ev (conjoin (pseudo-term-list-fix x)) env)
              (rules-ev (conjoin x) env))
         :hints(("Goal" :induct (len x)
                 :expand ((pseudo-term-list-fix x))))))

(define fgl-binder-rule-find-binder-hyp ((var pseudo-var-p) (hyps pseudo-term-listp) (w plist-worldp))
  :returns (mv ok
               (vequiv pseudo-fnsym-p)
               (rhs pseudo-termp)
               (rest-hyps pseudo-term-listp))
  :prepwork ((local (include-book "centaur/misc/equal-sets" :dir :system)))

  (b* (((when (atom hyps))
        (mv nil nil nil nil))
       (hyp (car hyps))
       ((when (pseudo-term-case hyp
                :fncall (and (eql (len hyp.args) 2)
                             (eq (car hyp.args) (pseudo-term-var var))
                             (fgl-equivp hyp.fn w))
                :otherwise nil))
        (mv t
            (pseudo-term-fncall->fn hyp)
            (second (pseudo-term-call->args hyp))
            (pseudo-term-list-fix (cdr hyps))))
       ((mv ok vequiv rhs rest-hyps)
        (fgl-binder-rule-find-binder-hyp var (cdr hyps) w)))
    (mv ok vequiv rhs
        (cons (pseudo-term-fix hyp)
              rest-hyps)))
  ///
  (defret <fn>-correct-when-hyps
    (implies (and ok
                  (rules-ev (conjoin hyps) env))
             (and (rules-ev (list vequiv (pseudo-term-var var) rhs) env)
                  (rules-ev (conjoin rest-hyps) env)))
    :hints(("Goal" :in-theory (enable RULES-EV-CONJOIN-WHEN-CONSP))))

  (defret <fn>-correct-when-not-hyps
    (implies (and ok
                  (not (rules-ev (conjoin hyps) env))
                  (rules-ev (list vequiv (pseudo-term-var var) rhs) env))
             (not (rules-ev (conjoin rest-hyps) env))))

  (defretd <fn>-correct-rewrite-hyps
    (implies ok
             (iff (rules-ev (conjoin hyps) env)
                  (and (rules-ev (list vequiv (pseudo-term-var var) rhs) env)
                       (rules-ev (conjoin rest-hyps) env)))))

  (local (defthm consolidate-consts
           (implies (and (syntaxp (and (quotep a) (quotep c)))
                         (acl2-numberp a) (acl2-numberp c))
                    (equal (equal (+ a b) c)
                           (equal (fix b) (- c a))))))

  (local (defthm expand-len-equals
           (implies (syntaxp (quotep n))
                    (equal (equal (len x) n)
                           (cond ((equal n 0) (atom x))
                                 ((zp n) nil)
                                 ((consp x) (equal (len (cdr x)) (1- n)))
                                 (t nil))))))

  (local (defthm termlist-vars-when-consp
           (implies (consp x)
                    (equal (cmr::termlist-vars x)
                           (union-equal (cmr::termlist-vars (cdr x))
                                        (cmr::term-vars (car x)))))
           :hints (("goal" :expand ((cmr::termlist-vars x))))))


  (local (in-theory (disable len pseudo-termp pseudo-term-listp)))
                  
  (defretd <fn>-vars-rewrite-hyps
    (implies ok
             (acl2::set-equiv (cmr::termlist-vars hyps)
                              (cons (pseudo-var-fix var)
                                    (append (cmr::term-vars rhs)
                                            (cmr::termlist-vars rest-hyps)))))
    :hints(("Goal" :induct <call>
            :expand ((cmr::termlist-vars hyps)
                     (cmr::term-vars (pseudo-term-var var))
                     (cmr::term-vars (car hyps))))
           (acl2::witness :ruleset acl2::set-reasoning-no-consp)))

  (defretd fgl-equivp-when-<fn>
    (implies ok
             (fgl-equivp vequiv w))))


(local (defthm not-equal-quote-when-pseudo-fnsym-p
         (implies (pseudo-fnsym-p x)
                  (not (equal x 'quote)))))

(local
 (cmr::defthm-term-vars-flag
   (defthm rules-ev-of-cons-non-term-var
     (implies (not (member v (cmr::term-vars x)))
              (equal (rules-ev x (cons (cons v val) env))
                     (rules-ev x env)))
     :hints ('(:expand ((cmr::term-vars x))
               :in-theory (enable rules-ev-of-fncall-args
                                  rules-ev-when-pseudo-term-call)))
     :flag cmr::term-vars)
   (defthm rules-ev-list-of-cons-non-term-var
     (implies (not (member v (cmr::termlist-vars x)))
              (equal (rules-ev-list x (cons (cons v val) env))
                     (rules-ev-list x env)))
     :hints ('(:expand ((cmr::termlist-vars x))))
     :flag cmr::termlist-vars)))

(local (defthm pseudo-term-fix-of-fncall
         (implies (pseudo-fnsym-p fn)
                  (equal (pseudo-term-fix (cons fn args))
                         (pseudo-term-fncall fn
                                             (pseudo-term-list-fix args))))
         :hints(("Goal" :in-theory (enable pseudo-term-fncall)
                 :expand ((pseudo-term-fix (cons fn args)))))))

(local (defthm term-vars-of-fncall
         (implies (pseudo-fnsym-p fn)
                  (equal (term-vars (cons fn args))
                         (term-vars (pseudo-term-fncall fn args))))
         :hints(("Goal" :use pseudo-term-fix-of-fncall
                 :in-theory (disable pseudo-term-fix-of-fncall)))))

(defthm term-vars-of-conjoin
  (implies (not (member v (termlist-vars x)))
           (not (member v (term-vars (conjoin x)))))
  :hints(("Goal" :in-theory (enable conjoin
                                    termlist-vars)
          :induct (len x)
          :expand ((:free (x y) (term-vars (pseudo-term-fncall x y)))
                   (:free (x y) (term-vars (cons x y)))))))

(define rewrite-rule-term-from-components ((lhs pseudo-termp)
                                           (rhs pseudo-termp)
                                           (hyps pseudo-term-listp)
                                           (equiv pseudo-fnsym-p))
  :returns (term pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
  `(implies ,(conjoin (pseudo-term-list-fix hyps))
            (,(pseudo-fnsym-fix equiv)
             ,(pseudo-term-fix lhs)
             ,(pseudo-term-fix rhs)))
  ///
  (defthm rewrite-rule-term-from-components-by-rewrite-rule-term
    (b* (((acl2::rewrite-rule x)))
      (implies (and (rules-ev (acl2::rewrite-rule-term x) a)
                    (not (equal x.subclass 'acl2::meta))
                    (pseudo-fnsym-p x.equiv))
               (rules-ev (rewrite-rule-term-from-components
                          x.lhs x.rhs x.hyps x.equiv)
                         a)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-rule-term-alt-def
                                    rules-ev-of-fncall-args)
                                   (acl2::rewrite-rule-term)))))

  (defthm rewrite-rule-term-from-components-by-rewrite-term
    (b* (((cmr::rewrite x)))
      (implies (rules-ev (cmr::rewrite-term x) a)
               (rules-ev (rewrite-rule-term-from-components
                          x.lhs x.rhs x.hyps x.equiv)
                         a)))
    :hints(("Goal" :in-theory (e/d (cmr::rewrite-term))))))
  

(define fgl-binder-rule-from-fields ((lhs pseudo-termp)
                                     (rhs pseudo-termp)
                                     (hyps pseudo-term-listp)
                                     (equiv pseudo-fnsym-p)
                                     (rune fgl-binder-rune-p)
                                     (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rule (implies (not errmsg) (fgl-binder-rule-p rule))))
  (b* ((rune (fgl-binder-rune-fix rune))
       ((unless (pseudo-term-case lhs :fncall))
        (mv (msg "Rule ~x0 has LHS which is not a function call~%" rune) nil))
       ((pseudo-term-fncall lhs))
       ((unless (consp lhs.args))
        (mv (msg "Rule ~x0 has LHS function call with no args, which won't ~
                    work for a binder rule~%" rune)
            nil))
       (var (car lhs.args))
       ((unless (pseudo-term-case var :var))
        (mv (msg "Rule ~x0 has LHS function call whose first argument is ~
                    not a variable, which is required for a binder rule~%" rune)
            nil))
       ((unless (equal (pseudo-term-fix rhs) var))
        (mv (msg "Rule ~x0 has RHS not equal to the variable to be bound, ~
                    which is required for a binder rule~%" rune)
            nil))
       (var (pseudo-term-var->name var))
       ((mv ok vequiv rhs rest-hyps)
        (fgl-binder-rule-find-binder-hyp var hyps w))
       ((unless ok)
        (mv (msg "Rule ~x0 had no hyp of the form ~x1 (where ~x2 is ~x3 and ~
                    VEQUIV is an equivalence relation), which is required for ~
                    a binder rule~%" rune '(vequiv var rhs) 'var var)
            nil))
       ((when (or (cmr::member-termlist-vars var rest-hyps)
                  (cmr::member-termlist-vars var (cdr lhs.args))
                  (cmr::member-term-vars var rhs)))
        (mv (msg "Rule ~x0 is not a valid binder rule because the variable to be bound appears in the ~s1~%"
                 rune
                 (cond ((cmr::member-termlist-vars var rest-hyps) "hyps")
                       ((cmr::member-termlist-vars var (cdr lhs.args)) "LHS arguments beyond the first")
                       ((cmr::member-term-vars var rhs) "RHS")))
            nil)))
    (mv nil (make-fgl-binder-rule-brewrite :rune rune
                                           :hyps rest-hyps
                                           :equiv equiv
                                           :r-equiv vequiv
                                           :lhs-fn lhs.fn
                                           :lhs-args (cdr lhs.args)
                                           :rhs rhs)))
  ///
  (defret fgl-binder-rule-equiv-term-of-<fn>
    (implies (and (not errmsg)
                  ;; (rules-ev-good-fgl-binder-rule-p x)
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev (fgl-binder-rule-equiv-term rule) a))
    :hints(("Goal" :in-theory (enable fgl-binder-rule-equiv-term
                                      fgl-equivp-when-fgl-binder-rule-find-binder-hyp))))

  (local (defthm consp-member-under-iff
           (iff (consp (member k x)) (member k x))))

  (local (defthm subsetp-termlist-vars-cdr-args
           (implies (pseudo-term-case x :fncall)
                    (subsetp (termlist-vars (cdr (pseudo-term-call->args x)))
                             (term-vars x)))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)
                   :expand ((term-vars x)
                            (termlist-vars (pseudo-term-call->args x)))))))

  (defret fgl-binder-rule-term-of-<fn>
    (implies (and (not errmsg)
                  (rules-ev (rewrite-rule-term-from-components lhs rhs hyps equiv)
                            (cons (cons (pseudo-term-var->name rhs)
                                        (cdr (assoc (fgl-binder-rule-free-var rule) a)))
                                  a))
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev (fgl-binder-rule-term rule) a))
    :hints(("Goal" :in-theory (e/d (fgl-binder-rule-term
                                    rewrite-rule-term-from-components
                                    rules-ev-of-fncall-args
                                    fgl-equivp-when-fgl-binder-rule-find-binder-hyp
                                    fgl-binder-rule-find-binder-hyp-correct-rewrite-hyps
                                    fgl-binder-rule-find-binder-hyp-vars-rewrite-hyps))
            :do-not-induct t)))

  (defret rules-ev-good-fgl-binder-rule-p-of-<fn>
    (implies (and (not errmsg)
                  (rules-ev-theoremp (rewrite-rule-term-from-components lhs rhs hyps equiv))
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rule-p rule))
    :hints (("goal" :in-theory (e/d (rules-ev-good-fgl-binder-rule-p
                                     rules-ev-when-theoremp)
                                    (<fn>))))))


(local (defthm pseudo-fnsym-p-by-symbolp
         (implies (and (symbolp x)
                       (not (equal x 'quote)))
                  (pseudo-fnsym-p x))
         :hints(("Goal" :in-theory (enable pseudo-fnsym-p)))))

(define fgl-binder-rule-from-lemma ((fgl-rune fgl-binder-rune-p) x (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rule (implies (not errmsg) (fgl-binder-rule-p rule))))
  (b* (((unless (pseudo-rewrite-rule-p x)) (mv (msg "Bad rewrite rule: ~x0" x) nil))
       ((acl2::rewrite-rule x))
       ((when (eq x.subclass 'acl2::meta))
        (mv (msg "Rule ~x0 is a :meta rule~%" x.rune) nil)))
    (fgl-binder-rule-from-fields x.lhs x.rhs x.hyps x.equiv fgl-rune w))
  ///
  (defret rules-ev-good-fgl-binder-rule-p-of-<fn>
    (implies (and (not errmsg)
                  (rules-ev-theoremp (acl2::rewrite-rule-term x))
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rule-p rule))
    :hints(("Goal" :in-theory (e/d (rules-ev-when-theoremp)
                                   (acl2::rewrite-rule-term))))))


(define fgl-binder-rules-from-lemmas ((fgl-rune fgl-binder-rune-p) lemmas (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  (b* (((when (atom lemmas)) (mv nil nil))
       ((mv err rule) (fgl-binder-rule-from-lemma fgl-rune (car lemmas) w))
       ((mv err2 rest) (fgl-binder-rules-from-lemmas fgl-rune (cdr lemmas) w)))
    (mv (or err err2)
        (if err rest (cons rule rest))))
  ///
  (defret rules-ev-good-fgl-rules-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rulesp lemmas)
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-binder-rules-p
                                      rules-ev-good-rewrite-rulesp)))))


(define fgl-binder-rule-from-cmr-rewrite ((rune fgl-binder-rune-p) (x cmr::rewrite-p) (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rule (implies (not errmsg) (fgl-binder-rule-p rule))))
  (b* (((cmr::rewrite x)))
    (fgl-binder-rule-from-fields x.lhs x.rhs x.hyps x.equiv rune w))
  ///
  (defret rules-ev-good-fgl-binder-rule-p-of-<fn>
    (implies (and (not errmsg)
                  (rules-ev-theoremp (cmr::rewrite-term x))
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rule-p rule))
    :hints(("Goal" :in-theory (e/d (rules-ev-when-theoremp)
                                   (acl2::rewrite-rule-term))))))

(define fgl-binder-rules-from-cmr-rewrites ((fgl-rune fgl-binder-rune-p)
                                      (x cmr::rewritelist-p)
                                      (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv err rule) (fgl-binder-rule-from-cmr-rewrite fgl-rune (car x) w))
       ((mv err2 rest) (fgl-binder-rules-from-cmr-rewrites fgl-rune (cdr x) w)))
    (mv (or err err2)
        (if err rest (cons rule rest))))
  ///
  (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
    (implies (and (rules-ev-theoremp (conjoin (cmr::rewritelist-terms x)))
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-binder-rules-p
                                      cmr::rewritelist-terms)))))


(define fgl-binder-rules-from-formula ((form pseudo-termp)
                                       (fgl-rune fgl-binder-rune-p)
                                       (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  (b* (((mv err rewrites) (cmr::parse-rewrites-from-term form world))
       ((mv err2 rules) (fgl-binder-rules-from-cmr-rewrites fgl-rune rewrites world)))
    (mv (or err err2) rules))
  ///

  (defret rules-ev-good-fgl-binder-rule-p-of-<fn>
    (implies (and (rules-ev-theoremp form)
                  (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-when-theoremp)))))



(define fgl-binder-rules-from-rewrite (rune (fgl-rune fgl-binder-rune-p) fn-lemma-map (w plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  :guard-hints (("goal" :in-theory (enable pseudo-fnsym-p)))
  (b* ((rw (cdr (hons-get rune fn-lemma-map))))
    (fgl-binder-rules-from-lemmas fgl-rune rw w))
  ///
  (defret rules-ev-good-fgl-binder-rule-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
                  (rules-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))))

(define fgl-binder-rules-from-rune ((rune fgl-binder-rune-p) (fn-lemma-map) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  :prepwork ((local (defthm fgl-binder-rule-p-of-binder-rune
                      (implies (and (fgl-binder-rune-p x)
                                    (not (fgl-binder-rune-case x :brewrite))
                                    (not (fgl-binder-rune-case x :bformula)))
                               (and (fgl-binder-rule-p x)
                                    (equal (fgl-binder-rule-kind x)
                                           (fgl-binder-rune-kind x))))
                      :hints(("Goal" :in-theory (enable fgl-binder-rune-p
                                                        fgl-binder-rule-p
                                                        fgl-binder-rune-kind
                                                        fgl-binder-rule-kind))))))
  (fgl-binder-rune-case rune
    :brewrite (fgl-binder-rules-from-rewrite `(:rewrite ,rune.name) rune fn-lemma-map world)
    :bformula (b* ((form (acl2::meta-extract-formula-w rune.name world))
                   ((unless (pseudo-termp form))
                    (mv (msg "Formula for ~x0 was not pseudo-termp: ~x1~%" rune.name form) nil)))
               (fgl-binder-rules-from-formula form rune world))
    :otherwise (mv nil (list (fgl-binder-rune-fix rune))))
  ///

  (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
                  (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable rules-ev-good-fgl-binder-rules-p)))
            (and stable-under-simplificationp
                 '(:in-theory (enable rules-ev-good-fgl-binder-rule-p
                                      fgl-binder-rule-term
                                      fgl-binder-rule-equiv-term))))))



(define fgl-binder-rules-from-runes ((runes fgl-binder-runelist-p) (fn-lemma-map) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  (b* (((when (atom runes)) (mv nil nil))
       ((mv errmsg1 rules1) (fgl-binder-rules-from-rune (car runes) fn-lemma-map world))
       ((mv errmsg2 rest) (fgl-binder-rules-from-runes (cdr runes) fn-lemma-map world)))
    (mv (or errmsg1 errmsg2) (append rules1 rest)))
  ///
  (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
    (implies (and (rules-ev-good-rewrite-rule-alistp fn-lemma-map)
                  (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-binder-rules-p rules))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-binder-rules-p)))))


(define fgl-binder-rules-filter-leading-fnsym ((fn pseudo-fnsym-p) (x fgl-binder-rulelist-p))
  :returns (new-x fgl-binder-rulelist-p)
  (b* (((When (atom x)) nil)
       (x1 (car x))
       ((unless (fgl-binder-rule-case x1 :brewrite))
        (cons (fgl-binder-rule-fix x1)
              (fgl-binder-rules-filter-leading-fnsym fn (cdr x))))
       ((fgl-binder-rule-brewrite x1))
       ((when (eq x1.lhs-fn (pseudo-fnsym-fix fn)))
        (cons (fgl-binder-rule-fix x1)
              (fgl-binder-rules-filter-leading-fnsym fn (cdr x)))))
    (fgl-binder-rules-filter-leading-fnsym fn (cdr x)))
  ///
  (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
    (implies (rules-ev-good-fgl-binder-rules-p x)
             (rules-ev-good-fgl-binder-rules-p new-x))
    :hints(("Goal" :in-theory (enable rules-ev-good-fgl-binder-rules-p)))))


(define fgl-binder-rules-lookup ((fn pseudo-fnsym-p) (alist))
  (cdr (hons-get (pseudo-fnsym-fix fn) alist)))

(define fgl-function-binder-rules ((fn pseudo-fnsym-p) (world plist-worldp))
  :returns (mv (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules fgl-binder-rulelist-p))
  (b* ((table (make-fast-alist (table-alist 'fgl-binder-rules world)))
       (fn (pseudo-fnsym-fix fn))
       (runes (fgl-binder-rules-lookup fn table))
       ((unless (fgl-binder-runelist-p runes))
        (mv (msg "Error: entry for ~x0 in the ~x1 table did not satisfy ~x2~%"
                 fn 'fgl-rewrite-rules 'fgl-runelist-p)
            nil))
       (lemmas (fgetprop fn 'acl2::lemmas nil world))
       (map (map-rewrite-rules lemmas nil))
       ((mv err rules1)
        (fgl-binder-rules-from-runes runes map world)))
    (mv err (fgl-binder-rules-filter-leading-fnsym fn rules1)))
  ///
  (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
    (implies (and (rules-ev-meta-extract-global-facts)
                  (equal world (w state)))
             (rules-ev-good-fgl-binder-rules-p rules)))

  (memoize 'fgl-function-binder-rules))

