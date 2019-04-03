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

(include-book "reconstruct")
(local (include-book "clause-processors/join-thms" :dir :system))

(defxdoc resolve-flag-cp
  :parents (mutual-recursion make-flag)
  :short "Clause processor to quickly remove flag junk from the clauses generated after a flag-function induction.")

(local (xdoc::set-default-parents resolve-flag-cp))


(defevaluator flag-ev flag-ev-list
  ((if a b c)
   (not a)
   (equal a b)
   (eql a b)
   (eq a b)
   (acl2::flag-is x))
  :namedp t)

(acl2::def-ev-pseudo-term-fty-support flag-ev flag-ev-list)

(local (acl2::def-join-thms flag-ev))

(local (defthm assoc-of-nonnil
         (implies v
                  (equal (assoc v x)
                         (hons-assoc-equal v x)))))



(define match-flag-equal ((x pseudo-termp)
                          (flag-var pseudo-var-p))
  :returns (mv matchedp obj)
  (pseudo-term-case x
    :fncall (if (member-eq x.fn '(equal eql eq))
                (b* (((list arg1 arg2) x.args))
                  (pseudo-term-case arg1
                    :var (if (eq arg1.name (pseudo-var-fix flag-var))
                             (pseudo-term-case arg2
                               :quote (mv t arg2.val)
                               :otherwise (mv nil nil))
                           (mv nil nil))
                    :quote (pseudo-term-case arg2
                             :var (if (eq arg2.name (pseudo-var-fix flag-var))
                                      (mv t arg1.val)
                                    (mv nil nil))
                             :otherwise (mv nil nil))
                    :otherwise (mv nil nil)))
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret match-flag-equal-implies-eval
    (implies matchedp
             (equal (flag-ev x a)
                    (equal (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)) obj)))))

(define match-flag-not-equal ((x pseudo-termp)
                              (flag-var pseudo-var-p))
  :returns (mv matchedp obj)
  (pseudo-term-case x
    :fncall (if (eq x.fn 'not)
                (match-flag-equal (car x.args) flag-var)
              (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret match-flag-not-equal-implies-eval
    (implies matchedp
             (equal (flag-ev x a)
                    (not (equal (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)) obj))))))

(local (Defthm not-member-of-remove
         (not (member a (remove a x)))))

(local (defthm member-of-remove-split
         (iff (member a (remove b x))
              (and (not (equal a b))
                   (member a x)))))

(local (defthm flag-ev-of-disjoin-pseudo-term-list-fix
         (iff (flag-ev (disjoin (pseudo-term-list-fix x)) a)
              (flag-ev (disjoin x) a))
         :hints(("Goal"
                 :induct (len x)
                 :expand ((pseudo-term-list-fix x))))))

(define scan-clause-for-flag-facts ((x pseudo-term-listp)
                                    (flag-var pseudo-var-p))
  :returns (mv (new-clause pseudo-term-listp)
               (known-value-p booleanp)
               (known-value)
               (eliminated-values true-listp :rule-classes :type-prescription))
  (b* (((when (atom x))
        (mv nil nil nil nil))
       ((mv matched val) (match-flag-not-equal (car x) flag-var))
       ((when matched)
        (mv (cdr (pseudo-term-list-fix x))
            t
            val
            nil))
       ((mv matched val) (match-flag-equal (car x) flag-var))
       ((mv rest known-value-p known-value eliminated-values)
        (scan-clause-for-flag-facts (cdr x) flag-var))
       ((unless matched)
        (mv (cons-with-hint (pseudo-term-fix (car x)) rest x)
            known-value-p known-value eliminated-values))
       ((when known-value-p)
        (mv rest known-value-p known-value nil)))
    (mv rest nil nil (cons val eliminated-values)))
  ///
  (defret scan-clause-for-flag-facts-known-value-correct
    (implies (and known-value-p
                  (not (flag-ev (disjoin x) a)))
             (equal known-value
                    (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)))))

  (defret scan-clause-for-flag-facts-eliminated-values-correct
    (implies (not (flag-ev (disjoin x) a))
             (not (member-equal (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a))
                                eliminated-values))))

  (defret scan-clause-for-flag-facts-new-clause-correct
    (implies (not (flag-ev (disjoin x) a))
             (not (flag-ev (disjoin new-clause) a)))))

(local (defthm true-list-fix-when-true-listp
         (implies (true-listp x)
                  (equal (true-list-fix x) x))))

(local (defthm member-of-true-list-fix
         (iff (member x (true-list-fix y))
              (member x y))))
         
(define flag-facts-p (x)
  (and (consp x)
       (booleanp (car x))
       (or (car x) (true-listp (cdr x))))
  ///
  (define flag-facts-fix ((x flag-facts-p))
    :returns (new-x flag-facts-p)
    (mbe :logic (if (car x)
                    (cons t (cdr x))
                  (cons (car x) (true-list-fix (cdr x))))
         :exec x)
    ///
    (defthm flag-facts-fix-when-flag-facts-p
      (implies (flag-facts-p x)
               (equal (flag-facts-fix x) x)))

    (fty::deffixtype flag-facts :pred flag-facts-p :fix flag-facts-fix :equiv flag-facts-equiv
      :define t)

    (defthm consp-of-flag-facts-fix
      (consp (flag-facts-fix x))
      :rule-classes :type-prescription)))

(define make-flag-facts (known-value-p
                         known-val
                         (eliminated-vals true-listp))
  :returns (facts flag-facts-p
                  :hints(("Goal" :in-theory (enable flag-facts-p))))
  (if known-value-p
      (cons t known-val)
    (cons nil (mbe :logic (true-list-fix eliminated-vals) :exec eliminated-vals)))
  ///
  (defcong iff equal (make-flag-facts known-value-p known-val eliminated-vals) 1))

(define flag-possible-value-p ((x flag-facts-p)
                               (val))
  :guard-hints (("goal" :in-theory (enable flag-facts-p)))
  (b* ((x (flag-facts-fix x)))
    (if (car x)
        (equal val (cdr x))
      (not (member-equal val (cdr x)))))
  ///

  (defthmd flag-possible-value-p-of-make-flag-facts-split
    (equal (flag-possible-value-p (make-flag-facts known-value-p known-val eliminated-vals) val)
           (if known-value-p
               (equal val known-val)
             (not (member val eliminated-vals))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable make-flag-facts)))))
  
  (defthm flag-possible-value-p-of-make-flag-facts-when-known-value
    (equal (flag-possible-value-p (make-flag-facts t known-val eliminated-vals) val)
           (equal val known-val))
    :hints(("Goal" :in-theory (e/d (flag-possible-value-p-of-make-flag-facts-split)
                                   (flag-possible-value-p)))))

  (defthm flag-possible-value-p-of-make-flag-facts-when-eliminated-vals
    (equal (flag-possible-value-p (make-flag-facts nil known-val eliminated-vals) val)
           (not (member val eliminated-vals)))
    :hints(("Goal" :in-theory (e/d (flag-possible-value-p-of-make-flag-facts-split)
                                   (flag-possible-value-p))))))

(define flag-only-value-p ((x flag-facts-p)
                           (val))
  :guard-hints (("goal" :in-theory (enable flag-facts-p)))
  (b* ((x (flag-facts-fix x)))
    (and (car x)
         (equal val (cdr x))))
  ///

  (defthmd flag-only-value-p-of-make-flag-facts-split
    (equal (flag-only-value-p (make-flag-facts known-value-p known-val eliminated-vals) val)
           (if known-value-p
               (equal val known-val)
             nil))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable make-flag-facts)))))
  
  (defthm flag-only-value-p-of-make-flag-facts-when-known-value
    (equal (flag-only-value-p (make-flag-facts t known-val eliminated-vals) val)
           (equal val known-val))
    :hints(("Goal" :in-theory (e/d (flag-only-value-p-of-make-flag-facts-split)
                                   (flag-only-value-p)))))

  (defthm flag-only-value-p-of-make-flag-facts-when-eliminated-vals
    (equal (flag-only-value-p (make-flag-facts nil known-val eliminated-vals) val)
           nil)
    :hints(("Goal" :in-theory (e/d (flag-only-value-p-of-make-flag-facts-split)
                                   (flag-only-value-p)))))

  (defthm flag-possible-value-p-when-only-value-p
    (implies (flag-only-value-p x val)
             (equal (flag-possible-value-p x val2)
                    (equal val2 val)))
    :hints(("Goal" :in-theory (enable flag-possible-value-p)))))

(define clause-get-flag-facts ((x pseudo-term-listp)
                               (flag-var pseudo-var-p))
  :returns (mv (new-clause pseudo-term-listp)
               (flag-facts flag-facts-p))
  (b* (((mv new-clause known-value-p known-val eliminated-vals)
        (scan-clause-for-flag-facts x flag-var)))
    (mv new-clause (make-flag-facts known-value-p known-val eliminated-vals)))
  ///
  (defret clause-get-flag-facts-possible-values-correct
    (implies (not (flag-ev (disjoin x) a))
             (flag-possible-value-p flag-facts
                                    (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a))))
    :hints(("Goal" :in-theory (enable flag-possible-value-p-of-make-flag-facts-split))))

  (defret clause-get-flag-facts-only-value-correct
    (implies (and (not (flag-ev (disjoin x) a))
                  (not (equal (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)) val)))
             (not (flag-only-value-p flag-facts val)))
    :hints(("Goal" :in-theory (enable flag-only-value-p-of-make-flag-facts-split))))

  (defret clause-get-flag-facts-new-clause-correct
    (implies (not (flag-ev (disjoin x) a))
             (not (flag-ev (disjoin new-clause) a)))))
                  

(define match-not ((x pseudo-termp))
  :returns (mv matchedp
               (arg pseudo-termp))
  (pseudo-term-case x
    :fncall (case x.fn
              (not (mv t (car x.args)))
              (equal (cond ((equal (car x.args) ''nil)
                            (mv t (cadr x.args)))
                           ((equal (cadr x.args) ''nil)
                            (mv t (car x.args)))
                           (t (mv nil nil))))
              (if    (cond ((and (equal (cadr x.args) ''nil)
                                 (equal (caddr x.args) ''t))
                            (mv t (car x.args)))
                           (t (mv nil nil))))
              (otherwise (mv nil nil)))
    :otherwise (mv nil nil))
  ///
  (defret match-not-correct
    (implies matchedp
             (equal (flag-ev x a)
                    (not (flag-ev arg a)))))

  (defret match-not-pseudo-term-count
    (implies matchedp
             (< (pseudo-term-count arg) (pseudo-term-count x)))
    :rule-classes :linear))

(define simplify-not ((x pseudo-termp) (iff-p))
  :returns (not-x pseudo-termp)
  (pseudo-term-case x
    :const (pseudo-term-quote (not x.val))
    :var (pseudo-term-fncall 'not (list x))
    :fncall (if iff-p
                (b* (((mv matchedp arg) (match-not x))
                     ((when matchedp) arg))
                  (pseudo-term-fncall 'not (list x)))
              (pseudo-term-fncall 'not (list x)))
    :otherwise (pseudo-term-fncall 'not (list x)))
  ///
  (defthm simplify-not-correct-iff
    (iff (flag-ev (simplify-not x iff-p) a)
         (not (flag-ev x a))))

  (defthm simplify-not-correct-equal
    (equal (flag-ev (simplify-not x nil) a)
           (not (flag-ev x a))))

  (defthm simplify-not-when-iff-p
    (implies (and (syntaxp (not (equal iff-p ''t)))
                  iff-p)
             (equal (simplify-not x iff-p)
                    (simplify-not x t)))))

(define simplify-if ((test pseudo-termp)
                     (then pseudo-termp)
                     (else pseudo-termp)
                     (iff-p))
  ;; Assumes the test is not a quoted val.  Just mainly looking to turn it into a NOT.
  :returns (if-term pseudo-termp)
  (b* ((then (pseudo-term-fix then))
       (else (pseudo-term-fix else))
       ((when (equal then else)) then)
       ((unless (and (pseudo-term-case then :quote)
                     (pseudo-term-case else :quote)))
        (pseudo-term-fncall 'if (list test then else)))
       (thenval (pseudo-term-quote->val then))
       (elseval (pseudo-term-quote->val else))
       ((when iff-p)
        (if thenval
            (if elseval
                ''t
              (pseudo-term-fix test))
          (if elseval
              (simplify-not test t)
            ''nil))))
    (cond ((eq thenval t)
           (cond ((eq elseval t) ''t)
                 (t (pseudo-term-fncall 'if (list test then else)))))
          ((eq thenval nil)
           (cond ((eq elseval t) (simplify-not test nil))
                 ((eq elseval nil) ''nil)
                 (t (pseudo-term-fncall 'if (list test then else)))))
          (T (pseudo-term-fncall 'if (list test then else)))))
  ///
  (defthm simplify-if-correct-iff
    (iff (flag-ev (simplify-if test then else iff-p) a)
         (if (flag-ev test a)
             (flag-ev then a)
           (flag-ev else a))))

  (defthm simplify-if-correct-equal
    (equal (flag-ev (simplify-if test then else nil) a)
           (if (flag-ev test a)
               (flag-ev then a)
             (flag-ev else a))))
  
  (defthm simplify-if-when-iff-p
    (implies (and (syntaxp (not (equal iff-p ''t)))
                  iff-p)
             (equal (simplify-if test then else iff-p)
                    (simplify-if test then else t)))))





(defines term-simplify-flag-conds
  (define term-simplify-flag-conds ((x pseudo-termp)
                                    (iff-p)
                                    (flag-var pseudo-var-p)
                                    (flag-facts flag-facts-p))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :fncall
      (b* (((mv matchedp val) (match-flag-equal x flag-var))
           ((when matchedp)
            (cond ((flag-only-value-p flag-facts val) ''t)
                  ((flag-possible-value-p flag-facts val) (pseudo-term-fix x))
                  (t ''nil)))
           ((mv matchedp arg) (match-not x))
           ((When matchedp)
            (b* ((new-arg (term-simplify-flag-conds arg t flag-var flag-facts)))
              (simplify-not new-arg iff-p)))
           ((when (eq x.fn 'if))
            (b* ((test (term-simplify-flag-conds (car x.args) t flag-var flag-facts))
                 ((when (pseudo-term-case test :quote))
                  (if (pseudo-term-quote->val test)
                      (term-simplify-flag-conds (cadr x.args) iff-p flag-var flag-facts)
                    (term-simplify-flag-conds (caddr x.args) iff-p flag-var flag-facts)))
                 (then (term-simplify-flag-conds (cadr x.args) iff-p flag-var flag-facts))
                 (else (term-simplify-flag-conds (caddr x.args) iff-p flag-var flag-facts)))
              (simplify-if test then else iff-p)))
           (args (termlist-simplify-flag-conds x.args flag-var flag-facts)))
        (pseudo-term-fncall x.fn args))
      :lambda
      (b* ((args (termlist-simplify-flag-conds x.args flag-var flag-facts)))
        (pseudo-term-lambda-with-hint
         x.formals x.body args x))
      :otherwise (pseudo-term-fix x)))
  (define termlist-simplify-flag-conds ((x pseudo-term-listp)
                                        (flag-var pseudo-var-p)
                                        (flag-facts flag-facts-p))
    :returns (new-x pseudo-term-listp)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (cons-with-hint (term-simplify-flag-conds (car x) nil flag-var flag-facts)
                      (termlist-simplify-flag-conds (cdr x) flag-var flag-facts)
                      x)))
  ///
  
  (defret len-of-termlist-simplify-flag-conds
    (equal (len new-x) (len x))
    :hints (("Goal" :induct (len x)
             :expand (<call>)))
    :fn termlist-simplify-flag-conds)

  (verify-guards term-simplify-flag-conds)

  (local (in-theory (disable FLAG-EV-WHEN-PSEUDO-TERM-FNCALL)))

  (defret-mutual term-simplify-flag-conds-correct
    (defret term-simplify-flag-conds-correct-iff
      (implies (flag-possible-value-p flag-facts
                                      (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)))
               (iff (flag-ev new-x a)
                    (flag-ev x a)))
      :hints ('(:expand (<call>)
                :in-theory (enable flag-ev-of-fncall-args))
              (and stable-under-simplificationp
                   '(:in-theory (enable FLAG-EV-WHEN-PSEUDO-TERM-FNCALL
                                        flag-ev-of-fncall-args))))
      :fn term-simplify-flag-conds)
    (defret term-simplify-flag-conds-correct-equal
      (implies (and (not iff-p)
                    (flag-possible-value-p flag-facts
                                           (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a))))
               (equal (flag-ev new-x a)
                      (flag-ev x a)))
      :hints ('(:expand (<call>)))
      :fn term-simplify-flag-conds)
    (defret termlist-simplify-flag-conds-correct
      (implies (flag-possible-value-p flag-facts
                                      (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a)))
               (equal (flag-ev-list new-x a)
                      (flag-ev-list x a)))
      :hints ('(:expand (<call>)))
      :fn termlist-simplify-flag-conds)))


      
(define clause-simplify-flag-conds ((x pseudo-term-listp)
                                    (flag-var pseudo-var-p)
                                    (flag-facts flag-facts-p))
  :returns (new-x pseudo-term-listp)
  (b* (((when (atom x)) nil)
       (lit1 (term-simplify-flag-conds (car x) t flag-var flag-facts))
       ((when (pseudo-term-case lit1 :quote))
        (if (pseudo-term-quote->val lit1)
            '('t)
          (clause-simplify-flag-conds (cdr x) flag-var flag-facts)))
       (rest (clause-simplify-flag-conds (cdr x) flag-var flag-facts))
       ((when (equal rest '('t))) rest))
    (cons-with-hint lit1 rest x))
  ///
  (defret clause-simplify-flag-conds-correct
    (implies (and (not (flag-ev (disjoin x) a))
                  (flag-possible-value-p flag-facts
                                         (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a))))
             (not (flag-ev (disjoin new-x) a)))
    :hints (("goal" :induct <call> :expand (<call>))
            (and stable-under-simplificationp
                 '(:use ((:instance term-simplify-flag-conds-correct-iff
                          (x (car x)) (iff-p t)))
                   :in-theory (disable term-simplify-flag-conds-correct-iff))))))

(define filter-possible-flag-values ((x true-listp)
                                     (flag-facts flag-facts-p))
  :returns (new-x true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (if (flag-possible-value-p flag-facts (car x))
        (cons (car x) (filter-possible-flag-values (cdr x) flag-facts))
      (filter-possible-flag-values (cdr x) flag-facts))))

(define resolve-flags-cp ((clause pseudo-term-listp)
                          (var-and-possible-vals))
  :returns (new-clauses)
  (b* (((unless (and (consp var-and-possible-vals)
                     (pseudo-var-p (car var-and-possible-vals))
                     (true-listp (cdr var-and-possible-vals))))
        (cw "Resolve-flags-cp: malformed hint object -- should be (cons flag-var possible-flag-vals)~%")
        (list (pseudo-term-list-fix clause)))
       ((cons flag-var possible-flag-vals) var-and-possible-vals)
       ((mv reduced-clause flag-facts)
        (clause-get-flag-facts clause flag-var))
       (fully-reduced-clause (clause-simplify-flag-conds reduced-clause flag-var flag-facts))
       ((when (equal fully-reduced-clause '('t))) nil)
       (possible-vals (filter-possible-flag-values possible-flag-vals flag-facts)))
    (list (cons (pseudo-term-fncall
                 'not
                 (list (pseudo-term-fncall
                        'acl2::flag-is
                        (list (pseudo-term-quote
                               (cond ((atom possible-vals) :unknown!!)
                                     ((atom (cdr possible-vals)) (car possible-vals))
                                     (t possible-vals)))))))
                fully-reduced-clause)))
  ///
  ;; (local (defret clause-simplify-flag-conds-correct-converse
  ;;          (implies (and (flag-ev (disjoin new-x) a)
  ;;                        (flag-possible-value-p flag-facts
  ;;                                                (cdr (hons-assoc-equal (pseudo-var-fix flag-var) a))))
  ;;                   (flag-ev (disjoin x) a))
  ;;          :fn clause-simplify-flag-conds))

  ;; (local (defret clause-get-flag-facts-new-clause-correct-converse
  ;;          (implies (flag-ev (disjoin new-clause) a)
  ;;                   (flag-ev (disjoin x) a))
  ;;          :fn clause-get-flag-facts))

  (defthm resolve-flags-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (flag-ev (conjoin-clauses (resolve-flags-cp clause var-and-possible-vals)) a))
             (flag-ev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance clause-simplify-flag-conds-correct
                    (x (mv-nth 0 (clause-get-flag-facts clause (car var-and-possible-vals))))
                    (flag-var (car var-and-possible-vals))
                    (flag-facts (mv-nth 1 (clause-get-flag-facts clause (car var-and-possible-vals))))))
             :in-theory (disable clause-simplify-flag-conds-correct)))
    :rule-classes :clause-processor))
                
