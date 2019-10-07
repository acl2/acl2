; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

    
;; (defun translate-defs-bodies (defs-lst wrld)
;;   (Declare (Xargs :mode :program))
;;   (if (atom defs-lst)
;;       nil
;;     (b* (((mv ctx msg/ans) (translate-cmp (car (last (car defs-lst)))
;;                                           t nil t 'translate-bodies wrld
;;                                           (default-state-vars nil)))
;;          ((when ctx) (translate-defs-bodies (cdr defs-lst) wrld)))
;;       (cons msg/ans (translate-defs-bodies (cdr defs-lst) wrld)))))


;; (defun remove-logic-fns (fns wrld)
;;   (if (atom fns)
;;       nil
;;     (if (logicp (car fns) wrld)
;;         (remove-logic-fns (cdr fns) wrld)
;;       (cons (car fns) (remove-logic-fns (cdr fns) wrld)))))

(include-book "std/osets/sort" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
;; (include-book "interp")

(program)

(defun function-deps (fn wrld)
  (b* ((body (getpropc fn 'unnormalized-body nil wrld)))
    (acl2::all-fnnames body)))

(defun function-deps-lst (fns wrld acc)
  (if (atom fns)
      acc
    (b* ((body (getpropc (car fns) 'unnormalized-body nil wrld)))
      (function-deps-lst (cdr fns) wrld (acl2::all-fnnames1 nil body acc)))))
       


(mutual-recursion
 (defun collect-dependent-fns (fn wrld targets seen dependents)
   (Declare (xargs :mode :program))
   (b* (((when (or (member-eq fn dependents)
                   (member-eq fn targets)))
         (mv t seen dependents))
        ((when (member-eq fn seen)) (mv nil seen dependents))
        (clique (or (getpropc fn 'acl2::recursivep nil wrld) (list fn)))
        (deps (function-deps-lst clique wrld nil))
        (seen (append clique seen))
        ((mv is-dependent seen dependents)
         (collect-dependent-fns-list deps wrld targets nil seen dependents))
        (dependents (if is-dependent (append clique dependents) dependents)))
     (mv is-dependent seen dependents)))
 (defun collect-dependent-fns-list (fns wrld targets dependentp seen dependents)
   (if (atom fns)
       (mv dependentp seen dependents)
     (b* (((mv is-dep seen dependents) (collect-dependent-fns (car fns) wrld targets seen dependents)))
       (collect-dependent-fns-list (cdr fns) wrld targets (or is-dep dependentp) seen dependents)))))



(defun collect-absolute-event-numbers (names wrld)
  (if (atom names)
      nil
    (cons (getpropc (car names) 'acl2::absolute-event-number nil wrld)
          (collect-absolute-event-numbers (cdr names) wrld))))


(defun prefix-syms (prefix names)
  (if (atom names)
      nil
    (cons (intern-in-package-of-symbol
           (concatenate 'string (symbol-name prefix) (symbol-name (car names)))
           (car names))
          (prefix-syms prefix (cdr names)))))

(defun remove-xargs-from-xargs (x xarg-types)
  (if (atom x)
      x
    (if (member-eq (car x) xarg-types)
        (remove-xargs-from-xargs (cddr x) xarg-types)
      (cons-with-hint (car x)
                      (cons-with-hint (cadr x)
                                      (remove-xargs-from-xargs (cddr x) xarg-types)
                                      (cdr x))
                      x))))

(defun remove-xargs-from-declares (x xarg-types)
  (if (atom x)
      x
    (cons-with-hint
     (if (and (consp (car x))
              (eq (caar x) 'xargs))
         (cons-with-hint 'xargs
                         (remove-xargs-from-xargs (cdar x) xarg-types)
                         (car x))
       (car x))
     (remove-xargs-from-declares (cdr x) xarg-types)
     x)))
  

(defun remove-xargs-from-decls/body (x xarg-types)
  (if (or (atom x)
          (atom (car x))
          (not (eq (caar x) 'declare)))
      x
    (cons-with-hint (cons-with-hint 'declare
                                    (remove-xargs-from-declares (cdar x) xarg-types)
                                    (car x))
                    (remove-xargs-from-decls/body (cdr x) xarg-types)
                    x)))
    


(defun remove-xargs-from-defun-cdr (x xarg-types)
  (cons-with-hint (car x) ;; fnname
                  (cons-with-hint (cadr x)
                                  (remove-xargs-from-decls/body (cddr x) xarg-types)
                                  (cdr x))
                  x))

(defun remove-xargs-from-defun (x xarg-types)
  (cons-with-hint 'defun
                  (remove-xargs-from-defun-cdr (cdr x) xarg-types)
                  x))

(defun remove-xargs-from-mutrec-defuns (x xarg-types)
  (if (atom x)
      x
    (cons-with-hint
     (remove-xargs-from-defun (car x) xarg-types)
     (remove-xargs-from-mutrec-defuns (cdr x) xarg-types)
     x)))

(defun remove-xargs-from-mutual-recursion (x xarg-types)
  (cons-with-hint 'mutual-recursion
                  (remove-xargs-from-mutrec-defuns (cdr x) xarg-types)
                  x))

(defun add-xargs-to-defun (x xargs)
  (append (take 3 x) ;; (defun foo (formals)
          (cons `(declare (xargs  . ,xargs))
                (nthcdr 3 x))))

(defun add-xargs-to-mutual-recursion (x xargs)
  (cons 'mutual-recursion
        (cons (add-xargs-to-defun (cadr x) xargs)
              (cddr x))))

(defun instance-subst-from-full-subst (names full-subst)
  (if (atom names)
      nil
    (cons (list (car names) (cdr (assoc (car names) full-subst)))
          (instance-subst-from-full-subst (cdr names) full-subst))))

(defun fns->expands (fns wrld)
  (if (atom fns)
      nil
    (cons `(:with ,(car fns)
            (,(car fns) . ,(acl2::formals (car fns) wrld)))
          (fns->expands (cdr fns) wrld))))

(defun modify-event-and-update-functional-subst (x full-subst instance-subst wrld)
  (if (eq (car x) 'mutual-recursion)
      (b* ((fns (acl2::strip-cadrs (cdr x)))
           (substituted (sublis full-subst x))
           ;; (subst-fns (sublis full-subst fns))
           (new-instance-subst (append (instance-subst-from-full-subst fns full-subst) instance-subst))
           ;; (expands (sublis full-subst (fns->expands fns wrld)))
           (xargs
            `(:hints (("Goal" :by (:functional-instance (:termination-theorem ,(car fns))
                                   . ,new-instance-subst)
                       :do-not '(preprocess simplify)
                       :in-theory nil
                       :do-not-induct t
                       )
                      '(:clause-processor dumb-clausify-cp)
                      (let ((term (car (last clause))))
                        (case-match term
                          (('equal (fn . args) . &)
                           (if (and (symbol-listp args)
                                    (member fn ',(acl2::strip-cadrs new-instance-subst)))
                               `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                                 ;; :do-not nil :in-theory (enable)
                                 )
                             '(;; :do-not nil :in-theory (enable)
                               )))
                          (& '(;; :do-not nil :in-theory (enable)
                               ))))
                      ;; :do-not '(preprocess simplify)
                      )
              :verify-guards t
              :guard-simplify nil
              :guard-hints (("Goal" :by (:functional-instance (:guard-theorem ,(car fns) t)
                                         . ,new-instance-subst)
                             ;; :in-theory '((:definition eq)
                             ;;              (:definition eql)
                             ;;              (:definition =))
                             ;; :do-not '(preprocess simplify)
                             :do-not '(preprocess simplify)
                             :in-theory nil
                             :do-not-induct t
                             )
                            '(:clause-processor dumb-clausify-cp)
                            (let ((term (car (last clause))))
                              (case-match term
                                (('equal (fn . args) . &)
                                 (if (and (symbol-listp args)
                                          (member fn ',(acl2::strip-cadrs new-instance-subst)))
                                     `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                                       ;; :do-not nil :in-theory (enable)
                                       )
                                   '(;; :do-not nil :in-theory (enable)
                                     )))
                                (& '(;; :do-not nil :in-theory (enable)
                                     ))))
                            ;; '(:expand ,expands
                            ;;   :do-not-induct t)
                            ;; '(:in-theory (enable))
                            )))
           (full (add-xargs-to-mutual-recursion
                  (remove-xargs-from-mutual-recursion substituted '(:hints :verify-guards :guard-hints :measure-debug :guard-debug))
                  xargs)))
        (mv full new-instance-subst))
    (b* ((fns (list (cadr x)))
         (substituted (sublis full-subst x))
         ;; (subst-fns (sublis full-subst fns))
         (new-instance-subst (append (instance-subst-from-full-subst fns full-subst) instance-subst))
         ;; (expands (sublis full-subst (fns->expands fns wrld)))
         (guard-xargs `(:verify-guards t
                        :guard-simplify nil
                        :guard-hints (("Goal" :by (:functional-instance (:guard-theorem ,(car fns) t)
                                                   . ,new-instance-subst)
                                       ;; :in-theory '((:definition eq)
                                       ;;              (:definition eql)
                                       ;;              (:definition =))
                                       ;; :do-not '(preprocess simplify)
                                       :do-not '(preprocess simplify)
                                       :in-theory nil
                                       :do-not-induct t
                                       )
                                      '(:clause-processor dumb-clausify-cp)
                                      (let ((term (car (last clause))))
                                        (case-match term
                                          (('equal (fn . args) . &)
                                           (if (and (symbol-listp args)
                                                    (member fn ',(acl2::strip-cadrs new-instance-subst)))
                                               `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                                                 :do-not nil)
                                             '(:do-not nil)))
                                          (& '(:do-not nil)))))))
         (xargs (if (recursivep (car fns) nil wrld)
                    `(:hints (("Goal" :by (:functional-instance (:termination-theorem ,(car fns))
                                           . ,new-instance-subst)
                               :do-not '(preprocess simplify)
                               :in-theory nil
                               :do-not-induct t
                               )
                              '(:clause-processor dumb-clausify-cp)
                              (let ((term (car (last clause))))
                                (case-match term
                                  (('equal (fn . args) . &)
                                   (if (and (symbol-listp args)
                                            (member fn ',(acl2::strip-cadrs new-instance-subst)))
                                       `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                                         :do-not nil)
                                     '(:do-not nil)))
                                  (& '(:do-not nil)))))
                      . ,guard-xargs)
                  guard-xargs))
         (full (add-xargs-to-defun
                (remove-xargs-from-defun substituted '(:hints :verify-guards :guard-hints :measure-debug :guard-debug))
                xargs)))
      (mv full new-instance-subst))))

(defun modify-events-and-update-functional-substs (x full-subst instance-subst wrld)
  (b* (((when (atom x)) (mv nil instance-subst))
       ((mv first instance-subst) (modify-event-and-update-functional-subst (car x) full-subst instance-subst wrld))
       ((mv rest instance-subst) (modify-events-and-update-functional-substs (cdr x) full-subst instance-subst wrld)))
    (mv (cons first rest) instance-subst)))
    
    


(defun collect-events-for-absolute-event-nums (event-nums wrld)
  (if (atom event-nums)
      nil
    (cons (acl2::access-event-tuple-form
           (cddar (acl2::lookup-world-index 'event (car event-nums) wrld)))
          (collect-events-for-absolute-event-nums (cdr event-nums) wrld))))

(defun substitute-functions (prefix top-fns fn-subst wrld)
  (b* (((mv depp & dependent-fns)
        (collect-dependent-fns-list top-fns wrld
                                    (strip-cars fn-subst)
                                    nil nil nil))
       ((unless depp)
        (mv (er hard? 'substitute-functions "None of the given top-fns depend on the functions bound in the substitution.") nil))
       (event-nums (set::mergesort (collect-absolute-event-numbers dependent-fns wrld)))
       (full-subst (append (pairlis$ dependent-fns (prefix-syms prefix dependent-fns)) fn-subst))
       (defuns (collect-events-for-absolute-event-nums event-nums wrld))
       ((mv events instance-subst)
        (modify-events-and-update-functional-substs defuns full-subst
                                                    (pairlis$ (strip-cars fn-subst)
                                                              (pairlis$ (strip-cdrs fn-subst) nil))
                                                    wrld)))
    (mv (cons 'progn events) instance-subst)))

;; (include-book "primitives")

(logic)

(defevaluator cl-ev cl-ev-lst ((if a b c)) :namedp t)

(defun dumb-clausify (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((atom x) (list (list x)))
        ((equal x ''t) nil)
        ((and (eq (car x) 'if)
              (equal (fourth x) ''nil))
         (append (dumb-clausify (second x))
                 (dumb-clausify (third x))))
        (t (list (list x)))))

(acl2::def-join-thms cl-ev)

(defthm dumb-clausify-correct
  (iff (cl-ev (conjoin-clauses (dumb-clausify x)) a)
       (cl-ev x a)))

(defun dumb-clausify-cp (x)
  (declare (xargs :guard (pseudo-term-listp x)))
  (if (or (atom x)
          (consp (cdr x)))
      (list x)
    (dumb-clausify (car x))))

(defthm dumb-clausify-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (cl-ev (conjoin-clauses (dumb-clausify-cp x)) a))
           (cl-ev (disjoin x) a))
  :rule-classes :clause-processor)



(include-book "centaur/misc/beta-reduce-full" :dir :System)
(include-book "clause-processors/sublis-var-meaning" :dir :system)

(defevaluator subst-ev subst-ev-list
  ((acl2-numberp x)
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
   (symbolp x)
   (if x y z)
   (not x)

   (return-last x y z))
  :namedp t)

(include-book "tools/def-functional-instance" :dir :system)

(acl2::def-functional-instance
  beta-reduce-full-correct-for-subst-ev
  acl2::beta-reduce-full-correct
  ((acl2::beta-eval subst-ev)
   (acl2::beta-eval-list subst-ev-list))
  :hints ('(:in-theory (enable subst-ev-of-fncall-args
                               subst-ev-of-nonsymbol-atom
                               subst-ev-of-bad-fncall))))

#!acl2
(mutual-recursion

 (defun my-quote-normal-form1 (form)
   (declare (xargs :guard (and (pseudo-termp form))
                   :verify-guards nil))
   (cond ((variablep form)
          (mv nil form))
         ((fquotep form)
          (mv nil form))
         (t (mv-let (changedp lst)
              (my-quote-normal-form1-lst (fargs form))
              (let ((fn (ffn-symb form)))
                (cond (changedp (mv t (cons-term fn lst)))
                      ((and (symbolp fn) ; optimization
                            (quote-listp lst))
                       (cons-term1-mv2 fn lst form))
                      (t (mv nil form))))))))

 (defun my-quote-normal-form1-lst (l)
   (declare (xargs :guard (and (pseudo-term-listp l))))
   (cond ((endp l)
          (mv nil l))
         (t (mv-let (changedp1 term)
              (my-quote-normal-form1 (car l))
              (mv-let (changedp2 lst)
                (my-quote-normal-form1-lst (cdr l))
                (cond ((or changedp1 changedp2)
                       (mv t (cons term lst)))
                      (t (mv nil l))))))))
 )

#!acl2
(defthm-term-subst-flg
  (defthm my-quote-normal-form1-is-sublis-var1
    (equal (my-quote-normal-form1 x)
           (sublis-var1 nil x))
    :hints ('(:expand ((my-quote-normal-form1 x)
                       (sublis-var1 nil x))))
    :flag term)
  (defthm my-quote-normal-form1-lst-is-sublis-var1-lst
    (equal (my-quote-normal-form1-lst x)
           (sublis-var1-lst nil x))
    :hints ('(:expand ((my-quote-normal-form1-lst x)
                       (sublis-var1-lst nil x))))
    :flag list))

(acl2::def-functional-instance sublis-var1-is-term-subst-for-subst-ev
  acl2::sublis-var1-is-term-subst
  ((acl2::cterm-ev subst-ev)
   (acl2::cterm-ev-lst subst-ev-list))
  :hints ('(:in-theory (enable subst-ev-of-fncall-args
                               subst-ev-of-nonsymbol-atom
                               subst-ev-of-bad-fncall))))

(defun subst-ev-alist (x a)
  (if (atom x)
      nil
    (cons (cons (caar x) (subst-ev (cdar x) a))
          (subst-ev-alist (cdr x) a))))

(acl2::def-functional-instance eval-of-term-subst-for-subst-ev
  acl2::eval-of-term-subst
  ((acl2::cterm-ev subst-ev)
   (acl2::cterm-ev-lst subst-ev-list)
   (acl2::cterm-ev-alist subst-ev-alist)))

(verify-guards acl2::my-quote-normal-form1
  :hints(("Goal" :expand ((pseudo-termp acl2::form)))))

(memoize 'acl2::my-quote-normal-form1)

(acl2::def-join-thms subst-ev)

(acl2::def-ev-pseudo-term-fty-support subst-ev subst-ev-list)

(defines remove-return-last-calls
  (define remove-return-last-calls ((x pseudo-termp))
    :returns (new-x pseudo-termp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :fncall (if (and** (eq x.fn 'return-last)
                         (eql (len x.args) 3))
                  (remove-return-last-calls (third x.args))
                (pseudo-term-fncall x.fn (remove-return-last-calls-list x.args)))
      :lambda (pseudo-term-lambda
               x.formals
               (remove-return-last-calls x.body)
               (remove-return-last-calls-list x.args))
      :otherwise (pseudo-term-fix x)))
  (define remove-return-last-calls-list ((x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    :returns (new-x pseudo-term-listp)
    (if (atom x)
        nil
      (cons (remove-return-last-calls (car x))
            (remove-return-last-calls-list (cdr x)))))
  ///
  (defret-mutual len-of-remove-return-last-calls-list
    (defret len-of-remove-return-last-calls-list
      (equal (len new-x) (len x))
      :fn remove-return-last-calls-list)
    :skip-others t)
  (verify-guards remove-return-last-calls)
  (local (defun-sk remove-return-last-calls-correct-cond (x new-x)
           (forall a
                   (equal (subst-ev new-x a)
                          (subst-ev x a)))
           :rewrite :direct))

  (local (defun-sk remove-return-last-calls-list-correct-cond (x new-x)
           (forall a
                   (equal (subst-ev-list new-x a)
                          (subst-ev-list x a)))
           :rewrite :direct))
  (local (in-theory (disable remove-return-last-calls-list-correct-cond
                             remove-return-last-calls-correct-cond)))

  (local (defret-mutual remove-return-last-calls-correct
           (defret remove-return-last-calls-correct-lemma
             (remove-return-last-calls-correct-cond x new-x)
             :hints ((and stable-under-simplificationp
                          `(:expand (,(car (last clause))
                                     <call>)
                            :in-theory (enable subst-ev-of-fncall-args))))
             :fn remove-return-last-calls)
           (defret remove-return-last-calls-list-correct-lemma
             (remove-return-last-calls-list-correct-cond x new-x)
             :hints ((and stable-under-simplificationp
                          `(:expand (,(car (last clause))
                                     <call>))))
             :fn remove-return-last-calls-list)))

  (defret remove-return-last-calls-correct
    (equal (subst-ev new-x a)
           (subst-ev x a))
    :hints (("goal" :use remove-return-last-calls-correct-lemma
             :in-theory (disable remove-return-last-calls-correct-lemma)))
    :fn remove-return-last-calls)

  (defret remove-return-last-calls-list-correct
    (equal (subst-ev-list new-x a)
           (subst-ev-list x a))
    :hints (("goal" :use remove-return-last-calls-list-correct-lemma
             :in-theory (disable remove-return-last-calls-list-correct-lemma)))
    :fn remove-return-last-calls-list)

  (defret disjoin-of-remove-return-last-calls-list
    (iff (subst-ev (disjoin new-x) a)
         (subst-ev (disjoin x) a))
    :hints (("goal" :induct (len x)
             :in-theory (enable (:i len))
             :expand (<call>)))
    :fn remove-return-last-calls-list)

  (memoize 'remove-return-last-calls))

;; (define remove-return-last-cp ((x pseudo-term-listp))
;;   :hooks nil
;;   (list (remove-return-last-calls-list x))
;;   ///
;;   (defthm remove-return-last-cp-correct
;;     (implies (and (pseudo-term-listp x)
;;                   (alistp a)
;;                   (subst-ev (conjoin-clauses (remove-return-last-cp x)) a))
;;              (subst-ev (disjoin x) a))
;;     :rule-classes :clause-processor))

(define beta-reduce-by-hint-cp ((clause pseudo-term-listp)
                           (thm)
                           state)
  (b* (((unless (symbolp thm))
        (value (list clause)))
       ((unless (and (consp clause) (not (cdr clause))))
        (value (list clause)))
       (formula (meta-extract-formula thm state))
       ((unless (pseudo-termp formula))
        (value (list clause)))
       (formula-rl (remove-return-last-calls formula))
       (formula-beta (acl2::beta-reduce-full formula-rl))
       ((mv & formula-norm) (acl2::my-quote-normal-form1 formula-beta))
       (term-rl (remove-return-last-calls (car clause)))
       (term-beta (acl2::beta-reduce-full term-rl))
       ((mv & term-norm) (acl2::my-quote-normal-form1 term-beta)))
    (value (if (equal term-norm formula-norm)
               nil
             (prog2$ (cw "beta-reduce-by-hint-cp failed:~%~x0~%~x1~%" term-norm formula-norm)
                     (list clause)))))
  ///
  (local (in-theory (disable pseudo-termp pseudo-term-listp
                             ;; acl2::pseudo-termp-opener
                             acl2::beta-reduce-full acl2::my-quote-normal-form1
                             acl2::sublis-var1)))

  (defthm beta-reduce-by-hint-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (subst-ev (meta-extract-global-fact `(:formula ,thm) state) a)
                  (subst-ev (conjoin-clauses
                                    (acl2::clauses-result
                                     (beta-reduce-by-hint-cp clause thm state)))
                                   a))
             (subst-ev (disjoin clause) a))
    :hints(("Goal" :in-theory (e/d (meta-extract-global-fact+)
                                   (;; beta-reduce-full-correct-for-subst-ev
                                    sublis-var1-is-term-subst-for-subst-ev))
            :expand ((pseudo-term-listp clause))
            :use (;; (:instance beta-reduce-full-correct-for-subst-ev
                  ;;  (x (car clause)))
                  ;; (:instance beta-reduce-full-correct-for-subst-ev
                  ;;  (x (meta-extract-formula thm state)))
                  (:instance sublis-var1-is-term-subst-for-subst-ev
                   (x (acl2::beta-reduce-full (remove-return-last-calls (meta-extract-formula thm state))))
                   (alist nil)
                   (a a))
                  (:instance sublis-var1-is-term-subst-for-subst-ev
                   (x (acl2::beta-reduce-full (remove-return-last-calls (car clause))))
                   (alist nil)
                   (a a))
                  )))
    :rule-classes :clause-processor))


;; (in-theory '((:definition eq)
;;              (:definition eql)
;;              (:definition =)))
    

;; (set-case-split-limitations '(0 1000))

;; (make-event
;;  (b* (((mv event &)
;;        (substitute-functions 'prims1- '(fgl-interp-test) '((fgl-primitive-fncall-stub . fgl-primitive-fncall-base)) (w state))))
;;    event))

