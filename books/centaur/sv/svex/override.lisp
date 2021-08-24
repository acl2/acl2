; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (std::add-default-post-define-hook :fix))


(defprod svex-override-triple
  ((testvar svar-p)
   (valvar svar-p)
   (valexpr svex-p))
  :layout :list)




(deflist svex-override-triplelist :elt-type svex-override-triple :true-listp t)


(define svex-override-triplelist-lookup ((test svar-p) (table svex-override-triplelist-p))
  :returns (val (iff (svex-override-triple-p val) val))
  :verify-guards nil
  (mbe :logic (b* (((when (atom table)) nil)
                   ((svex-override-triple x1) (svex-override-triple-fix (car table)))
                   ((when (equal (svar-fix test) x1.testvar)) x1))
                (svex-override-triplelist-lookup test (cdr table)))
       :exec (assoc-equal test table))
  ///
  (local (defthmd svex-override-triplelist-lookup-is-assoc-equal
           (implies (and (svar-p test) (svex-override-triplelist-p table))
                    (equal (svex-override-triplelist-lookup test table)
                           (assoc-equal test table)))
           :hints (("goal" :in-theory (enable svex-override-triple->testvar
                                              svex-override-triplelist-p
                                              svex-override-triple-p)))))
  (local (defthm alistp-when-svex-override-triplelist-p
           (implies (svex-override-triplelist-p x)
                    (alistp x))
           :hints (("goal" :in-theory (enable svex-override-triplelist-p
                                              svex-override-triple-p)))))

  (defret test-var-of-<fn>
    (implies val
             (equal (svex-override-triple->testvar val) (svar-fix test))))

  (verify-guards svex-override-triplelist-lookup
    :hints (("goal" :use svex-override-triplelist-lookup-is-assoc-equal))))


(define svex-override-triplelist-lookup-valvar ((valvar svar-p) (table svex-override-triplelist-p))
  :returns (val (iff (svex-override-triple-p val) val))
  (b* (((when (atom table)) nil)
       ((svex-override-triple x1) (svex-override-triple-fix (car table)))
       ((when (equal (svar-fix valvar) x1.valvar)) x1))
    (svex-override-triplelist-lookup-valvar valvar (cdr table)))
  ///

  (defret valvar-of-<fn>
    (implies val
             (equal (svex-override-triple->valvar val) (svar-fix valvar))))





  (defthm triplelist-lookup-valvar-of-lookup-test
    (implies (svex-override-triplelist-lookup test triples)
             (svex-override-triplelist-lookup-valvar
              (svex-override-triple->valvar (svex-override-triplelist-lookup test triples))
              triples))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup
                                      svex-override-triplelist-lookup-valvar))))

  (defthm triplelist-lookup-test-of-lookup-valvar
    (implies (svex-override-triplelist-lookup-valvar valvar triples)
             (svex-override-triplelist-lookup
              (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples))
              triples))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup
                                      svex-override-triplelist-lookup-valvar))))


  (defthm triplelist-lookup-valvar-of-lookup-test-free
    (implies (and (equal valvar (svex-override-triple->valvar (svex-override-triplelist-lookup test triples)))
                  (svex-override-triplelist-lookup test triples))
             (svex-override-triplelist-lookup-valvar valvar triples)))

  (defthm triplelist-lookup-test-of-lookup-valvar-free
    (implies (and (equal testvar (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples)))
                  (svex-override-triplelist-lookup-valvar valvar triples))
             (svex-override-triplelist-lookup
              testvar
              triples)))

  (defthm triplelist-lookup-equal-triplelist-lookup-valvar
    (implies (svex-override-triplelist-lookup test triples)
             (equal (equal (svex-override-triplelist-lookup test triples)
                           (svex-override-triplelist-lookup-valvar valvar triples))
                    (and (equal (svar-fix test) (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar triples)))
                         (equal (svar-fix valvar) (svex-override-triple->valvar (svex-override-triplelist-lookup test triples)))
                         (equal (svex-override-triple->valexpr (svex-override-triplelist-lookup test triples))
                                (svex-override-triple->valexpr (svex-override-triplelist-lookup-valvar valvar triples))))))
    :hints(("Goal" :in-theory (e/d (svex-override-triplelist-lookup-valvar
                                    svex-override-triplelist-lookup
                                    svex-override-triple-fix-redef)
                                   (svex-override-triple-of-fields))))))


(define svex-override-triplelist-vars ((x svex-override-triplelist-p))
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((svex-override-triple trip) (car x)))
    (cons trip.testvar (cons trip.valvar (svex-override-triplelist-vars (cdr x)))))
  ///
  (local (in-theory (enable svex-override-triplelist-lookup
                            svex-override-triplelist-lookup-valvar)))
  (defret valvar-not-test-var-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup test x))
             (not (equal (svex-override-triple->valvar
                          (svex-override-triplelist-lookup test x))
                         (svar-fix test)))))

  (defret test-var-not-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (not (equal (svex-override-triple->testvar
                          (svex-override-triplelist-lookup-valvar valvar x))
                         (svar-fix valvar)))))

  (defret not-lookup-when-not-member-<fn>
    (implies (not (member-equal (svar-fix var) vars))
             (and (not (svex-override-triplelist-lookup var x))
                  (not (svex-override-triplelist-lookup-valvar var x)))))

  (defret valvar-not-lookup-testvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (not (svex-override-triplelist-lookup valvar x))))

  (defret testvar-not-lookup-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x))
             (not (svex-override-triplelist-lookup-valvar testvar x))))

  (defret valvar-lookup-of-testvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x))
             (equal (svex-override-triplelist-lookup-valvar
                     (svex-override-triple->valvar (svex-override-triplelist-lookup testvar x))
                     x)
                    (svex-override-triplelist-lookup testvar x))))

  (defret testvar-lookup-of-valvar-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup-valvar valvar x))
             (equal (svex-override-triplelist-lookup
                     (svex-override-triple->testvar (svex-override-triplelist-lookup-valvar valvar x))
                     x)
                    (svex-override-triplelist-lookup-valvar valvar x))))


  (defret valvar-not-equal-test-lookup-name-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar x)
                  (svar-p testvar))
             (not (equal (svex-override-triple->valvar
                          (svex-override-triplelist-lookup testvar x))
                         testvar))))

  (defret not-valvar-of-lookup-when-not-member-<fn>
    (implies (and (not (member-equal var vars))
                  (svar-p var)
                  (svex-override-triplelist-lookup test x))
             (not (equal (svex-override-triple->valvar (svex-override-triplelist-lookup test x))
                         var))))

  (defret equal-valvar-of-lookup-when-no-duplicate-<fn>
    (implies (and (no-duplicatesp-equal vars)
                  (svex-override-triplelist-lookup testvar1 x)
                  (svex-override-triplelist-lookup testvar2 x))
             (equal (equal (svex-override-triple->valvar
                            (svex-override-triplelist-lookup testvar1 x))
                           (svex-override-triple->valvar
                            (svex-override-triplelist-lookup testvar2 x)))
                    (equal (svar-fix testvar1) (svar-fix testvar2)))))

)








(define 4vec-no-1s-p ((x 4vec-p))
  (b* (((4vec x)))
    (int= (logand x.upper x.lower) 0))
  ///
  (defthm bit?!-when-4vec-no-1s-p
    (implies (4vec-no-1s-p test)
             (equal (4vec-bit?! test override-val real-val)
                    (4vec-fix real-val)))
    :hints(("Goal" :in-theory (enable 4vec-bit?!)))))




     
      

(local
 (defthm bit?!-when-branches-same
   (equal (4vec-bit?! test real-val real-val)
          (4vec-fix real-val))
   :hints(("Goal" :in-theory (enable 4vec-bit?!))
          (bitops::logbitp-reasoning))))
 
(local (defthm equal-of-4vec-bit?!-by-example
         (implies (equal (4vec-bit?! test then1 else1) (4vec-bit?! test then2 else1))
                  (equal (equal (4vec-bit?! test then1 else2) (4vec-bit?! test then2 else2))
                         t))
         :hints(("Goal" :in-theory (enable 4vec-bit?!))
                (bitops::logbitp-reasoning))))

(local (defthm equal-of-4vec-bit?!-implies-equal-else
         (implies (and (equal (4vec-bit?! test then1 else1) (4vec-bit?! test then2 else1))
                       (4vec-p then2))
                  (equal (equal (4vec-bit?! test then1 then2) then2)
                         t))
         :hints (("goal" :use ((:instance equal-of-4vec-bit?!-by-example
                                (else2 then2)))
                  :in-theory (disable equal-of-4vec-bit?!-by-example)))))
       

(local (defthm svex-env-lookup-of-cons
         (equal (svex-env-lookup key (cons pair rest))
                (if (and (consp pair)
                         (svar-p (car pair))
                         (equal (svar-fix key) (car pair)))
                    (4vec-fix (cdr pair))
                  (svex-env-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-env-lookup)))))


(local (defthmd cons-under-iff
         (iff (cons a b) t)))


                               
                              
(define svex-override-triple-check ((test svex-p)
                                    (then svex-p)
                                    (else svex-p)
                                    (triples svex-override-triplelist-p))
  ;; returns NIL if it doesn't look like an override triple,
  ;; T if it looks like a correct override triple,
  ;; some other object representing the bad value if it looks like an incorrect override triple.
  :returns (result)
  (b* (((unless (svex-case test :var))
        nil)
       ((svex-var test))
       (triple (svex-override-triplelist-lookup test.name triples))
       ((unless triple)
        nil)
       ;; impossible when no duplicate vars
       ;; ((when (svex-override-triplelist-lookup-valvar test.name triples))
       ;;  (cons :test-var-is-also-valvar test.name))
       ((svex-override-triple triple))
       ((unless (svex-case then :var))
        (cons :test-var-with-then-nonvar (svexlist-fix (list test then else))))
       ((svex-var then))
       ((unless (equal then.name triple.valvar))
        (cons :test-var-with-then-othervar (svexlist-fix (list test then else))))
       ;; impossible when no duplicate vars
       ;; ((when (equal triple.valvar triple.testvar))
       ;;  (list :bad-triple-valvar-same-as-testvar))
       ((unless (equal (svex-fix else) triple.valexpr))
        (cons :test-var-with-else-other (svexlist-fix (list test then else))))
       ;; impossible when no duplicate vars
       ;; ((when (svex-override-triplelist-lookup triple.valvar triples))
       ;;  (cons :valvar-is-also-test-var triple.valvar))
       ;; always true when no duplicate vars
       ;; ((unless (equal triple (svex-override-triplelist-lookup-valvar triple.valvar triples)))
       ;;  (cons :valvar-is-other-valvar triple.valvar))
       )
    t)

  ///
  
  (defthm svex-override-triple-check-cdr-when-nil
    (implies (and (equal (svex-override-triple-check test then else x) nil)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x)))
             (equal (svex-override-triple-check test then else (cdr x)) nil))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svex-override-triplelist-lookup))))

  (defthm svex-override-triple-check-cdr-when-t
    (implies (and (equal (svex-override-triple-check test then else x) t)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (not (equal (svex-override-triple-check test then else (cdr x)) nil)))
             (equal (svex-override-triple-check test then else (cdr x)) t))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      svex-override-triplelist-lookup)))))


;; This checks whether a svex/svexlist satisfies syntactic criteria for
;; recomposition after a decomposition proof using the given overrides.
;; The correctness theorem looks like this:
;; (defret remove-override-when-<fn>
;;       (implies (and (not bad)
;;                     (svar-p test)
;;                     (svar-p valvar)
;;                     (b* ((look (svex-override-triplelist-lookup test triples)))
;;                       (and look
;;                            (b* (((svex-override-triple look)))
;;                              (and (equal valvar look.valvar)
;;                                   (equal (4vec-bit?! testval val 0)
;;                                          (4vec-bit?! testval (svex-eval look.valexpr env) 0))
;;                                   (equal (svex-override-triplelist-lookup-valvar valvar triples)
;;                                          look)
;;                                   (not (svex-override-triplelist-lookup-valvar test triples))
;;                                   (not (svex-override-triplelist-lookup valvar triples))
;;                                   (4vec-no-1s-p (svex-env-lookup test env)))))))
;;                (equal (svex-eval x (cons (cons test testval)
;;                                          (cons (cons valvar val)
;;                                                env)))
;;                       (svex-eval x env)))
;;       :hints ('(:expand <call>)
;;               (and stable-under-simplificationp
;;                    '(:expand ((:free (env) (svex-eval x env))))))
;;       :fn svex-check-overridetriples)
;; That is, you can remove an override test and override value binding from the environment
;; if the following conditions apply...
;;   0. This function's check of the expression is OK
;;   1. The test and value variables are a corresponding pair of variables from the given triples
;;      and there's no confusion where e.g. they are the same, the test variable is another triple's
;;      value variable or vice versa, etc
;;   2. The test variable's binding in the rest of the env is "false" (in this case, not 1)
;;      on all bits
;;   3. The override value's current binding in the env matches
;;      (on the bits where test's binding is 1) the evaluation of the triple's value 
;;      expression on the rest of the env.

;; This test is probably efficient enough, and could be changed to use fast
;; alist lookups into the triplelist.  But a couple of things might make it
;; hard to apply.
;;   1 -- Syntactically, the theorem just says we can take two pairs out of the env.
;;        Of course, the envs here occur under a svex-envs-similar context so this is
;;        relatively easy to expand.
;;   2 -- In practice we're going to have an evaluation involving an environment where 
;;        several overrides are added to a previous environment, and each of the override
;;        values is an evaluation of the corresponding variable's expression 
;;        using the previous environment.  This doesn't quite
;;        correspond to an iterative application of this theorem -- we need to whow that
;;        these expressions are independent of the other overrides, or at least can be
;;        topologically ordered.
(defines svex-check-overridetriples
  (define svex-check-overridetriples ((x svex-p)
                                      (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svex-count x) 1)
    :returns (bad)
    (svex-case x
      :quote nil
      :var (and (or (svex-override-triplelist-lookup x.name triples)
                    (svex-override-triplelist-lookup-valvar x.name triples))
                (list :bad-var (svex-fix x)))
      :call (svex-check-overridetriples-call x triples)))
  (define svex-check-overridetriples-call ((x svex-p)
                                     (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svex-count x) 0)
    :hints ((and stable-under-simplificationp
                 '(:expand ((svex-count x)))))
    :guard (svex-case x :call)
    :returns (bad)
    (b* (((unless (mbt (svex-case x :call))) (list :programming-err (svex-fix x)))
         ((svex-call x)))
      (case x.fn
        (bit?! (b* (((unless (Eql (len x.args) 3))
                     (svexlist-check-overridetriples x.args triples))
                    ((list test then else) x.args)
                    (check (svex-override-triple-check test then else triples))
                    ((unless check)
                     ;; not an override triple -- just recur on args
                     (svexlist-check-overridetriples x.args triples))
                    ((when (eq check t))
                     ;; good override triple -- just recur on else
                     (svex-check-overridetriples else triples)))
                 check))

        (otherwise (svexlist-check-overridetriples x.args triples)))))

  (define svexlist-check-overridetriples ((x svexlist-p)
                                    (triples svex-override-triplelist-p))
    :measure (two-nats-measure (svexlist-count x) 0)
    :returns (bad)
    (if (atom x)
        nil
      (or (svex-check-overridetriples (car x) triples)
          (svexlist-check-overridetriples (cdr x) triples))))
  ///

  (local (defthm member-of-cons
           (iff (member k (cons a b))
                (or (equal k a)
                    (member k b)))))

  (local (defthm member-when-atom
           (implies (atom x)
                    (not (member k x)))))

  (local (in-theory (disable svex-check-overridetriples
                             svex-check-overridetriples-call
                             svexlist-check-overridetriples
                             member-equal)))

  (local (defthm svex-eval-when-var
           (implies (svex-case x :var)
                    (equal (svex-eval x env)
                           (svex-env-lookup (svex-var->name x) env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (std::defret-mutual remove-override-when-check-overridetriples
    (defret remove-override-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* ((look (svex-override-triplelist-lookup test triples)))
                      (and look
                           (b* (((svex-override-triple look)))
                             (and (equal valvar look.valvar)
                                  (equal (4vec-bit?! testval val 0)
                                         (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                                  ;; (equal (svex-override-triplelist-lookup-valvar valvar triples)
                                  ;;        look)
                                  ;; (not (svex-override-triplelist-lookup-valvar test triples))
                                  ;; (not (svex-override-triplelist-lookup valvar triples))
                                  (4vec-no-1s-p (svex-env-lookup test env)))))))
               (equal (svex-eval x (cons (cons test testval)
                                         (cons (cons valvar val)
                                               env)))
                      (svex-eval x env)))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
      :fn svex-check-overridetriples)
    (defret remove-override-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* ((look (svex-override-triplelist-lookup test triples)))
                      (and look
                           (b* (((svex-override-triple look)))
                             (and (equal valvar look.valvar)
                                  (equal (4vec-bit?! testval val 0)
                                         (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                                  ;; (equal (svex-override-triplelist-lookup-valvar valvar triples)
                                  ;;        look)
                                  ;; (not (svex-override-triplelist-lookup-valvar test triples))
                                  ;; (not (svex-override-triplelist-lookup valvar triples))
                                  (4vec-no-1s-p (svex-env-lookup test env)))))))
               (equal (svex-eval x (cons (cons test testval)
                                         (cons (cons valvar val)
                                               env)))
                      (svex-eval x env)))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply 4veclist-nth-safe
                                   svex-override-triple-check))
              (and stable-under-simplificationp
                   '(:in-theory (enable cons-under-iff))))
      :fn svex-check-overridetriples-call)
    (defret remove-override-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* ((look (svex-override-triplelist-lookup test triples)))
                      (and look
                           (b* (((svex-override-triple look)))
                             (and (equal valvar look.valvar)
                                  (equal (4vec-bit?! testval val 0)
                                         (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                                  ;; (equal (svex-override-triplelist-lookup-valvar valvar triples)
                                  ;;        look)
                                  ;; (not (svex-override-triplelist-lookup-valvar test triples))
                                  ;; (not (svex-override-triplelist-lookup valvar triples))
                                  (4vec-no-1s-p (svex-env-lookup test env)))))))
               (equal (svexlist-eval x (cons (cons test testval)
                                         (cons (cons valvar val)
                                               env)))
                      (svexlist-eval x env)))
      :hints ('(:expand <call>))
      :fn svexlist-check-overridetriples))

  (local (defthm svexlist-check-overridetriples-when-svex-override-triple-check-is-t
           (implies (and (equal (svex-override-triple-check (car args)
                                                            (cadr args)
                                                            (caddr args)
                                                            triples)
                                t)
                         (not (svex-override-triple-check (car args)
                                                          (cadr args)
                                                          (caddr args)
                                                          (cdr triples)))
                         (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                         (equal (len args) 3)
                         (not (svex-check-overridetriples (caddr args) (cdr triples))))
                    (not (svexlist-check-overridetriples args (cdr triples))))
           :hints(("Goal" :in-theory (enable svex-override-triple-check)
                   :expand ((:free (x) (svex-check-overridetriples x (cdr triples)))
                            (svexlist-check-overridetriples args (cdr triples))
                            (svexlist-check-overridetriples (cdr args) (cdr triples))
                            (svexlist-check-overridetriples (cddr args) (cdr triples))
                            (svexlist-check-overridetriples (cdddr args) (cdr triples))
                            (:free (x) (svex-override-triplelist-lookup x triples))
                            (svex-override-triplelist-vars triples))))))

  (std::defret-mutual cdr-triples-preserves-<fn>
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (var) (svex-override-triplelist-lookup var triples))
                         (:free (var) (svex-override-triplelist-lookup-valvar var triples)))))
      :fn svex-check-overridetriples)
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:Free (triples) <call>))))
      :fn svex-check-overridetriples-call)
    (defret cdr-triples-preserves-<fn>
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
               (not (let ((triples (cdr triples))) <call>)))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svexlist-check-overridetriples)))






(include-book "vars")



(defines svex-vars-intersect
  :verify-guards nil
  :flag-local nil
  :prepwork ((local (Defthm intersect-nil
                      (equal (intersect nil x) nil)
                      :hints(("Goal" :in-theory (enable intersect)))))

             (local (Defthm intersect-single
                      (equal (intersect (list k) x)
                             (and (set::in k x) (list k)))
                      :hints(("Goal" :in-theory (enable intersect empty head tail setp insert)
                              :expand ((intersect (list k) x))))))

             (local (defthm hons-assoc-equal-under-iff
                      (iff (hons-assoc-equal k x)
                           (member-equal k (Alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys)))))

             (local (defthm union-of-equal-intersect
                      (implies (and (equal a (intersect b c))
                                    (equal d (intersect e c)))
                               (equal (union a d)
                                      (intersect (union b e) c)))
                      :hints(("Goal" :in-theory (enable set::double-containment
                                                        set::pick-a-point-subset-strategy))))))
  (define svex-vars-intersect
    ((x svex-p "Expression to collect variables from.")
     (tab))
    :returns
    (vars (equal vars (set::intersect (svex-vars x)
                                      (set::mergesort (alist-keys tab))))
          :hints ('(:expand ((svex-vars x)))))
    :measure (svex-count x)
    (svex-case x
      :quote nil
      :var (and (hons-get x.name tab) (list x.name))
      :call (svexlist-vars-intersect x.args tab)))

  (define svexlist-vars-intersect
    ((x svexlist-p "Expression list to collect variables from.")
     (tab))
    :returns
    (vars (equal vars (set::intersect (svexlist-vars x)
                                      (set::mergesort (alist-keys tab))))
          :hints ('(:expand ((svexlist-vars x)))))

    :measure (svexlist-count x)
    (if (atom x)
        nil
      (union (svex-vars-intersect (car x) tab)
             (svexlist-vars-intersect (cdr x) tab))))
  ///
  (verify-guards svex-vars-intersect)
  (memoize 'svex-vars-intersect)
  ///
  (deffixequiv-mutual svex-vars-intersect
    :hints (("Goal" :expand ((svexlist-fix x))))))




