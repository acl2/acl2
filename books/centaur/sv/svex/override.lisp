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
(include-book "alist-equiv")
(include-book "std/util/defprojection" :dir :system)
(local (include-book "std/alists/hons-remove-assoc" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
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
    :hints (("goal" :use svex-override-triplelist-lookup-is-assoc-equal)))

  (defret member-of-<fn>
    (implies val
             (member-equal val (svex-override-triplelist-fix table)))))


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
                                   (svex-override-triple-of-fields)))))

  (defret member-of-<fn>
    (implies val
             (member-equal val (svex-override-triplelist-fix table)))))


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


  

  (local (Defthm member-vars-when-member-has-test-var
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal var (svex-override-triple->testvar trip)))
                    (member-equal var (svex-override-triplelist-vars x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-fix)))))

  (local (defret lookup-by-member
           (implies (and (no-duplicatesp-equal vars)
                         (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->testvar trip)))
                    (equal (svex-override-triplelist-lookup var x) trip))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup)))))

  (local (defthm lookup-exists-by-member
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->testvar trip)))
                    (svex-override-triplelist-lookup var x))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup)))))


  (defretd lookup-test-when-set-equiv-and-no-duplicate-vars
    (implies (and (no-duplicatesp-equal vars)
                  (set-equiv (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y)))
             (equal (svex-override-triplelist-lookup var y)
                    (svex-override-triplelist-lookup var x)))
    :hints (("goal" :use ((:instance member-of-svex-override-triplelist-lookup
                           (table x) (test var))
                          (:instance member-of-svex-override-triplelist-lookup
                           (table y) (test var))
                          (:instance lookup-exists-by-member
                           (x y) (trip (svex-override-triplelist-lookup var x))))
             :cases ((svex-override-triplelist-lookup var y))
             :in-theory (disable member-of-svex-override-triplelist-lookup
                                 lookup-exists-by-member))))

  (defcong set-equiv set-equiv (svex-override-triplelist-fix x) 1
    :hints (("goal" :use ((:instance
                           (:functional-instance acl2::set-equiv-congruence-over-elementlist-projection
                            (acl2::element-p (lambda (x) t))
                            (acl2::outelement-p (lambda (x) t))
                            (acl2::element-xformer svex-override-triple-fix)
                            (acl2::elementlist-projection svex-override-triplelist-fix))
                           (y x-equiv))))))


  (defthm svex-override-triplelist-lookup-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triplelist-lookup var (mergesort x))
                    (svex-override-triplelist-lookup var x)))
    :hints (("goal" :use ((:instance lookup-test-when-set-equiv-and-no-duplicate-vars
                           (y (mergesort x)))))))
  


  (local (Defthm member-vars-when-member-has-val-var
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal var (svex-override-triple->valvar trip)))
                    (member-equal var (svex-override-triplelist-vars x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-fix)))))

  (local (defret lookup-valvar-by-member
           (implies (and (no-duplicatesp-equal vars)
                         (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->valvar trip)))
                    (equal (svex-override-triplelist-lookup-valvar var x) trip))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar)))))

  (local (defthm lookup-valvar-exists-by-member
           (implies (and (member-equal trip (svex-override-triplelist-fix x))
                         (equal (svar-fix var) (svex-override-triple->valvar trip)))
                    (svex-override-triplelist-lookup-valvar var x))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar)))))


  (defretd lookup-val-when-set-equiv-and-no-duplicate-vars
    (implies (and (no-duplicatesp-equal vars)
                  (set-equiv (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y)))
             (equal (svex-override-triplelist-lookup-valvar var y)
                    (svex-override-triplelist-lookup-valvar var x)))
    :hints (("goal" :use ((:instance member-of-svex-override-triplelist-lookup-valvar
                           (table x) (valvar var))
                          (:instance member-of-svex-override-triplelist-lookup-valvar
                           (table y) (valvar var))
                          (:instance lookup-valvar-exists-by-member
                           (x y) (trip (svex-override-triplelist-lookup-valvar var x))))
             :cases ((svex-override-triplelist-lookup-valvar var y))
             :in-theory (disable member-of-svex-override-triplelist-lookup-valvar
                                 lookup-valvar-exists-by-member))))

  (defthm svex-override-triplelist-lookup-valvar-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triplelist-lookup-valvar var (mergesort x))
                    (svex-override-triplelist-lookup-valvar var x)))
    :hints (("goal" :use ((:instance lookup-val-when-set-equiv-and-no-duplicate-vars
                           (y (mergesort x)))))))

  (local (defthm member-svex-override-triplelist-vars-of-insert
           (iff (member k (svex-override-triplelist-vars (insert trip x)))
                (b* (((svex-override-triple trip)))
                  (or (equal k trip.testvar)
                      (equal k trip.valvar)
                      (member k (svex-override-triplelist-vars (sfix x))))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             insert head empty tail sfix setp)))))

  (local (defthm insert-preserves-no-duplicate-vars
           (implies (b* (((svex-override-triple trip))
                         (rest-vars  (svex-override-triplelist-vars x)))
                      (and (no-duplicatesp-equal rest-vars)
                           (not (equal trip.testvar trip.valvar))
                           (not (member-equal trip.testvar rest-vars))
                           (not (member-equal trip.valvar rest-vars))))
                    (no-duplicatesp-equal (svex-override-triplelist-vars (insert trip x))))
           :hints(("Goal" :in-theory (enable insert
                                             svex-override-triplelist-vars
                                             head empty tail)))))

  (defthm mergesort-preserves-member-vars
    (iff (member k (svex-override-triplelist-vars (mergesort x)))
         (member k (svex-override-triplelist-vars x)))
    :hints(("Goal" :in-theory (enable mergesort
                                      svex-override-triplelist-vars))))

  (defcong set-equiv set-equiv (svex-override-triplelist-vars x) 1
    :hints (("goal" :in-theory (e/d (acl2::set-unequal-witness-rw)
                                    (mergesort-preserves-member-vars))
             :use ((:instance mergesort-preserves-member-vars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-vars x)
                        (svex-override-triplelist-vars x-equiv)))
                    (x x))
                   (:instance mergesort-preserves-member-vars
                    (k (acl2::set-unequal-witness
                        (svex-override-triplelist-vars x)
                        (svex-override-triplelist-vars x-equiv)))
                    (x x-equiv)))
             :do-not-induct t)))

  (defthm mergesort-preserves-no-duplicate-vars
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (no-duplicatesp-equal (svex-override-triplelist-vars (mergesort x))))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                      mergesort)))))








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
                                      svex-override-triplelist-lookup))))

  (defthm svex-override-triple-check-of-mergesort
    (implies (no-duplicatesp-equal (svex-override-triplelist-vars x))
             (equal (svex-override-triple-check test then else (mergesort x))
                    (svex-override-triple-check test then else x)))))


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

  (local (defthm open-nth
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (if (zp n)
                               (car x)
                             (nth (1- n) (cdr x)))))))

  (std::defret-mutual remove-override-test-when-check-overridetriples
    (defret remove-override-test-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
                      (and look
                           (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                  (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                           (4vec-no-1s-p (svex-env-lookup test env)))))
               (equal (svex-eval x (cons (cons test testval)
                                         ;; (cons (cons valvar val)
                                               env))
                      (svex-eval x env)))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
      :fn svex-check-overridetriples)
    (defret remove-override-test-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
                      (and look
                           (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                  (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                           (4vec-no-1s-p (svex-env-lookup test env)))))
               (equal (svex-eval x (cons (cons test testval)
                                         ;; (cons (cons valvar val)
                                               env))
                      (svex-eval x env)))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply 4veclist-nth-safe
                                   svex-override-triple-check))
              (and stable-under-simplificationp
                   '(:in-theory (enable cons-under-iff))))
      :fn svex-check-overridetriples-call)
    (defret remove-override-test-when-<fn>
      (implies (and (not bad)
                    (svar-p test)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples)))
                      (and look
                           (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                  (4vec-bit?! testval (svex-eval look.valexpr env) 0))
                           (4vec-no-1s-p (svex-env-lookup test env)))))
               (equal (svexlist-eval x (cons (cons test testval)
                                             ;; (cons (cons valvar val)
                                             env))
                      (svexlist-eval x env)))
      :hints ('(:expand <call>))
      :fn svexlist-check-overridetriples))

  (std::defret-mutual remove-override-val-when-check-overridetriples
    (defret remove-override-val-when-<fn>
      (implies (and (not bad)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
                      (and look
                           (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
               (equal (svex-eval x (cons (cons valvar val) env))
                      (svex-eval x env)))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
      :fn svex-check-overridetriples)
    (defret remove-override-val-when-<fn>
      (implies (and (not bad)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
                      (and look
                           (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
               (equal (svex-eval x (cons (cons valvar val) env))
                      (svex-eval x env)))
      :hints ('(:expand (<call>
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply 4veclist-nth-safe
                                   svex-override-triple-check)))
      :fn svex-check-overridetriples-call)
    (defret remove-override-val-when-<fn>
      (implies (and (not bad)
                    (svar-p valvar)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
                      (and look
                           (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
               (equal (svexlist-eval x (cons (cons valvar val) env))
                      (svexlist-eval x env)))
      :hints ('(:expand <call>)
              (and stable-under-simplificationp
                   '(:expand ((:free (env) (svex-eval x env))))))
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
      :fn svexlist-check-overridetriples))


  (std::defret-mutual <fn>-of-mergesort
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svex-check-overridetriples)
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:Free (triples) <call>))))
      :fn svex-check-overridetriples-call)
    (defret <fn>-of-mergesort
      (implies (no-duplicatesp-equal (svex-override-triplelist-vars triples))
               (equal (let ((triples (mergesort triples))) <call>)
                      bad))
      :hints ('(:expand ((:free (triples) <call>))))
      :fn svexlist-check-overridetriples))

  (fty::deffixequiv-mutual svex-check-overridetriples))






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


(define svex-env-removekey ((key svar-p) (env svex-env-p))
  :returns (new-env svex-env-p)
  :prepwork ((local (defthm svex-env-p-of-hons-remove-assoc
                      (implies (svex-env-p x)
                               (svex-env-p (acl2::hons-remove-assoc k x)))
                      :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))))
  (acl2::hons-remove-assoc (svar-fix key) (svex-env-fix env))

  ///

  (defret svex-env-boundp-of-<fn>
    (equal (svex-env-boundp k new-env)
           (and (not (equal (svar-fix k) (svar-fix key)))
                (svex-env-boundp k env)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup k new-env)
           (if (equal (svar-fix k) (svar-fix key))
               (4vec-x)
             (svex-env-lookup k env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (in-theory (disable svex-env-removekey)))

  (defthm svex-env-acons-key-val-removekey-under-svex-envs-similar
    (implies (and (svar-p key)
                  (equal (4vec-fix val) (svex-env-lookup key env)))
             (svex-envs-similar (cons (cons key val)
                                      (svex-env-removekey key env))
                                env))
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (defthm svex-env-acons-key-val-removekey-under-svex-envs-similar-fix
    (implies (and (equal (4vec-fix val) (svex-env-lookup key env)))
             (svex-envs-similar (cons (cons (svar-fix key) val)
                                      (svex-env-removekey key env))
                                env))
    :hints(("Goal" :in-theory (enable svex-envs-similar)))))

(defsection svex-env-removekey-check-overridetriples

  (defret svex-env-removekey-test-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svex-eval x (svex-env-removekey test env))
                    (svex-eval x env)))
    :hints (("goal" :use ((:instance remove-override-test-when-<fn>
                           (test (svar-fix test))
                           (env (svex-env-removekey test env))
                           (testval (svex-env-lookup test env))))
             :in-theory (disable remove-override-test-when-<fn>)))
    :fn svex-check-overridetriples)

  (defret svex-env-removekey-val-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
                    (and look
                         (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
             (equal (svex-eval x (svex-env-removekey valvar env))
                    (svex-eval x env)))
    :hints (("goal" :use ((:instance remove-override-val-when-<fn>
                           (valvar (svar-fix valvar))
                           (env (svex-env-removekey valvar env))
                           (val (svex-env-lookup valvar env))))
             :in-theory (disable remove-override-val-when-<fn>)))
    :fn svex-check-overridetriples)


  (local (defthm member-valvar-when-trip-member
           (implies (member-equal trip (svex-override-triplelist-fix x))
                    (member-equal (svex-override-triple->valvar trip)
                                  (svex-override-triplelist-vars x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-fix)))))

  (local (defthm svex-override-triplelist-lookup-valvar-when-member
           (implies (and (member-equal trip (svex-override-triplelist-fix triples))
                         (no-duplicatesp-equal (svex-override-triplelist-vars triples)))
                    (equal (svex-override-triplelist-lookup-valvar
                            (svex-override-triple->valvar trip) triples)
                           trip))
           :hints(("Goal" :in-theory (enable member-equal svex-override-triplelist-vars
                                             svex-override-triplelist-lookup-valvar
                                             svex-override-triplelist-fix)))))

  (local (defthm member-nil-of-svex-override-triplelist-fix
           (not (member nil (svex-override-triplelist-fix x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-fix)))))

  (defret svex-env-removekey-val-when-<fn>-member
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple trip)))
                    (and (member-equal trip (svex-override-triplelist-fix triples))
                         (4vec-no-1s-p (svex-env-lookup trip.testvar env)))))
             (equal (svex-eval x (svex-env-removekey(svex-override-triple->valvar trip) env))
                    (svex-eval x env)))
    :hints (("goal" :use ((:instance remove-override-val-when-<fn>
                           (valvar (svex-override-triple->valvar trip))
                           (env (svex-env-removekey (svex-override-triple->valvar trip) env))
                           (val (svex-env-lookup (svex-override-triple->valvar trip) env))))
             :in-theory (disable remove-override-val-when-<fn>)))
    :fn svex-check-overridetriples)

  (local (defthm svex-env-removekey-swap
           (svex-envs-similar (svex-env-removekey k1 (svex-env-removekey k2 env))
                              (svex-env-removekey k2 (svex-env-removekey k1 env)))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))
           :rule-classes nil))

  (defret svex-env-removekey-val-and-test-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal look.valvar val)
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svex-eval x (svex-env-removekey val (svex-env-removekey test env)))
                    (svex-eval x env)))
    :fn svex-check-overridetriples)

  (defret svex-env-removekey-test-and-val-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal look.valvar val)
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svex-eval x (svex-env-removekey test (svex-env-removekey val env)))
                    (svex-eval x env)))
    :hints (("goal" :use ((:instance svex-env-removekey-swap
                           (k1 test) (k2 val)))))
    :fn svex-check-overridetriples)
  


  (defret svex-env-removekey-car-test-and-val-when-<fn>
    (b* (((svex-override-triple trip) (car triples)))
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (consp triples)
                    (b* ((testval (svex-env-lookup trip.testvar env))
                         (env1 (svex-env-removekey trip.testvar env)))
                      (equal (4vec-bit?! testval (svex-env-lookup trip.valvar env) 0)
                             (4vec-bit?! testval (svex-eval trip.valexpr env1) 0))))
               (equal (svex-eval x (svex-env-removekey trip.testvar (svex-env-removekey trip.valvar env)))
                      (svex-eval x env))))
    :hints (("goal" :use ((:instance svex-env-removekey-test-and-val-when-<fn>
                           (test (svex-override-triple->testvar (car triples)))
                           (val (svex-override-triple->valvar (car triples)))))
             :in-theory (e/d (svex-override-triplelist-lookup)
                             (svex-env-removekey-test-and-val-when-<fn>))))
    :fn svex-check-overridetriples)

  (defret svex-env-removekey-test-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svexlist-eval x (svex-env-removekey test env))
                    (svexlist-eval x env)))
    :hints (("goal" :use ((:instance remove-override-test-when-<fn>
                           (test (svar-fix test))
                           (env (svex-env-removekey test env))
                           (testval (svex-env-lookup test env))))
             :in-theory (disable remove-override-test-when-<fn>)))
    :fn svexlist-check-overridetriples)

  (defret svex-env-removekey-val-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup-valvar valvar triples)))
                    (and look
                         (4vec-no-1s-p (svex-env-lookup look.testvar env)))))
             (equal (svexlist-eval x (svex-env-removekey valvar env))
                    (svexlist-eval x env)))
    :hints (("goal" :use ((:instance remove-override-val-when-<fn>
                           (valvar (svar-fix valvar))
                           (env (svex-env-removekey valvar env))
                           (val (svex-env-lookup valvar env))))))
    :fn svexlist-check-overridetriples)


  (defret svex-env-removekey-val-when-<fn>-member
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple trip)))
                    (and (member-equal trip (svex-override-triplelist-fix triples))
                         (4vec-no-1s-p (svex-env-lookup trip.testvar env)))))
             (equal (svexlist-eval x (svex-env-removekey(svex-override-triple->valvar trip) env))
                    (svexlist-eval x env)))
    :hints (("goal" :use ((:instance remove-override-val-when-<fn>
                           (valvar (svex-override-triple->valvar trip))
                           (env (svex-env-removekey (svex-override-triple->valvar trip) env))
                           (val (svex-env-lookup (svex-override-triple->valvar trip) env))))
             :in-theory (disable remove-override-val-when-<fn>)))
    :fn svexlist-check-overridetriples)

  (defret svex-env-removekey-val-and-test-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal look.valvar val)
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svexlist-eval x (svex-env-removekey val (svex-env-removekey test env)))
                    (svexlist-eval x env)))
    :fn svexlist-check-overridetriples)

  (defret svex-env-removekey-test-and-val-when-<fn>
    (implies (and (not bad)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (b* (((svex-override-triple look) (svex-override-triplelist-lookup test triples))
                       (testval (svex-env-lookup test env))
                       (env1 (svex-env-removekey test env)))
                    (and look
                         (equal look.valvar val)
                         (equal (4vec-bit?! testval (svex-env-lookup look.valvar env) 0)
                                (4vec-bit?! testval (svex-eval look.valexpr env1) 0)))))
             (equal (svexlist-eval x (svex-env-removekey test (svex-env-removekey val env)))
                    (svexlist-eval x env)))
    :hints (("goal" :use ((:instance svex-env-removekey-swap
                           (k1 test) (k2 val)))))
    :fn svexlist-check-overridetriples)

  (defret svex-env-removekey-car-test-and-val-when-<fn>
    (b* (((svex-override-triple trip) (car triples)))
      (implies (and (not bad)
                    (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                    (consp triples)
                    (b* ((testval (svex-env-lookup trip.testvar env))
                         (env1 (svex-env-removekey trip.testvar env)))
                      (equal (4vec-bit?! testval (svex-env-lookup trip.valvar env) 0)
                             (4vec-bit?! testval (svex-eval trip.valexpr env1) 0))))
               (equal (svexlist-eval x (svex-env-removekey trip.testvar (svex-env-removekey trip.valvar env)))
                      (svexlist-eval x env))))
    :hints (("goal" :use ((:instance svex-env-removekey-test-and-val-when-<fn>
                           (test (svex-override-triple->testvar (car triples)))
                           (val (svex-override-triple->valvar (car triples)))))
             :in-theory (e/d (svex-override-triplelist-lookup)
                             (svex-env-removekey-test-and-val-when-<fn>))))
    :fn svexlist-check-overridetriples))


(local (defthm 4vec-bit?!-identity
         (equal (equal (4vec-bit?! test then 0)
                       (4vec-bit?! test else 0))
                (equal (4vec-bit?! test then else)
                       (4vec-fix else)))
         :hints(("Goal" :in-theory (enable 4vec-bit?!))
                (bitops::logbitp-reasoning))))

(define svex-override-triplelist-env-ok ((x svex-override-triplelist-p)
                                         (override-env svex-env-p)
                                         (prev-env svex-env-p))
  (if (atom x)
      t
    (and (b* (((svex-override-triple trip) (car x))
              (testval (svex-env-lookup trip.testvar override-env))
              (valval (svex-env-lookup trip.valvar override-env))
              (exprval (svex-eval trip.valexpr prev-env)))
           (equal (4vec-bit?! testval valval 0)
                  (4vec-bit?! testval exprval 0)))
         (svex-override-triplelist-env-ok (cdr x) override-env prev-env)))
  ///
  (defthm svex-override-triplelist-env-ok-implies-lookup
    (implies (and (svex-override-triplelist-env-ok x override-env prev-env)
                  (svex-override-triplelist-lookup test x))
             (b* (((svex-override-triple trip) (svex-override-triplelist-lookup test x))
                  (testval (svex-env-lookup test override-env))
                  (valval (svex-env-lookup trip.valvar override-env))
                  (exprval (svex-eval trip.valexpr prev-env)))
               (and (equal (4vec-bit?! testval valval 0)
                           (4vec-bit?! testval exprval 0))
                    (equal (4vec-bit?! testval valval exprval)
                           exprval))))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup))))

  (defthm svex-override-triplelist-env-ok-of-remove-test
    (implies (and (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok x env prev-env)
                  (not (svex-override-triplelist-lookup-valvar test x)))
             (svex-override-triplelist-env-ok x (svex-env-removekey test env) prev-env))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup-valvar
                                      svex-override-triplelist-vars))))

  (defcong svex-envs-similar equal (svex-override-triplelist-env-ok x override-env prev-env) 2)
  (defcong svex-envs-similar equal (svex-override-triplelist-env-ok x override-env prev-env) 3))


(defprojection svex-override-triplelist->valexprs ((x svex-override-triplelist-p))
  :returns (valexprs svexlist-p)
  (svex-override-triple->valexpr x))

(defprojection svex-override-triplelist->testvars ((x svex-override-triplelist-p))
  :returns (testvars svarlist-p)
  (svex-override-triple->testvar x)
  ///
  (defthm member-of-svex-override-triplelist->testvars
    (iff (svex-override-triplelist-lookup test x)
         (member-equal (svar-fix test) (svex-override-triplelist->testvars x)))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-lookup)))))





;; (define svex-override-triplelist-env-ok ((x svex-override-triplelist-p)
;;                                          (env svex-env-p))
;;   (if (atom x)
;;       t
;;     (and (b* (((svex-override-triple trip) (car x))
;;               (testval (svex-env-lookup trip.testvar env))
;;               (valval (svex-env-lookup trip.valvar env))
;;               (exprval (svex-eval trip.valexpr env)))
;;            (equal (4vec-bit?! testval valval exprval) exprval))
;;          (svex-override-triplelist-env-ok (cdr x) env))))



(defthmd svex-env-removekeys-in-terms-of-removekey
  (svex-envs-similar (svex-env-removekeys keys env)
                     (if (atom keys)
                         (svex-env-fix env)
                       (svex-env-removekey (car keys)
                                           (svex-env-removekeys (cdr keys) env))))
  :hints(("Goal" :in-theory (enable svex-envs-similar)))
  :rule-classes :definition)

(defcong svex-envs-similar svex-envs-similar (svex-env-removekeys keys env) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defcong svex-envs-similar svex-envs-similar (svex-env-removekey keys env) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))



(defthm-svex-eval-flag
  (defthm svex-eval-of-svex-env-removekey-when-not-member-vars
    (implies (not (member (svar-fix v) (svex-vars x)))
             (equal (svex-eval x (svex-env-removekey v env))
                    (svex-eval x env)))
    :hints ('(:expand ((:free (env) (svex-eval x env)))))
    :flag expr)
  (defthm svexlist-eval-of-svex-env-removekey-when-not-member-vars
    (implies (not (member (svar-fix v) (svexlist-vars x)))
             (equal (svexlist-eval x (svex-env-removekey v env))
                    (svexlist-eval x env)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
    :flag list))

(defthm-svex-eval-flag
  (defthm svex-eval-of-svex-env-removekeys-when-not-intersectp
    (implies (not (intersectp-equal (svarlist-fix vars) (svex-vars x)))
             (equal (svex-eval x (svex-env-removekeys vars env))
                    (svex-eval x env)))
    :hints ('(:expand ((:free (env) (svex-eval x env)))))
    :flag expr)
  (defthm svexlist-eval-of-svex-env-removekeys-when-not-intersectp
    (implies (not (intersectp-equal (svarlist-fix vars) (svexlist-vars x)))
             (equal (svexlist-eval x (svex-env-removekeys vars env))
                    (svexlist-eval x env)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
    :flag list))

;; (define svex-override-triplelist-ordering-ok ((tests svarlist-p)
;;                                               (x svex-override-triplelist-p)
;;                                               (env svex-env-p))
;;   :guard (subsetp-equal tests (svex-override-triplelist->testvars x))
;;   (if (atom tests)
;;       t
;;     (and (b* (((svex-override-triple trip) (svex-override-triplelist-lookup (car tests) x))
;;               (testval (svex-env-lookup trip.testvar env))
;;               (valval (svex-env-lookup trip.valvar env))
;;               (exprval (svex-eval trip.valexpr (svex-env-removekeys tests env))))
;;            (equal (4vec-bit?! testval valval 0)
;;                   (4vec-bit?! testval exprval 0)))
;;          (svex-override-triplelist-ordering-ok (cdr tests) x (svex-env-removekey (car tests) env)))))


(defsection svex-eval-of-remove-overridetriple-tests
  (local (defun ind (tests svex x env)
           (if (atom tests)
               (list svex x env)
             (b* ((test (car tests))
                  ((svex-override-triple trip) (svex-override-triplelist-lookup test x))
                  (new-env (svex-env-removekey test env)))
               (list (ind (cdr tests) svex x new-env)
                     (ind (cdr tests) trip.valexpr x new-env))))))

  (local (defthm svex-check-overridetriples-of-member
           (implies (And (not (svexlist-check-overridetriples
                               exprs x))
                         (member-equal (svex-fix svex) (svexlist-fix exprs)))
                    (not (svex-check-overridetriples svex x)))
           :hints(("Goal" :in-theory (enable svexlist-check-overridetriples)
                   :expand ((svexlist-fix exprs))
                   :induct (len exprs)))))

  (local (defthm member-valexpr-of-lookup
           (implies (svex-override-triplelist-lookup test x)
                    (member-equal (svex-override-triple->valexpr
                                   (svex-override-triplelist-lookup test x))
                                  (svex-override-triplelist->valexprs x)))
           :hints(("Goal" :in-theory (enable svex-override-triplelist->valexprs
                                             svex-override-triplelist-lookup)))))

  (local (defthm svex-check-overridetriples-of-valexpr-lookup
           (implies (and (not (svexlist-check-overridetriples
                               (svex-override-triplelist->valexprs x) x))
                         (svex-override-triplelist-lookup test x))
                    (not (svex-check-overridetriples
                          (svex-override-triple->valexpr
                                   (svex-override-triplelist-lookup test x))
                          x)))))

  (local (defthm svex-env-removekeys-of-removekey
           (svex-envs-similar (svex-env-removekeys keys (svex-env-removekey key env))
                              (svex-env-removekey key (svex-env-removekeys keys env)))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))


  

  (defthm svex-eval-of-remove-overridetriple-tests
    (implies (and (not (svexlist-check-overridetriples
                        (svex-override-triplelist->valexprs x) x))
                  ;; (svex-override-triplelist-env-ok
                  ;;  x env (svex-env-removekeys tests env))
                  (subsetp-equal tests (svex-override-triplelist->testvars x))
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok
                   x env (svex-env-removekeys tests env))
                  (not (svex-check-overridetriples svex x)))
             (equal (svex-eval svex (svex-env-removekeys tests env))
                    (svex-eval svex env)))
    :hints (("goal" :induct (ind tests svex x env)
             :in-theory (enable svex-env-removekeys-in-terms-of-removekey
                                subsetp-equal))))

  (defthm svexlist-eval-of-remove-overridetriple-tests
    (implies (and (not (svexlist-check-overridetriples
                        (svex-override-triplelist->valexprs x) x))
                  ;; (svex-override-triplelist-env-ok
                  ;;  x env (svex-env-removekeys tests env))
                  (subsetp-equal tests (svex-override-triplelist->testvars x))
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok
                   x env (svex-env-removekeys tests env))
                  (not (svexlist-check-overridetriples svexes x)))
             (equal (svexlist-eval svexes (svex-env-removekeys tests env))
                    (svexlist-eval svexes env)))
    :hints (("goal" :induct (len svexes)
             :expand ((svexlist-check-overridetriples svexes x)
                      (:free (env) (svexlist-eval svexes env)))))))

(define svex-override-triplelist-lookup->valvar ((test svar-p)
                                                 (x svex-override-triplelist-p))
  :guard (svex-override-triplelist-lookup test x)
  :returns (valvar svar-p)
  (svex-override-triple->valvar (svex-override-triplelist-lookup test x)))

(defprojection svex-override-triplelist-tests->valvars ((x svarlist-p)
                                                        (triples svex-override-triplelist-p))
  :guard (subsetp-equal x (svex-override-triplelist->testvars triples))
  :returns (valvars svarlist-p)
  (svex-override-triplelist-lookup->valvar x triples))


(define svex-override-triplelist-valvars-of-empty-tests ((valvars svarlist-p)
                                                         (x svex-override-triplelist-p)
                                                         (env svex-env-p))
  (if (atom valvars)
      t
    (and (b* ((trip (svex-override-triplelist-lookup-valvar (car valvars) x)))
           (and trip
                (4vec-no-1s-p
                 (svex-env-lookup
                  (svex-override-triple->testvar
                   trip)
                  env))))
         (svex-override-triplelist-valvars-of-empty-tests (cdr valvars) x env)))
  ///
  (local (defthm 4vec-no-1s-p-of-if
           (implies (and (4vec-no-1s-p then)
                         (4vec-no-1s-p else))
                    (4vec-no-1s-p (if test then else)))))

  (defthm svex-override-triplelist-valvars-of-empty-tests-remove-valvars
    (implies (and (not (svex-check-overridetriples svex x))
                  (svex-override-triplelist-valvars-of-empty-tests valvars x env)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svarlist-p valvars))
             (equal (svex-eval svex (svex-env-removekeys valvars env))
                    (svex-eval svex env)))
    :hints(("Goal" :in-theory (enable svex-env-removekeys-in-terms-of-removekey))))

  (defthm svex-override-triplelist-valvars-of-empty-tests-remove-valvars-svexlist
    (implies (and (not (svexlist-check-overridetriples svexes x))
                  (svex-override-triplelist-valvars-of-empty-tests valvars x env)
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svarlist-p valvars))
             (equal (svexlist-eval svexes (svex-env-removekeys valvars env))
                    (svexlist-eval svexes env)))
    :hints(("Goal" :induct (len svexes)
            :expand ((:free (env) (svexlist-eval svexes env))
                     (svexlist-check-overridetriples svexes x)))))

  (defthm svex-override-triplelist-valvars-of-empty-tests-of-valvars-of-removed-tests
    (implies (and (subsetp-equal tests (svex-override-triplelist->testvars x))
                  (no-duplicatesp-equal (svex-override-triplelist-vars x)))
             (svex-override-triplelist-valvars-of-empty-tests
              (svex-override-triplelist-tests->valvars tests x)
              x (svex-env-removekeys tests env)))
    :hints (("goal" :induct (len tests)
             :in-theory (enable subsetp-equal
                                svex-override-triplelist-lookup->valvar))))


  (local (defthm svex-env-removekeys-of-append
           (svex-envs-similar (svex-env-removekeys (append x y) env)
                              (svex-env-removekeys x (svex-env-removekeys y env)))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))


  ;; (defthm svex-override-triplelist-env-ok-remove-valvars
  ;;   (implies (and (not (svexlist-check-overridetriples
  ;;                       (svex-override-triplelist->valexprs x) x))
  ;;                 ;; (svex-override-triplelist-env-ok
  ;;                 ;;  x env (svex-env-removekeys tests env))
  ;;                 (no-duplicatesp-equal (svex-override-triplelist-vars x))
  ;;                 (svex-override-triplelist-valvars-of-empty-tests
  ;;                  valvars x prev-env)
  ;;                 (subsetp-equal y (svex-override-triplelist-fix x))
  ;;            (iff (svex-override-triplelist-env-ok y env (svex-env-removekeys valvars prev-env))
  ;;                 (svex-override-triplelist-env-ok y env prev-env)))
  ;;   :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
  ;;                                     subsetp-equal))))

  (defthm svex-eval-of-remove-overridetriple-tests-and-vals
    (implies (and (not (svexlist-check-overridetriples
                        (svex-override-triplelist->valexprs x) x))
                  ;; (svex-override-triplelist-env-ok
                  ;;  x env (svex-env-removekeys tests env))
                  (subsetp-equal tests (svex-override-triplelist->testvars x))
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok
                   x env (svex-env-removekeys tests env))
                  (not (svex-check-overridetriples svex x)))
             (equal (svex-eval svex (svex-env-removekeys
                                     (append (svex-override-triplelist-tests->valvars tests x)
                                             tests)
                                     env))
                    (svex-eval svex env))))

  (defthm svexlist-eval-of-remove-overridetriple-tests-and-vals
    (implies (and (not (svexlist-check-overridetriples
                        (svex-override-triplelist->valexprs x) x))
                  ;; (svex-override-triplelist-env-ok
                  ;;  x env (svex-env-removekeys tests env))
                  (subsetp-equal tests (svex-override-triplelist->testvars x))
                  (no-duplicatesp-equal (svex-override-triplelist-vars x))
                  (svex-override-triplelist-env-ok
                   x env (svex-env-removekeys tests env))
                  (not (svexlist-check-overridetriples svexes x)))
             (equal (svexlist-eval svexes (svex-env-removekeys
                                           (append (svex-override-triplelist-tests->valvars tests x)
                                                   tests)
                                           env))
                    (svexlist-eval svexes env)))))
